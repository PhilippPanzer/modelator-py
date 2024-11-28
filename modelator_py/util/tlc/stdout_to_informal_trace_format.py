import typing
import re
from typing import Iterator

from modelator_py.util.informal_trace_format import ITFTrace

from .state_to_informal_trace_format import state_to_informal_trace_format_state


def _trace_lines_model_checking_mode(line_iter: typing.Iterator[str]) -> typing.Iterator[typing.List[str]]:

    def is_header(line):
        """One line before the beginning of the trace."""
        single_state_trace_header = "is violated by the initial state" in line
        mult_state_trace_header = line == "Error: The behavior up to this point is:"
        prop_violation_trace_header = line == "Error: The following behavior constitutes a counter-example:"
        return single_state_trace_header or mult_state_trace_header or prop_violation_trace_header

    def is_start_of_new_trace(line):
        """When there are multiple traces, closes the previous trace"""

        # when there are multiple violations, a new trace report starts with:
        continue_case = (
                line.startswith("Error: Invariant")
                or line.startswith("Error: Action property")
                or line.startswith("Error: Temporal properties were violated.")
        )

        # when the first violation was in the init state, the second one starts with:
        init_state_continue_case = line.startswith("Finished computing initial states")
        return continue_case or init_state_continue_case

    def is_footer(line):
        multi_state_footer = (
            ("states generated" in line)
            and ("distinct states found" in line)
            and ("states left on queue" in line)
            and (not line.startswith("Progress"))
        ) or ("Model checking completed" in line)

        single_state_footer = "Finished in" in line

        return single_state_footer or multi_state_footer

    header_open = False
    header_cnt = 0
    header_ix = -1
    trace = []

    for i, line in enumerate(line_iter):
        line = line.strip("\n")
        if (header_ix >= 0
                and not is_start_of_new_trace(line)
                and not (is_header(line) or is_footer(line))
                and line):
            trace.append(line)

        if is_start_of_new_trace(line):
            header_open = True
            if 0 < header_cnt:
                yield trace
                trace = []

        if is_header(line):
            header_cnt += 1
            header_ix = i

        # we need boolean header_open because the footer the conditions for the footer
        # of a single state trace will be met also in the line after the footer of a multi-state trace
        if header_open and is_footer(line):
            header_open = False
            if 0 < header_cnt:
                yield trace
            break

def trace_lines_model_checking_mode_from_file(f) -> typing.Iterator[typing.List[str]]:
    """
    Returns list of lists. Each sublist is a list of lines
    that make a trace.

    Args:
        stdout : stdout of TLC execution run in model checking mode
    """
    return _trace_lines_model_checking_mode(f)

def trace_lines_model_checking_mode(stdout) -> typing.List[typing.List[str]]:
    """
    Returns list of lists. Each sublist is a list of lines
    that make a trace.

    Args:
        stdout : stdout of TLC execution run in model checking mode
    """
    return list(_trace_lines_model_checking_mode(stdout.split("\n")))


def trace_lines_simulation_mode(stdout) -> typing.List[typing.List[str]]:
    """
    Returns list of lists. Each sublist is a list of lines
    that make a trace.

    Args:
        stdout : stdout of TLC execution run in simulation mode
    """
    ret = []
    lines = stdout.split("\n")

    def is_header(line):
        """Begins a trace and may also end a previous trace"""
        HEADER = "State 1:"
        return line.startswith(HEADER)

    def is_footer(line):
        """Ends the list of traces"""
        return line.startswith("Finished in")

    header_cnt = 0
    header_ix = -1
    for i, line in enumerate(lines):
        if is_header(line):
            if 0 < header_cnt:
                trace = lines[header_ix : i - 4]
                ret.append(trace)
            header_cnt += 1
            header_ix = i
        if is_footer(line) and 0 < header_cnt:
            ret.append(lines[header_ix : i - 4])

    return ret


def split_into_states(lines: typing.List[str]) -> typing.Tuple[typing.List[typing.List[str]], typing.Optional[typing.Tuple[int, int]]]:
    """
    Converts a TLA+/ASCII trace string expression into a list of TLA+ state
    string expressions. Requires removing non-TLA+ ascii from the trace string
    expression.

    A trace from TLC is a sequence of [header, content] pairs.
    The headers are not valid TLA+.
    This function returns a list where each item is valid TLA+ content.
    """
    ret = []
    HEADER = "State "
    LOOP_MARKER = "Back to state "
    header_cnt = 0
    header_ix = -1

    loop_marker_idx = None
    loop_start_state = -1
    loop_end_state = -1

    # this is for the case when the invariant is violated in the initial state
    # then, the counterexample is not prefixed with "State "
    if len(lines) > 0 and not lines[0].startswith(HEADER):
        lines = [HEADER] + lines
    for i, line in enumerate(lines):
        if line.startswith(HEADER):
            if 0 < header_cnt:
                ret.append(lines[header_ix + 1 : i])
            header_ix = i
            header_cnt += 1
        elif line.startswith(LOOP_MARKER):
            m = re.match(r"Back to state (?P<loop_start>\d+):", line)
            assert m, f"Unexpected line: '{line}'"
            loop_marker_idx = i
            loop_start_state = int(m.groupdict()["loop_start"])
            loop_end_state = header_cnt

    if 0 < header_cnt:
        if loop_marker_idx is None:
            ret.append(lines[header_ix + 1 :])
        else:
            ret.append(lines[header_ix + 1 : loop_marker_idx])

    if loop_marker_idx is None:
        return ret, None
    else:
        return ret, (loop_start_state, loop_end_state)

def extract_traces_from_file(f: Iterator[str]) -> Iterator[list]:
    """
    Extract zero, one or more traces from the input string iterator.

    This generator yields 2-tuples, where the first entry is a trace
    and the second entry contains loop information in the case of lassos, or None if it's a normal trace.
    A trace is a list of substrings from the input and each substring is a state.
    """
    for trace in trace_lines_model_checking_mode_from_file(f):
        trace_with_loop_info = split_into_states(trace)
        trace_split = trace_with_loop_info[0]
        loop_info = trace_with_loop_info[1]
        trace_state_strings = ["\n".join(lines) for lines in trace_split]
        yield trace_state_strings, loop_info

def extract_traces(stdout: str):
    """
    Extract zero, one or more traces from the stdout of TLC.

    This function returns a 2-tuple, where the first entry is the list of traces
    and the second entry contains loop information in the case of lassos.
    The list of traces is a list of sublists of substrings from the input.
    Each sublist of substrings is a trace and each substring is a state.
    """
    if "Running Random Simulation" in stdout:
        traces = trace_lines_simulation_mode(stdout)
    else:
        traces = trace_lines_model_checking_mode(stdout)
    traces_with_loop_info = [split_into_states(t) for t in traces]

    # get list of traces, each trace is a list of states, each state a list of lines
    traces_split = [t[0] for t in traces_with_loop_info]
    loop_infos = [t[1] for t in traces_with_loop_info]

    # get list of traces, where each trace is a list of states, a state is a string of the TLA+ formula
    traces_state_strings = [["\n".join(lines) for lines in t] for t in traces_split]
    return traces_state_strings, loop_infos

def tlc_trace_to_informal_trace_format_trace(trace: typing.List[str]):
    """
    Convert a tla trace from TLC stdout to the Informal Trace Format
    https://apalache.informal.systems/docs/adr/015adr-trace.html?highlight=trace%20format#adr-015-informal-trace-format-in-json

    Trace input is a list of states. Each state is a string.
    """

    states = [state_to_informal_trace_format_state(state) for state in trace]
    vars = []
    if 0 < len(states):
        vars = list(states[0].var_value_map.keys())

    return ITFTrace(vars, states)
