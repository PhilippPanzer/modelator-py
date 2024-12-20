import os

from modelator_py.util.informal_trace_format import with_lists, with_records
from modelator_py.util.tlc.itf import TlcITFCmd, tlc_itf
from modelator_py.util.tlc.stdout_to_informal_trace_format import (
    extract_traces,
    tlc_trace_to_informal_trace_format_trace, extract_traces_from_file,
)

from ...helper import get_resource_dir


def test_extract_no_trace_from_tlc():
    fn = "TlcTraceAbsenceParse.txt"
    fn = os.path.join(get_resource_dir(), fn)
    content = None
    with open(fn, "r") as fd:
        content = fd.read()

    tlc_traces, loop_infos = extract_traces(content)
    assert len(tlc_traces) == 0

def test_extract_no_trace_from_tlc_file():
    fn = "TlcTraceAbsenceParse.txt"
    fn = os.path.join(get_resource_dir(), fn)
    with open(fn, "r") as fd:
        ret = list(extract_traces_from_file(fd))
    assert len(ret) == 0

def _extract_trace_from_tlc(fn):
    fn = os.path.join(get_resource_dir(), fn)
    with open(fn, "r") as fd:
        content = fd.read()

    return extract_traces(content)

def _extract_trace_from_tlc_file(fn):
    fn = os.path.join(get_resource_dir(), fn)
    with open(fn, "r") as fd:
        return list(extract_traces_from_file(fd))


def test_extract_trace_from_tlc():
    fn = "TlcTraceParse.txt"
    tlc_traces, loop_infos = _extract_trace_from_tlc(fn)
    assert len(tlc_traces) == 1

def test_extract_trace_from_tlc_file():
    fn = "TlcTraceParse.txt"
    tlc_traces_and_loop_infos = _extract_trace_from_tlc_file(fn)
    assert len(tlc_traces_and_loop_infos ) == 1
    assert tlc_traces_and_loop_infos[0][1] is None


def test_extract_trace_initState_from_tlc():
    fn = "TlcTraceParseInitState.txt"
    tlc_traces, loop_infos = _extract_trace_from_tlc(fn)
    assert len(tlc_traces) == 1

def test_extract_trace_initState_from_tlc_file():
    fn = "TlcTraceParseInitState.txt"
    tlc_traces = _extract_trace_from_tlc_file(fn)
    assert len(tlc_traces) == 1

def test_extract_trace_initStateContinue_from_tlc():
    fn = "TlcTraceParseInitStateContinue.txt"
    tlc_traces, loop_infos = _extract_trace_from_tlc(fn)
    assert len(tlc_traces) == 3

def test_extract_trace_initStateContinue_from_tlc_file():
    fn = "TlcTraceParseInitStateContinue.txt"
    tlc_traces = _extract_trace_from_tlc_file(fn)
    assert len(tlc_traces) == 3

def test_extract_trace_from_tlc_simulation_mode():
    fn = "TlcTraceParseSimulationMode.txt"
    fn = os.path.join(get_resource_dir(), fn)
    content = None
    with open(fn, "r") as fd:
        content = fd.read()

    tlc_traces = extract_traces(content)[0]
    assert len(tlc_traces) == 1


def test_extract_multiple_traces_from_tlc_simulation_mode():
    fn = "TlcMultipleTraceParseSimulationMode.txt"
    fn = os.path.join(get_resource_dir(), fn)
    content = None
    with open(fn, "r") as fd:
        content = fd.read()

    tlc_traces = extract_traces(content)[0]
    assert len(tlc_traces) == 51


def test_extract_multiple_traces_from_tlc():

    fn = "TlcMultipleTraceParse.txt"
    fn = os.path.join(get_resource_dir(), fn)
    content = None
    with open(fn, "r") as fd:
        content = fd.read()

    traces = extract_traces(content)[0]

    assert len(traces) == 4


def test_extract_multiple_traces_from_tlc_cutoff():

    # Some number of lines from stdout have been removed.
    fns = [
        "TlcMultipleTraceParseCutoff0.txt",
        "TlcMultipleTraceParseCutoff1.txt",
    ]

    contents = []

    for fn in fns:
        path = os.path.join(get_resource_dir(), fn)
        with open(path, "r") as fd:
            content = fd.read()
            contents.append(content)

    traces = [extract_traces(content)[0] for content in contents]
    assert all(len(r) == 3 for r in traces)


def test_extract_informal_trace_format_trace_from_tlc_stress_example():
    fn = "TlcTraceParse.txt"
    fn = os.path.join(get_resource_dir(), fn)
    content = None
    with open(fn, "r") as fd:
        content = fd.read()

    tlc_traces = extract_traces(content)[0]
    assert len(tlc_traces) == 1
    tlc_trace = tlc_traces[0]
    tlc_trace_to_informal_trace_format_trace(tlc_trace)


def test_TlcLassoTraceParse():
    fn = "TlcLassoTraceParse.txt"
    fn = os.path.join(get_resource_dir(), fn)
    content = None
    with open(fn, "r") as fd:
        content = fd.read()

    tlc_traces = extract_traces(content)[0]
    assert len(tlc_traces) == 1
    tlc_trace = tlc_traces[0]
    itf_trace = tlc_trace_to_informal_trace_format_trace(tlc_trace)
    itf_trace = with_lists(itf_trace)

def test_extract_informal_trace_format_trace_from_tlc_stress_example_include_lists():
    fn = "TlcTraceParse.txt"
    fn = os.path.join(get_resource_dir(), fn)
    content = None
    with open(fn, "r") as fd:
        content = fd.read()

    tlc_traces = extract_traces(content)[0]
    assert len(tlc_traces) == 1
    tlc_trace = tlc_traces[0]
    itf_trace = tlc_trace_to_informal_trace_format_trace(tlc_trace)
    itf_trace = with_lists(itf_trace)


def test_extract_informal_trace_format_trace_from_tlc_stress_example_include_records():
    fn = "TlcTraceParse.txt"
    fn = os.path.join(get_resource_dir(), fn)
    content = None
    with open(fn, "r") as fd:
        content = fd.read()

    tlc_traces = extract_traces(content)[0]
    assert len(tlc_traces) == 1
    tlc_trace = tlc_traces[0]
    itf_trace = tlc_trace_to_informal_trace_format_trace(tlc_trace)
    itf_trace = with_records(itf_trace)


def test_extract_informal_trace_format_trace_from_tlc_stress_example_include_lists_and_records():
    fn = "TlcTraceParse.txt"
    fn = os.path.join(get_resource_dir(), fn)
    content = None
    with open(fn, "r") as fd:
        content = fd.read()

    tlc_traces = extract_traces(content)[0]
    assert len(tlc_traces) == 1
    tlc_trace = tlc_traces[0]
    itf_trace = tlc_trace_to_informal_trace_format_trace(tlc_trace)
    itf_trace = with_records(itf_trace)
    itf_trace = with_lists(itf_trace)


def test_extract_informal_trace_format_traces_from_tlc_simple_example():

    fn = "TlcMultipleTraceParse.txt"
    fn = os.path.join(get_resource_dir(), fn)
    content = None
    with open(fn, "r") as fd:
        content = fd.read()

    tlc_traces = extract_traces(content)[0]
    itf_traces = [
        tlc_trace_to_informal_trace_format_trace(trace) for trace in tlc_traces
    ]
    assert not any(e is None for e in itf_traces)


def test_extract_informal_trace_format_traces_from_tlc_real_world_example():

    fn = "TlcMultipleTraceParse_RealWorld0.txt"
    fn = os.path.join(get_resource_dir(), fn)
    content = None
    with open(fn, "r") as fd:
        content = fd.read()

    cmd = TlcITFCmd()
    cmd.stdout = content
    cmd.lists = True
    cmd.records = True
    tlc_itf(cmd=cmd)
