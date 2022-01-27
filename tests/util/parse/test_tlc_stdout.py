import os

from modelator.util.parse.tlc_stdout import extract_traces

from ...helper import get_resource_dir


def test_extract_traces():

    fn = "TlcMultipleTraceParse.txt"
    fn = os.path.join(get_resource_dir(), fn)
    content = None
    with open(fn, "r") as fd:
        content = fd.read()

    result = extract_traces(content)
    assert len(result) == 4