import pytest
import json
from typing import Mapping, Sequence, TypedDict
import os
import dsa
import syntax
import source 
import ghost_data
import ghost_code
import assume_prove
import nip

class ExpectedFailure(TypedDict):
    reason: str 
    assert_node: int 
    use_node: int

class ExpectedFailures(TypedDict):
    test: Mapping[str, ExpectedFailure]
    helper: Sequence[str]

def generate_param_test_from_json() -> ExpectedFailures:
    filename = "tests/errors/errors.json"
    assert os.path.isfile(filename)
    f = open(filename)
    funcs: ExpectedFailures = json.load(f)
    f.close()
    return funcs

def get_func_from_txt() -> Mapping[str, dsa.Function]:
    filename = "tests/errors/errors.txt"
    assert os.path.isfile(filename)
    with open(filename) as f:
        stuff = syntax.parse_and_install_all(f, None)
    _, functions, _ = stuff

    def map_to_dsa_func(sfunc: syntax.Function) -> dsa.Function:
        prog_func = source.convert_function(sfunc).with_ghost(
                ghost_data.get(filename, sfunc.name))
        nip_func = nip.nip(prog_func)
        ghost_func = ghost_code.sprinkle_ghost_code(filename, nip_func, functions)
        dsa_func = dsa.dsa(ghost_func)
        return dsa_func

    dsa_functions: Mapping[str, dsa.Function] = {k: map_to_dsa_func(v) for k,v in functions.items()} 
    return dsa_functions


dsa_functions = get_func_from_txt()
expected_results = generate_param_test_from_json()
print(expected_results)
@pytest.mark.parametrize("fname", dsa_functions.keys())
def test_function(fname: str):
    func = dsa_functions



    
     
