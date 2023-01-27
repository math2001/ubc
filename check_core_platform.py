from __future__ import annotations
import syntax
import source
import assume_prove
import dsa
import smt


def verify(unsafe_func: syntax.Function) -> smt.VerificationResult:
    prog_func = source.convert_function(unsafe_func)
    dsa_func, dsa_contexts = dsa.dsa(prog_func)
    prog = assume_prove.make_prog(dsa_func, dsa_contexts)
    smtlib = smt.make_smtlib(prog)
    sats = tuple(smt.send_smtlib_to_z3(smtlib))
    return smt.parse_sats(sats)


if __name__ == "__main__":
    with open('tests/monitor_CFunctions.txt') as f:
        structs, functions, const_globals = syntax.parse_and_install_all(
            f, None)
        for func in functions.values():
            if func.entry is None:
                continue

            if func.name.startswith('monitor.seL4_'):
                continue
            try:
                result = verify(func)
            except Exception as e:
                print(f'{func.name} crashed: {e}')
                continue

            if result is not smt.VerificationResult.OK:
                print(f'{func.name} failed: {result}')
            else:
                print(f'{func.name} verified')
