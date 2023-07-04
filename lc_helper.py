from argparse import FileType
from typing import NamedTuple


def pretty_bit_set(num: int) -> str:
    bit_set = []
    bits = bin(num)[2:]
    for i, b in enumerate(bits):
        if b == '1':
            bit_set.append(str(len(bits) - 1 - i))
    return f'bitset {bin(num)} {{{", ".join(bit_set)}}}'
    return f'bitset {{{", ".join(bit_set)}}}'


def extract_bits(n: int, hi: int, lo: int) -> int:
    """ extract hi - lo + 1 bits (hi and lo included, like SMTLIB)
    """
    return (n >> lo) & ((1 << (hi - lo + 1)) - 1)


def pretty_receive_oracle(num: int) -> str:
    size = 72
    constructor = extract_bits(num, size - 1, size - 2)
    assert 0 <= constructor and constructor <= 3
    constructor_name = ["notification", "ppcall", "unknown"][constructor]
    if constructor_name == "notification":
        return f'notification {pretty_bit_set(extract_bits(num, size - 3, size-3-63))}'
    return constructor_name + "{<todo>}"


class ExternType(NamedTuple):
    name: str
    bit_size: int


lc_type = {
    'lc_running_pd': ExternType(name='PD', bit_size=6),
    'lc_receive_oracle': ExternType(name='NextRecv', bit_size=72),
    'lc_unhandled_notified': ExternType(name='Ch_set', bit_size=64),
    'lc_last_handled_notified': ExternType(name='Ch_set', bit_size=64),
    'lc_unhandled_ppcall': ExternType(name='Maybe_Prod_Ch_MsgInfo', bit_size=71),
    'lc_unhandled_reply': ExternType(name='Maybe_MsgInfo', bit_size=65),
    'lc_last_handled_reply': ExternType(name='Maybe_MsgInfo', bit_size=65)
}


def print_local_context(num: int) -> None:
    top = sum(t.bit_size for t in lc_type.values()) - 1

    for name, field_typ in lc_type.items():
        val = extract_bits(num, top, top - field_typ.bit_size + 1)
        if field_typ.name.endswith("_set"):
            print(name, pretty_bit_set(val))
        elif name == 'lc_receive_oracle':
            print(name, pretty_receive_oracle(val))
        else:
            print(name, val)
        top -= field_typ.bit_size
