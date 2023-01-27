""" An expression parser used to parse pre/post condition and loop invariants
"""

from __future__ import annotations
from os import pread
from typing import NamedTuple, Callable, Tuple
from enum import unique, Enum
from typing_extensions import assert_never
from source import Expr, ExprFunction, ExprOp, ExprNum, ExprType, ExprVar, ExprSymbol, Operator as SourceOperator, type_word32

class TokenOpen(NamedTuple):
    pass

class TokenClose(NamedTuple):
    pass

class TokenColon(NamedTuple):
    pass

class TokenLiteralNum(NamedTuple):
    num: int

class TokenIdentifier(NamedTuple):
    identifier: str

class OpDescription(NamedTuple):
    symbol: str
    bp: int
    """ binding power (precedence) """


@unique
class BinaryOperator(Enum):
    """
    Based on C's precedence: http://www.eecs.northwestern.edu/~wkliao/op-prec.htm
    (identical to cpp https://en.cppreference.com/w/c/language/operator_precedence)

    >>> Precedence: operators                        associates
        150: () [] . ->                              left
        140: ++ -- + - ! ~ (type) * & sizeof         right
        130: * / %                                   left
        120: + -                                     left
        110: << >>                                   left
        100: < <= > >=                               left
        90:  == !=                                   left
        80:  &                                       left
        70:  ^                                       left
        60:  |                                       left
        50:  &&                                      left
        40:  ||                                      left
        30:  ?:                                      right
        20:  = += -= *= /= %= &= ^= |= <<= >>=       right
        10:  ,                                       left

    The name of the enum's field (PLUS, MINUS, etc) correspond to source.Operator
    """

    PLUS = OpDescription('+', 120)
    MINUS = OpDescription('-', 120)
    TIMES = OpDescription('*', 130)
    MODULUS = OpDescription('%', 130)
    DIVIDED_BY = OpDescription('/', 130)

    BW_AND = OpDescription('&', 80)
    BW_XOR = OpDescription('^', 70)
    BW_OR = OpDescription('|', 60)

    AND = OpDescription('&&', 50)
    OR = OpDescription('||', 40)
    EQUALS = OpDescription('==', 20)
    IMPLIES = OpDescription('==>', 15)

    LESS = OpDescription('<u', 100)  # unsigned less than
    LESS_EQUALS = OpDescription('<=u', 100)
    GREATER = OpDescription('>u', 100)
    GREATER_THAN = OpDescription('>=u', 100)

    SIGNED_LESS = OpDescription('<s', 100) # signed less than
    SIGNED_LESS_EQUALS = OpDescription('<=s', 100)
    SIGNED_GREATER = OpDescription('>s', 100)
    SIGNED_GREATER_THAN = OpDescription('>=s', 100)

def to_source_operator(op: UnaryOperator | BinaryOperator) -> SourceOperator:
    return

@unique
class UnaryOperator(Enum):
    """ See BinaryOperator's doc """
    BW_NOT = OpDescription('~', 140)
    NOT = OpDescription('!', 140)


class TokenOp(NamedTuple):
    op: UnaryOperator | BinaryOperator

class TokenEOF:
    pass

Token = TokenOpen | TokenClose | TokenIdentifier | TokenLiteralNum | TokenOp | TokenColon | TokenEOF

# python's str methods aren't super clear. We only support ascii expression
def is_letter(s: str) -> bool:
    assert len(s) == 1
    c = ord(s)
    return (ord('a') <= c and c <= ord('z')) or (ord('A') <= c and c <= ord('Z'))

def is_digit(s: str) -> bool:
    assert len(s) == 1
    c = ord(s)
    return ord('0') <= c and c <= ord('9')

def accept(expr: str, prefix: str) -> str | None:
    if not expr.startswith(prefix):
        return None
    return expr[len(prefix):]

def accept_literal_num(s: str) -> tuple[TokenLiteralNum, str] | None:
    # TODO: support hex literals
    # TODO: support binary literals

    if not (is_digit(s[0]) or (s[0] == '-' and is_digit(s[1]))):
        return None

    i = 1
    # underscores are legal in number literals for things like 1_000
    while i < len(s) and (is_digit(s[i]) or s[i] == '_'):
        i += 1

    return TokenLiteralNum(int(s[:i])), s[i:]


sorted_unary_operators = tuple(sorted(UnaryOperator, key=lambda op: -len(op.value.symbol)))
sorted_binary_operators = tuple(sorted(BinaryOperator, key=lambda op: -len(op.value.symbol)))

operators_sorted_by_length_dec = tuple(sorted(list(BinaryOperator) + list(UnaryOperator), key=lambda op: -len(op.value.symbol)))
def accept_operator(s: str) -> tuple[TokenOp, str] | None:
    # we want to try to accept the longest operators first, in case an operator
    # is a prefix of an other (for example == and ==>)
    for op in operators_sorted_by_length_dec:
        if s.startswith(op.value.symbol):
            return TokenOp(op), s[len(op.value.symbol):]
    return None


def accept_identifier(s: str) -> tuple[TokenIdentifier, str] | None:
    if not is_letter(s[0]) and s[0] != '_':
        return None

    i = 1
    while i < len(s) and (is_letter(s[i]) or is_digit(s[i]) or s[i] == '_'):
        i += 1
    return TokenIdentifier(s[:i]), s[i:]

def consume_space(s: str) -> str:
    i = 0
    while i < len(s) and s[i].isspace():
        i += 1
    return s[i:]

def get_next_token(s: str) -> tuple[Token, str]:
    s = consume_space(s)

    if len(s) == 0:
        return TokenEOF(), ""

    if ss := accept(s, '('):
        return TokenOpen(), ss

    if ss := accept(s, ')'):
        return TokenClose(), ss

    if ss := accept(s, ':'):
        return TokenColon(), ss

    # python scoping is annoying
    if res := accept_literal_num(s):
        return res

    if res1 := accept_operator(s):
        return res1

    if res2 := accept_identifier(s):
        return res2

    raise ValueError(f"don't know how to parse the next token of {s!r}")

def get_all_tokens(s: str) -> tuple[Token, ...]:
    tokens: list[Token] = []
    while True:
        tok, s = get_next_token(s)
        if isinstance(tok, TokenEOF):
            return tuple(tokens)
        tokens.append(tok)

TokenPredicate = Callable[[Token], bool]
is_token_close = lambda tok: isinstance(tok, TokenClose)

class Parser:
    """
    Pratt parser

    1 + 2 + 3 + 4

    when doing a loop, you're associating to the left
    ((1 + 2) + 3) + 4
    when doing recursion, you're associating to the right
    1 + (2 + (3 + 4))

    for the root parse call, loop condition is always true
    if, afterwards, the loop condition is always false
        parse = parse_atom
        => associating to the left
    if the loop condition is always true:
        parse = parse_atom ; parse operator ; parse
        => associating to the right

    Conclusion: if you want to associate to the left, make the loop condition
    false.

    You want to associate to the left when the previous operator's bp is higher
    than the current one.

    parse(bp):
        left = parse_atom()
        op = peek operator
        while bp < op.bp:
            consume op
            left = expr(left, op, parse(op.bp))
    """


    inp: str

    tok: Token | None
    tok1: Token

    def __init__(self, inp: str):
        self.tok = None
        self.tok1, inp = get_next_token(inp)
        self.inp = inp


    def accept(self) -> Token:
        self.tok = self.tok1
        self.tok1, self.inp = get_next_token(self.inp)
        return self.tok

    def expect(self, p: TokenPredicate) -> None:
        tok = self.accept()
        if not p(tok):
            raise ValueError(f"expected {p} to hold for token {tok}")

    def peek(self) -> Token:
        return self.tok1

    def parse_atom(self) -> Expr[None, str]:
        tok = self.accept()
        if isinstance(tok, TokenLiteralNum):
            return ExprNum(None, tok.num)

        if isinstance(tok, TokenIdentifier):
            return ExprVar(None, tok.identifier)

        if isinstance(tok, TokenOpen):
            expr = self.parse_expr(0)
            self.expect(is_token_close)
            return expr

        if isinstance(tok, TokenOp) and isinstance(tok.op, UnaryOperator):
            op = SourceOperator[tok.op.name]
            expr = self.parse_atom()
            return ExprOp(None, op, (expr, ))

        raise ValueError(f"unexpected token {tok}")

    def parse_expr(self, bp: int) -> Expr[None, str]:
        """ bp = binding power """
        print(f'parser expr {self.tok1} {self.inp!r}')
        left: Expr[None, str] = self.parse_atom()
        print(f'  atom {left} {self.inp!r}')

        while True:

            tok_op = self.peek()
            if isinstance(tok_op, TokenEOF | TokenClose):
                return left

            assert isinstance(tok_op, TokenOp) and isinstance(tok_op.op, BinaryOperator), f"expected token op, got {tok_op}"
            op_desc = tok_op.op.value
            if bp >= op_desc.bp:
                return left

            self.accept()  # consume operator

            left = ExprOp(None, SourceOperator[tok_op.op.name], (left, self.parse_expr(op_desc.bp)))


def parse_expr(inp: str) -> Expr[None, str]:
    p = Parser(inp)
    expr = p.parse_expr(bp=0)
    tok = p.accept()
    if not isinstance(tok, TokenEOF):
        raise ValueError(f"left over tokens in expression {tok} {p.inp!r}")
    return expr


def serialize_expr(expr: Expr[None, str]) -> str:
    if isinstance(expr, ExprNum):
        return f'{expr.num}'
    elif isinstance(expr, ExprVar):
        return f'{expr.name}'
    elif isinstance(expr, ExprSymbol):
        return f'{expr.name}'
    elif isinstance(expr, ExprFunction):
        return f'({expr.function_name}({", ".join(serialize_expr(arg) for arg in expr.arguments)}))'
    elif isinstance(expr, ExprType):
        assert False, "don't expect expr type"
    elif isinstance(expr, ExprOp):
        if expr.operator.name in UnaryOperator.__members__:
            assert len(expr.operands) == 1, 'unary operator expects 1 operand'
            parser_operator = UnaryOperator[expr.operator.name]
            return f"({parser_operator.value.symbol}({serialize_expr(expr.operands[0])}))"
        if expr.operator.name in BinaryOperator.__members__:
            assert len(expr.operands) == 2, 'binary operator expects 2 operands'
            parser_operator = BinaryOperator[expr.operator.name]
            return f"({serialize_expr(expr.operands[0])} {parser_operator.value.symbol} {serialize_expr(expr.operands[1])})"
        raise ValueError(f'unsupported operator {expr.operator}')
    assert_never(expr)

if __name__ == '__main__':
    # print(get_all_tokens('(a + 2 <u 0) ==> b == -1'))

    print(serialize_expr(parse_expr('(a + 2) * 3')))
    print(serialize_expr(parse_expr('a + 2 * 3')))
    print(serialize_expr(parse_expr('a * 2 + 3')))


