import pytest

from expr_parser import parse_expr, serialize_expr

@pytest.mark.parametrize('expr, serialized_expr', (
    ('(a + 2) * 3', '((a + 2) * 3)'),
    ('a + 2 * 3', '(a + (2 * 3))'),
    ('a * 2 + 3', '((a * 2) + 3)'),
    ('a * 2 + 3', '((a * 2) + 3)'),
    ('a * 2 + 3 * b', '((a * 2) + (3 * b))'),
    ('a * 2 + 3 * b', '((a * 2) + (3 * b))'),
    ('a * 2 + 3 - b', '(((a * 2) + 3) - b)'),
    ('a - b - c', '((a - b) - c)'),
    ('-2 + 3', '(-2 + 3)'),
    ('3 + -2', '(3 + -2)'),
    ('3 + -2', '(3 + -2)'),
    ('3 + -2 - 1', '((3 + -2) - 1)'),
    ('~2', '(~(2))'),
    ('~2 - 1', '((~(2)) - 1)'),
    ('~2 - 4*2 >s 2 ==> foo', '(((((~(2)) - (4*2))) >s 2) ==> foo)'),
))
def test_expr_parser_table(expr: str, serialized_expr: str):
    actual = serialize_expr(parse_expr(expr))
    assert actual == serialized_expr
