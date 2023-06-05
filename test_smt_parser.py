import smt_parser
import parser_combinator as pc
import smt
import source
import glob
from typing import Literal, Sequence, Callable
import assume_prove as ap


def test_parse_identifier() -> None:
    f = smt_parser.parse_identifier()
    maybeIdentifier = pc.parse(f, "hello")
    assert not isinstance(maybeIdentifier, pc.ParseError)
    (ident, s) = maybeIdentifier
    assert ident == "hello"
    assert s == ''

    maybeIdentifier = pc.parse(f, "123hello")
    assert isinstance(maybeIdentifier, pc.ParseError)


def test_parse_cmd_declare_fun() -> None:
    f = smt_parser.parse_cmd_declare_fun()
    maybeDeclFun = pc.parse(f, "(declare-fun id () Bool)")
    assert not isinstance(maybeDeclFun, pc.ParseError)
    (declFun, s) = maybeDeclFun
    declFunExpected = smt.CmdDeclareFun(symbol=smt.Identifier(
        "id"), arg_sorts=[], ret_sort=source.type_bool)
    assert declFun == declFunExpected
    assert s == ''

    string = "(declare-fun PMS!val!1 () PMS)"
    maybeDeclFun = pc.parse(f, string)
    assert not isinstance(maybeDeclFun, pc.ParseError)

    _, s = maybeDeclFun
    assert s.strip() == ''


def test_parse_op() -> None:
    f = smt_parser.parse_op()
    maybeOp = pc.parse(f, "bvadd")
    assert not isinstance(maybeOp, pc.ParseError)
    (op, s) = maybeOp
    assert op == source.Operator.PLUS
    assert s == ''

    maybeOp = pc.parse(f, "bvsub")
    assert not isinstance(maybeOp, pc.ParseError)
    (op, s) = maybeOp
    assert op == source.Operator.MINUS
    assert s == ''


def test_parse_sorted_var() -> None:
    f = smt_parser.parse_sorted_var()
    maybeSortedVar = pc.parse(f, "(x Bool)")
    assert not isinstance(maybeSortedVar, pc.ParseError)


def test_parse_decl_fun_model() -> None:
    f = smt_parser.parse_model_response()
    maybeFunModel = pc.parse(f, "(define-fun blah () Bool true)")
    assert not isinstance(maybeFunModel, pc.ParseError)
    (funModel, s) = maybeFunModel
    assert funModel == smt.CmdDefineFun(
        symbol=smt.Identifier("blah"), args=[], ret_sort=source.type_bool, term=source.expr_true)
    assert s == ''


def get_bool(val: bool) -> source.ExprT[ap.VarName]:
    if val:
        return source.expr_true
    return source.expr_false


def get_bitvec_from_str(val: str, base: Literal[2, 16]) -> source.ExprT[ap.VarName]:
    val = val[2:]
    intval = int(val, base)
    return source.ExprNum(typ=source.type_word32, num=intval)


def get_cmd_define_fun(name: str, ty: source.Type, e: source.ExprT[ap.VarName]) -> smt.CmdDefineFun:
    return smt.CmdDefineFun(symbol=smt.Identifier(name), args=[], ret_sort=ty, term=e)


def get_bool_fn(name: str, b: bool) -> smt.CmdDefineFun:
    return get_cmd_define_fun(name, source.type_bool, get_bool(b))


def get_bvec_fn(name: str, val: str, base: Literal[2, 16]) -> smt.CmdDefineFun:
    return get_cmd_define_fun(name, source.type_word32, get_bitvec_from_str(val, base))


def test_parse_model() -> None:
    f = smt_parser.parse_responses()
    maybeResponses = pc.parse(f,
                              """
        sat
        sat
        (model
        (define-fun node_Err_ok () Bool false)
        (define-fun node_Ret_ok () Bool true)
        (define-fun node_2_ok () Bool false)
        (define-fun node_17_ok () Bool false)
        (define-fun node_9_ok () Bool false)
        (define-fun node_8_ok () Bool false)
        (define-fun node_7_ok () Bool true)
        (define-fun node_j2_ok () Bool true)
        (define-fun node_6_ok () Bool false)
        (define-fun node_5_ok () Bool false)
        (define-fun node_j1_ok () Bool false)
        (define-fun node_4_ok () Bool false)
        (define-fun node_3_ok () Bool true)
        (define-fun node_1_ok () Bool true)
        (define-fun a___int@v~1 () (_ BitVec 32) #b10101000000000000000101000000000)
        (define-fun b___int@v~1 () (_ BitVec 32) #b01011100100000000000000000000000)
        (define-fun b___int@v~2 () (_ BitVec 32) #b10011011111111111111011000000000)
        (define-fun a___int@v~3 () (_ BitVec 32) #b00000100100000000000101000000000)
        (define-fun b___int@v~3 () (_ BitVec 32) #b01011100100000000000000000000000)
        (define-fun a___int@v~2 () (_ BitVec 32) #b00000100100000000000101000000000)
        (define-fun ret__int@v~1 () (_ BitVec 32) #b00000000000000000000000000000000)
        )
        """)
    assert not isinstance(maybeResponses, pc.ParseError)
    (responses, s) = maybeResponses
    assert len(responses) == 3
    assert s.isspace()
    assert responses[0] == smt.CheckSatResponse.SAT
    assert responses[1] == smt.CheckSatResponse.SAT
    assert isinstance(responses[2], Sequence)
    assert len(responses[2]) == 21

    res = [get_bool_fn("node_Err_ok", False), get_bool_fn("node_Ret_ok", True), get_bool_fn("node_2_ok", False), get_bool_fn("node_17_ok", False), get_bool_fn("node_9_ok", False), get_bool_fn("node_8_ok", False), get_bool_fn("node_7_ok", True), get_bool_fn("node_j2_ok", True), get_bool_fn("node_6_ok", False), get_bool_fn("node_5_ok", False), get_bool_fn("node_j1_ok", False), get_bool_fn("node_4_ok", False), get_bool_fn("node_3_ok", True), get_bool_fn("node_1_ok", True), get_bvec_fn("a___int@v~1", "#b10101000000000000000101000000000", 2), get_bvec_fn("b___int@v~1", "#b01011100100000000000000000000000", 2), get_bvec_fn("b___int@v~2", "#b10011011111111111111011000000000", 2), get_bvec_fn("a___int@v~3", "#b00000100100000000000101000000000", 2), get_bvec_fn("b___int@v~3", "#b01011100100000000000000000000000", 2), get_bvec_fn("a___int@v~2", "#b00000100100000000000101000000000", 2), get_bvec_fn("ret__int@v~1", "#b00000000000000000000000000000000", 2)
           ]

    for out, expected in zip(responses[2], res):
        assert out == expected

    maybeResponses = pc.parse(f,
                              """
        unsat 
        unknown 
        (
          (define-fun node_Ret_ok () Bool
            true)
          (define-fun node_9_ok () Bool
            false)
          (define-fun node_1_ok () Bool
            true)
          (define-fun b___int@v~1 () (_ BitVec 32)
            #x8c044046)
          (define-fun node_17_ok () Bool
            false)
          (define-fun b___int@v~3 () (_ BitVec 32)
            #x12010094)
          (define-fun a___int@v~3 () (_ BitVec 32)
            #x2fdf0018)
          (define-fun node_j2_ok () Bool
            true)
          (define-fun node_3_ok () Bool
            true)
          (define-fun node_4_ok () Bool
            false)
          (define-fun node_8_ok () Bool
            true)
          (define-fun node_Err_ok () Bool
            false)
          (define-fun node_7_ok () Bool
            true)
          (define-fun node_2_ok () Bool
            false)
          (define-fun a___int@v~1 () (_ BitVec 32)
            #xc4048048)
          (define-fun a___int@v~2 () (_ BitVec 32)
            #x2fdf0018)
          (define-fun node_5_ok () Bool
            true)
          (define-fun node_6_ok () Bool
            false)
          (define-fun node_j1_ok () Bool
            true)
          (define-fun ret__int@v~1 () (_ BitVec 32)
            #x00000000)
          (define-fun b___int@v~2 () (_ BitVec 32)
            #x00000000)
        )
        """)
    assert not isinstance(maybeResponses, pc.ParseError)
    (responses, s) = maybeResponses
    assert s.isspace()
    assert len(responses) == 3
    assert responses[0] == smt.CheckSatResponse.UNSAT
    assert responses[1] == smt.CheckSatResponse.UNKNOWN
    assert isinstance(responses[2], Sequence)
    assert len(responses[2]) == 21

    res = [
        get_bool_fn("node_Ret_ok", True),
        get_bool_fn("node_9_ok", False),
        get_bool_fn("node_1_ok", True),
        get_bvec_fn("b___int@v~1", "#x8c044046", 16),
        get_bool_fn("node_17_ok", False),
        get_bvec_fn("b___int@v~3", "#x12010094", 16),
        get_bvec_fn("a___int@v~3", "#x2fdf0018", 16),
        get_bool_fn("node_j2_ok", True),
        get_bool_fn("node_3_ok", True),
        get_bool_fn("node_4_ok", False),
        get_bool_fn("node_8_ok", True),
        get_bool_fn("node_Err_ok", False),
        get_bool_fn("node_7_ok", True),
        get_bool_fn("node_2_ok", False),
        get_bvec_fn("a___int@v~1", "#xc4048048", 16),
        get_bvec_fn("a___int@v~2", "#x2fdf0018", 16),
        get_bool_fn("node_5_ok", True),
        get_bool_fn("node_6_ok", False),
        get_bool_fn("node_j1_ok", True),
        get_bvec_fn("ret__int@v~1", "#x00000000", 16),
        get_bvec_fn("b___int@v~2", "#x00000000", 16)
    ]

    maybeResponses = pc.parse(f,
                              """
        sat
        sat
        (
        (define-fun node_Err_ok () Bool false)
        (define-fun node_Ret_ok () Bool true)
        (define-fun node_2_ok () Bool false)
        (define-fun node_17_ok () Bool false)
        (define-fun node_9_ok () Bool false)
        (define-fun node_8_ok () Bool true)
        (define-fun node_7_ok () Bool true)
        (define-fun node_j2_ok () Bool true)
        (define-fun node_6_ok () Bool false)
        (define-fun node_5_ok () Bool false)
        (define-fun node_j1_ok () Bool false)
        (define-fun node_4_ok () Bool false)
        (define-fun node_3_ok () Bool true)
        (define-fun node_1_ok () Bool true)
        (define-fun a___int@v~1 () (_ BitVec 32) #b10000000000000001111010001100010)
        (define-fun b___int@v~1 () (_ BitVec 32) #b00000000000000000000101111011110)
        (define-fun b___int@v~2 () (_ BitVec 32) #b00000000000000000000000000000000)
        (define-fun a___int@v~3 () (_ BitVec 32) #b10000000000000010000000001000000)
        (define-fun b___int@v~3 () (_ BitVec 32) #b00000000000000000000101111011110)
        (define-fun a___int@v~2 () (_ BitVec 32) #b10000000000000010000000001000000)
        (define-fun ret__int@v~1 () (_ BitVec 32) #b00000000000000000000000000000000)
        )""")
    assert not isinstance(maybeResponses, pc.ParseError)
    assert s.isspace()
    (responses, s) = maybeResponses
    assert len(responses) == 3
    assert responses[0] == smt.CheckSatResponse.SAT
    assert responses[1] == smt.CheckSatResponse.SAT
    assert isinstance(responses[2], Sequence)
    assert len(responses[2]) == 21

    res = [get_bool_fn("node_Err_ok", False), get_bool_fn("node_Ret_ok", True), get_bool_fn("node_2_ok", False), get_bool_fn("node_17_ok", False), get_bool_fn("node_9_ok", False), get_bool_fn("node_8_ok", True), get_bool_fn("node_7_ok", True), get_bool_fn("node_j2_ok", True), get_bool_fn("node_6_ok", False), get_bool_fn("node_5_ok", False), get_bool_fn("node_j1_ok", False), get_bool_fn("node_4_ok", False), get_bool_fn("node_3_ok", True), get_bool_fn("node_1_ok", True), get_bvec_fn("a___int@v~1", "#b10000000000000001111010001100010", 2), get_bvec_fn("b___int@v~1", "0b00000000000000000000101111011110", 2), get_bvec_fn("b___int@v~2", "#b00000000000000000000000000000000", 2), get_bvec_fn("a___int@v~3", "#b10000000000000010000000001000000", 2), get_bvec_fn("b___int@v~3", "#b00000000000000000000101111011110", 2), get_bvec_fn("a___int@v~2", "#b10000000000000010000000001000000", 2), get_bvec_fn("ret__int@v~1", "#b00000000000000000000000000000000", 2)
           ]

    for out, expected in zip(responses[2], res):
        assert out == expected


def test_complex() -> None:
    fn = smt_parser.parse_responses()
    with open("./tests/smt/pass/complex.smt", "r") as f:
        data = f.read()
        maybeModels = pc.parse(fn, data)
        assert not isinstance(maybeModels, pc.ParseError)
        # print(maybeModels)
        _, s = maybeModels
        assert s.strip() == ""


def test_parse_parens_balance() -> None:
    string = "(+ 3 4))"
    fn = smt_parser.parse_balanced_parens()
    maybeStr = fn(string)
    assert not isinstance(maybeStr, pc.ParseError)
    res_str, leftover = maybeStr
    assert leftover == ")"
    assert res_str == string[:-1]

    string = "3)"
    fn = smt_parser.parse_balanced_parens()
    maybeStr = fn(string)
    assert not isinstance(maybeStr, pc.ParseError)
    res_str, leftover = maybeStr
    assert leftover == ")"
    assert res_str == string[:-1]

    string = "(+ 3 (* 4 5)))"
    fn = smt_parser.parse_balanced_parens()
    maybeStr = fn(string)
    assert not isinstance(maybeStr, pc.ParseError)
    res_str, leftover = maybeStr
    assert leftover == ")"
    assert res_str == string[:-1]

    string = "(_ bv0 64))"
    fn = smt_parser.parse_balanced_parens()
    maybeStr = fn(string)
    assert not isinstance(maybeStr, pc.ParseError)
    res_str, leftover = maybeStr
    assert leftover == ")"
    assert res_str == string[:-1]

    string = "HTD!val!0)"
    fn = smt_parser.parse_balanced_parens()
    maybeStr = fn(string)
    assert not isinstance(maybeStr, pc.ParseError)
    res_str, leftover = maybeStr
    assert leftover == ")"


def test_parse_typed_arg() -> None:
    string = "(abc (_ BitVec 64))"
    maybeTypedArg = smt_parser.parse_sorted_var()(string)
    assert not isinstance(maybeTypedArg, pc.ParseError)
    typedArg, s = maybeTypedArg
    assert typedArg.name == "abc"
    assert typedArg.typ == source.type_word64
    assert s == ""


def test_parse_cmd_define_fun() -> None:
    string = "(define-fun asd ((x (_ BitVec 64)) (y (Array (_ BitVec 64) (_ BitVec 64)))) (_ BitVec 64) (_ bv0 64))"
    maybeDefineFun = smt_parser.parse_cmd_define_fun_partial()(string)
    assert not isinstance(maybeDefineFun, pc.ParseError)
    defineFun, s = maybeDefineFun
    assert defineFun.symbol == "asd"
    assert defineFun.term == "(_ bv0 64)"
    assert s == ""

    string = "(define-fun HTD~1 () HTD HTD!val!0)"
    maybeDefineFun = smt_parser.parse_cmd_define_fun_partial()(string)
    assert not isinstance(maybeDefineFun, pc.ParseError)
    defineFun, s = maybeDefineFun
    assert defineFun.symbol == "HTD~1"
    assert len(defineFun.args) == 0
    assert isinstance(defineFun.ret_sort, source.TypeBuiltin)
    assert defineFun.ret_sort == source.TypeBuiltin(source.Builtin.HTD)
    assert defineFun.term == "HTD!val!0"
    assert s == ""

    string = "(define-fun node_guard_n7_ok () Bool false)"
    maybeDefineFun = smt_parser.parse_cmd_define_fun_partial()(string)
    assert not isinstance(maybeDefineFun, pc.ParseError)
    defineFun, s = maybeDefineFun
    assert defineFun.symbol == "node_guard_n7_ok"


def test_parse_type_word_array() -> None:
    string = "(Array (_ BitVec 50) (_ BitVec 46))"
    maybeWordArray = smt_parser.parse_type_word_array()(string)
    assert not isinstance(maybeWordArray, pc.ParseError)
    wordArray, s = maybeWordArray
    assert s == ""
    assert isinstance(wordArray, source.TypeWordArray)
    assert wordArray.index_bits == 50
    assert wordArray.value_bits == 46


def test_parse_model_response() -> None:
    string = "(define-fun asd ((x (_ BitVec 64)) (y (Array (_ BitVec 64) (_ BitVec 64)))) (_ BitVec 64) (_ bv0 64))"
    maybeDefineFun = smt_parser.parse_model_response()(string)
    assert not isinstance(maybeDefineFun, pc.ParseError)
    defineFun, s = maybeDefineFun
    assert isinstance(defineFun, smt.CmdPartialDefineFun)
    assert defineFun.symbol == "asd"
    assert defineFun.term == "(_ bv0 64)"
    assert s == ""


def test_should_parse_files() -> None:
    fn = smt_parser.parse_responses()
    for file in glob.glob("./tests/smt/pass/*.smt"):
        with open(file, "r") as f:
            data = f.read()
            maybeModels = pc.parse(fn, data)
            assert not isinstance(maybeModels, pc.ParseError)
            _, s = maybeModels
            assert s.strip() == ""


def test_should_parse_libsel4cp_model() -> None:
    fn = smt_parser.parse_responses()
    with open("./tests/smt/pass/libsel4cp.smt", "r") as f:
        s = f.read()
        maybeModels = pc.parse(fn, s)
        assert not isinstance(maybeModels, pc.ParseError)
        _, s = maybeModels
        print(s.strip())
        assert s.strip() == ""


def test_parse_forall() -> None:
    fn = smt_parser.parse_forall()
    string = """
    (forall ((x PMS)) 
        (or (= x PMS!val!1) 
            (= x PMS!val!2) 
            (= x PMS!val!0) 
            (= x PMS!val!3) 
            (= x PMS!val!4)))"""
    maybeForall = fn(string)
    assert not isinstance(maybeForall, pc.ParseError)
    _, s = maybeForall
    assert s.strip() == ""

    string = """
    (forall ((x HTD)) 
        (or (x = HTD!val!0) (= x HTD!val!2) (= x HTD!val!3) (= x HTD!val!1)))
    """
    maybeForall = fn(string)
    assert not isinstance(maybeForall, pc.ParseError)
    _, s = maybeForall
    assert s.strip() == ""
