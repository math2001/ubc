from __future__ import annotations
from typing import TypeAlias
from typing_extensions import NewType
from dataclasses import dataclass
SMTLIB = NewType("SMTLIB", str)

SMTVarName = NewType("SMTVarName", str)


@dataclass(frozen=True, order=True)
class SMTTyBool():
    bvsize: int = 1


@dataclass(frozen=True, order=True)
class SMTTyCh():
    bvsize: int = 8


@dataclass(frozen=True, order=True)
class SMTTyMsgInfo():
    bvsize: int = 80


@dataclass(frozen=True, order=True)
class SMTTyMaybe():
    a: SMTType
    @property
    def bvsize(self) -> int:
        return self.a.bvsize + 1


@dataclass(frozen=True, order=True)
class SMTTyTuple():
    fst: SMTType
    snd: SMTType

    @property
    def bvsize(self) -> int:
        return self.fst.bvsize + self.snd.bvsize

@dataclass(frozen=True, order=True)
class SMTTyBitVec:
    bvsize: int


SMTType: TypeAlias = SMTTyBool | SMTTyCh | SMTTyMsgInfo | SMTTyMaybe | SMTTyTuple | SMTTyBitVec
