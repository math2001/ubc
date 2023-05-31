from typing import NamedTuple


class ProvenanceGraphLang(NamedTuple):
    pass


class ProvenanceNipGuard(NamedTuple):
    pass


class ProvenanceNipUpdate(NamedTuple):
    pass


class ProvenanceDSAJoiner(NamedTuple):
    pass


class ProvenancePreCondFnObligation(NamedTuple):
    pass


class ProvenancePostCondFnAssume(NamedTuple):
    pass


class ProvenancePreCond(NamedTuple):
    pass


class ProvenancePostCond(NamedTuple):
    pass


class ProvenanceLoopInvariantAssume(NamedTuple):
    pass


class ProvenanceLoopInvariantObligation(NamedTuple):
    pass

class ProvenanceCallStashInitialArgs(NamedTuple):
    pass

class ProvenanceCallStash(NamedTuple):
    pass


Provenance = ProvenanceGraphLang | ProvenanceNipGuard | ProvenanceNipUpdate | ProvenanceDSAJoiner | ProvenancePreCond | ProvenancePreCondFnObligation | ProvenancePostCondFnAssume | ProvenanceLoopInvariantAssume | ProvenanceLoopInvariantObligation | ProvenancePostCond | ProvenanceCallStashInitialArgs | ProvenanceCallStash  
