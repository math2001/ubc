from typing import NamedTuple


class ProvenanceGraphLang(NamedTuple):
    pass


class ProvenancePrelude(NamedTuple):
    source: str
    col: int
    row: int


class ProvenanceGhost(NamedTuple):
    pass


class ProvenanceNipGuard(NamedTuple):
    pass


class ProvenanceNipUpdate(NamedTuple):
    pass


class ProvenanceDSAJoiner(NamedTuple):
    pass

# TODO: deal with this when we have proper handling of universe variables


class ProvenanceUnknown(NamedTuple):
    pass


Provenance = ProvenanceGraphLang | ProvenancePrelude | ProvenanceGhost | ProvenanceNipGuard | ProvenanceNipUpdate | ProvenanceDSAJoiner | ProvenanceUnknown
