## What changed

Proved WeilConjectures.PodHomChainDomains.domains_and_bijections in
Sheaf.Paper.PodHomChainCtfDomains with its exact existing signature. Extract the
seven full-subcategory object properties; obtain the projection IsIso from its
existing projectionIso; use bijectivity of the four supplied Hom equivalences;
prove bijectivity of precomposition with the forward projection by explicitly
precomposing with its inverse. This works uniformly for all four stages and
introduces no new construction, statement or hypothesis.

Updated lem-pod-hom-chain-ctf-domains's proof, proof_deps and proof_origin to
record this implementation. The only retained direct import is the public
Sheaf.Paper.PodCtfPairingMaps. Import-interface audit is recorded at
coord/changes/M1-pod-hom-chain-import-pruning.md. The only downstream module is
Sheaf.Paper.VerdierHomChainComposition; it already imports the removed upstream
adjunction module itself and needs no adaptation. The unit route is preserved:
this is the same Hom-chain bookkeeping on the stipulated restricted data.

## Proved and sorry left

Closed 1 of 1 holes: WeilConjectures.PodHomChainDomains.domains_and_bijections
(node lem-pod-hom-chain-ctf-domains). Added 0 holes; split off 0 statements.
No sorry remains in the item, and no other Lean module is changed. The proof
uses the existing canonical projection, whose projection-formula proof remains
a dependency; this does not claim that all transitive dependencies are closed.
The remote single-file compile of the complete proof succeeded in 14.8 seconds;
the final import-pruned version compiled cleanly in 13.0 seconds.

## No longer needed

Removed direct imports:

- WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
- Sheaf.Paper.DerivedPullbackTensorHom
- Sheaf.Paper.ExchangeProjectionSuppliedDomains
- Sheaf.Paper.FiniteTorStability
- Sheaf.Paper.SfIntegralDirectImageConstructible

The item's proof no longer calls fix-prop-adjunctions, thm-sf-ctf-stability,
def-weil-derived-pullback-tensor-hom,
lem-sf-integral-direct-image-constructible, fix-prop-projection-formula or
def-exchange-projection directly: supplied restricted R already packages domain
preservation and the adjunctions; PodCtfPairing.projectionIso packages the
canonical projection theorem. These earlier nodes and modules remain available
and may remain needed by those constructions or by other consumers. No module
is withdrawn and no source-library declaration is removed.

Kept det-thm-sf-ctf-stability-adjunctions and def-pod-ctf-pairing-maps as direct
proof dependencies. No top-level tool approval was removed.

## Where the brief, the DAG or earlier work was wrong

The original plan repeats coefficient-by-coefficient stability and restriction
arguments that the statement's supplied PodCtfAdjunctionData already contains.
They are needed to construct such data, rather than to extract properties of
its restricted objects. The projection was already defined as the hom of the
canonical projectionIso. No mathematical error or statement repair was needed.
Mathlib search found Iso.homFromEquiv and Iso.homToEquiv; the proof instead gives
the elementary inverse calculation directly, keeping the specified direction
visible. No new nodes or changes to unit steps are required.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
