## What changed

Proved `RingTheory.isRegularRing_transverseLocalRootFamily` with its exact original
signature and all public imports and definitions unchanged. All added helpers are private
and proved. Constructed the quotient/tensor algebra equivalence, the exact monomial basis,
coefficient reduction and one-root presentation equivalences, and the simultaneous
regularity induction. The off-root case uses the local proof of Stacks 07PF directly
in the prime localization of the polynomial ring. Updated the node to this route.
Proof-local transparency options and a private `import all` of the polynomial
implementation resolve instance equalities; they change no API.

## Proved and sorry left

Closed 1 of 1 original holes: `RingTheory.isRegularRing_transverseLocalRootFamily`
(node `lem-sfb-transverse-local-root-family-regular`). Added 0 holes; split off 0.
No `sorry` remains in the delivery. All private helpers have complete proofs.
The proof uses the existing named dependency declarations, without changing them.

## No longer needed

Removed proof imports `WeilConjectures.RingTheory.LocalizationOfRegularRing`,
`WeilConjectures.RingTheory.HypersurfaceDerivationRegular`, and
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`.
The route does not use `lem-weil-pbc-localization-of-regular-ring` or
`lem-weil-pbc-hypersurface-derivation-regular`: the off-root calculation is performed
directly in the regular local polynomial ring. Removed their obsolete tool-use entries.
`lem-weil-pbc-noetherian-local-finite-krull-dimension` is unnecessary: regular-local
embedding dimensions already express both dimensions as finite natural numbers.
These modules/nodes may still have other consumers; no module is withdrawn.
The monic quotient, finite algebra Noetherianity, regular-local domain/localization,
root-at-root, polynomial regularity and regular ring definition dependencies remain.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The planned coefficient dimension subtraction and two
prime cases are valid, including empty K/I and n=1. The tensor power-basis argument
replaces the proposed iterative basis bookkeeping. The auxiliary localization A[1/f]
is unnecessary in the off-root case. The current unit route is preserved.
The two newly used existing generic inputs are the localization part of
`lem-weil-pbc-derivation-extends` (already proved) and
`lem-weil-pbc-regular-local-hypersurface-criterion` (proved source declaration).
There are no new nodes, consumer adaptations, or definition repairs. The preflight
command comparison requested a change record for the proof-local section and options;
`coord/changes/D3-transverse-root-proof-section.md` documents that the public API is unchanged.

Validation: the full module compiled in 36.8 seconds with `lcompile.py`. The first
delivery passed compilation and the axiom probe; its preflight requested the proof-section
change record, now supplied. The final delivery reruns all required checks. Public signatures, definitions and
public imports were compared verbatim with the current shared source.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
