## What changed

Proved `CategoryTheory.ringedExtendedCech_unit_isIso_implies_complete` in
`Sheaf.Paper.ExtendedCechUnitIsoImpliesComplete`, with its statement unchanged.
Added proof-only imports and private proved helpers for localization flatness,
the localized two-term contraction, K-flatness, derived Hom currying, and local
linear-combination descent. The existing three public imports are unchanged.
Updated the node's proof, proof dependencies, and proof origin to match the Lean
argument. No definitions, public signatures, or other Lean modules change.
The complete item compiled without warnings through `lcompile.py` in 42.0 seconds.
The previous session attempted delivery twice. `deliver3.py` failed before pushing because its probe
could not find the mirrored object file for
`WeilConjectures.Algebra.Homology.HomComplex`. Retrying with the supported
`LCOMPILE_NO_LOCAL=1` setting returned the same 0.7-second failure. This is a
delivery-tool failure after the successful complete-file compile; no delivery
commit was pushed.
On resumption, the required initial delivery check reproduced the same missing
`WeilConjectures.Algebra.Homology.HomComplex.olean` error at probe line 6 in 0.7
seconds. A further delivery attempt with `LCOMPILE_NO_LOCAL=1` returned the same
error and timing. Inspection of `lcompile.py` shows that its attached-result
cache key omits this environment setting and that missing-object errors are
cacheable. Thus the supported remote-mode retry does not obtain a fresh result
for this probe. The launcher scripts and cache were not modified, and the proof
packet remains intact for the launcher owner to repair the compile service.
The proof-scope commands and unchanged consumers are documented in
`coord/changes/V8-extended-cech-unit-private-proof-scopes.md`.

The localization tensor and flatness calculations follow the existing private
calculations in `Sheaf.CategoryTheory.RingedLocalizationFactorTensorAugmentation`
and `Sheaf.Paper.RingedLocalizationModels`. The K-flatness calculations follow
`Sheaf.CategoryTheory.RingedCechCompletionUnitIdempotence`; the local-span
calculation follows `Sheaf.Paper.RingedGeneratingListsLocalEquality`. They are
proved here as private helpers rather than changing those modules' interfaces.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.ringedExtendedCech_unit_isIso_implies_complete`
(node `lem-weil-pbc-extended-cech-unit-isIso-implies-complete`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered Lean
file. The proof uses the already declared intermediate results listed in the
updated node; their existing proof obligations are unchanged.

## No longer needed

The assigned proof no longer imports or directly uses
`Sheaf.Paper.RingedLocalizationRHomCalculus`
(node `lem-weil-pbc-ringed-localization-rhom-calculus`). Its packaged
standard-universe localization calculus is replaced by the K-flat currying
comparison in the theorem's chosen derived-category universe. The tensor
contraction and all glue for this implication are proved in the item itself.
No original public import was removed, and no module is withdrawn. This removes
only the dependency of this node; it does not claim the calculus module is unused
by its other consumers. The blueprint unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The original single proof step
left the contraction and currying glue implicit. The delivered proof supplies
it, reindexing each chosen generator to the first position so that associativity
alone suffices for the tensor-complex calculation. The argument also explicitly
handles a zero-length generating list through the zero ideal and covering
descent. No further split of this repeatedly split obligation was necessary.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
