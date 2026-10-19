## What changed

Proved `AlgebraicGeometry.Etale.goodCurvesPreimage_boundary` with its signature unchanged.
The pullback maps openly into the coproduct of the proper models; its opensRange supplies the
required open and canonical isomorphism. A private proved finite-index induction establishes
properness from `proper_coproduct_two`. Finite type over the Noetherian base and compactness then
give Noetherianity. Density and surjectivity supply the nonempty open fibres required by
`good_curves_boundary_quasiFinite`. The finite family is lifted to `ULift (Fin n)` to match
that theorem's index universe, and the explicitly constructed reduced closed complement is
transported along the canonical coproduct isomorphism.

Added a proof-only import of
`WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.PiProd` for `sigmaOptionIso`.
Updated the existing node's proof route and removed its unused finite-coproduct dependency.
No signatures, definitions, public imports, or other modules were changed.
The conservative command scanner requires a change record for the added namespace open and
local colimit-instance priorities: `coord/changes/A8-good-curves-preimage-boundary-elaboration.md`.
The direct consumer `GoodCurvesPreimageConstructible` uses the unchanged signature at line 277.
The retained proof was repaired against current compiler diagnostics: explicit open-set
coercions, terminal reflexivity steps, coproduct-map transport, and composition association.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.goodCurvesPreimage_boundary`
(node `lem-weil-pbc-good-curves-preimage-boundary`).
Added holes: none. Split off: none. Sorries remaining in the delivered module: none.
The existing `AlgebraicGeometry.good_curves_boundary_quasiFinite` is used as the named
proof dependency intended by the brief; its proof remains that dependency's own item.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.FiniteCoproductLfpQcqs` and the
node dependency `lem-weil-pbc-finite-coproduct-lfp-qcqs`: properness already yields the
compactness needed for Noetherianity. Its extra finite-presentation and quasi-separatedness
conclusions are not used here. No other dependency nodes are bypassed, and the unit route stays.

## Where the brief, the DAG or earlier work was wrong

The boundary theorem binds its index in the schemes' universe. Direct specialization to
`Fin n` therefore fails for general `Scheme.{u}`. The proof handles this without changing
that other group's interface, by lifting the index and transporting its closed complement.
The DAG's separate finite-coproduct compactness step was redundant.

Searches used the prescribed leanfinder, loogle and grep services, then direct source searches
for coproduct properness, open-immersion coproducts, fibre homeomorphisms and pullback ranges.
The existing binary proper-coproduct theorem and Mathlib's open-immersion APIs supply these
steps; no new statement is needed. Source read: `literature/stacks-project/more-etale.tex`,
`lemma-constant-shriek-rel-dim-1`, especially the second boundary Zprime.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
