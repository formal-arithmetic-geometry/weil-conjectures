## What changed

Proved `AlgebraicGeometry.flat_fibre_component_closure_dimension` with its signature unchanged.
Private helpers construct the structure-sheaf stalk linear equivalence, transport associated
points from the scheme convention to the module convention on locally Noetherian fibres,
transfer stalkwise flatness, and identify reduced-closure fibres and their components with
the displayed topological subspaces.

The final proof applies the existing pointwise theorem
`AlgebraicGeometry.flat_relative_associated_specialization` directly, then transports its
dimension equality along homeomorphisms. Added private imports of
`Sheaf.AlgebraicGeometry.FlatRelativeAssociatedSpecialization`,
`WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`, and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`.
Updated the item node's proof, proof dependencies and proof origin to this route.
No public signature, definition, or public import changed. Only the item module, its node,
and the file-local proof-settings change record change.

Repair of the return at c08d7e55b: restored the original private import
`Sheaf.TraceFormula.FlatAssociatedEquidimensional`. The landing checker identified a
downstream use of its `AlgebraicGeometry.closureInclusion` in
`Sheaf.AlgebraicGeometry.HighGenusHomClosure`. Keeping the import preserves the original
import closure and needs no consumer adaptation. The theorem's direct pointwise proof
and updated DAG proof dependencies remain unchanged.

Validation: the repaired complete module compiled cleanly through lcompile.py in 26.6
seconds. All original imports are retained, the public theorem signature is unchanged,
and the module contains no `sorry`. Import-direction checking permits the pointwise dependency.
The proof handles empty intersections by the component quantifier, needs no Noetherianity
of the base, and uses local Noetherianity only for the fibre associated-prime convention.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.flat_fibre_component_closure_dimension`
(node `lem-trf-flat-fibre-component-closure-dimension`).
Added 0 holes. The item has 0 remaining sorries; no new modules or nodes are introduced.
The proof uses existing deferred theorems `AlgebraicGeometry.fibre_component_relative_associated`
and `AlgebraicGeometry.flat_relative_associated_specialization`; their proofs are outside
this delivery. This is a complete proof from existing DAG declarations, not a new decomposition.

## No longer needed

Removed no imports. The proof no longer needs the proof dependency
`lem-trf-flat-associated-equidimensional`: the pointwise specialization theorem already gives
`dim C = dim Y_t`, so neither a common integer dimension nor the factorization over the
reduced closure of the base point is needed. The item does not use `closureSubscheme`,
`closureInclusion`, `closureMap`, `fibreModule`, `fibreAssociated`, `relativeAssassin`, or
`moduleFlatAt` from that module. It instead uses the canonical module-relative-assassin API.
The module import is retained for downstream compatibility, so the module itself is not
pruned. No other declared item dependencies were pruned, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid but its two imported statements do not share a
Lean associated-point interface. Scheme associated points use radical annihilators, whereas
module associated points use actual annihilators. Local Noetherianity of the fibre and the
structure-sheaf pullback and stalk equivalences supply the required conversion explicitly.
The direct 0GSI route avoids the additional closure-of-base fibre comparison of the 0GSJ route.
The existing theorem docstring was updated to describe the implemented proof.

The returned delivery incorrectly removed an import needed by a downstream consumer.
This repair keeps that import, as requested by the landing checker.

Preflight also requested `coord/changes/Q7-flat-fibre-component-proof-settings.md` for
namespace opens and elaborator transparency options. The record inventories all 91
downstream modules; no consumer adaptation or signature change is needed.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
