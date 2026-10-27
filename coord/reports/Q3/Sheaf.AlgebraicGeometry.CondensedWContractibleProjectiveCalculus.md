## What changed

Completed `AlgebraicGeometry.ProEtale.CondensedRing.condensed_wcontractible_projective_calculus`.
The proof uses the existing fully faithful evaluation and perfect/lisse equivalence,
K-projective chain representatives, the actual finite-projective mapping cone, and
uniqueness of distinguished triangles with a fixed first arrow. It proves zero and
shift closure, isomorphism invariance, the arrow lifting square, and the scalar clause.
For scalar extension, it computes the specified left adjoint on bounded flat models
using the normalized derived-adjunction K-flat representative theorem. Tensor-product
instances supply finite generation and projectivity without flatness of the ring map.

Repaired the shared `CondensedLisseEvaluationModel.componentComparisons` interface:
the section-ring isomorphism now explicitly preserves point scalars. Its normalization
uses `affineScalarSection`, which is the original concrete scalar-section construction
moved verbatim from this item (with the underlying ring object as parameter).
`projectiveCalculusScalarSection` is a definitional alias, so the item statement has
exactly the same meaning and no target signature changes.

The existing `CondensedComponentPullbackCompatibility` theorem uses this repaired
predicate. Its existing proof hole remains; its node and docstring now explain the
scalar-normalization obligation, by monoidal naturality of the point-factorization
comparison. This is recorded as an interface repair, not as a proof of that theorem.
The item theorem signature is byte-identical to the original; the moved scalar
constructor body is byte-identical after replacing the bundled `Λ.X` parameter by `Λ`.
Validation: the item compiles cleanly against the changed sandbox modules (23.4 s).
The model and component theorem also compile; all Lean lines are within 100 characters.
The item signature and relocated scalar constructor body were compared verbatim.
No upstream source-library module is modified. Change record:
`coord/changes/condensed-component-scalar-normalization-Q3.md`.

The original, unchanged `CondensedWContractibleLisseEvaluation` consumer compiles
against the repaired model and passes the strengthened comparison through its existing
proof. Textual consumer searches include the quarantined Sheaf tree.

Source reading: HRS (3.1), (3.2), Remark 3.2, Definition 3.3, Lemma 4.1 and Proposition
4.3(3), especially the canonical coefficient identification preceding its last square.
Read the current blueprint's relative-purity proof and the unit realized record; this
node is below the unit route, whose statement and steps are unchanged. Edge cases:
empty affine, zero ring, zero complexes, arbitrary shifts, prescribed representative
isomorphisms, zero/identity arrows, and nonflat scalar maps are all covered by the same
cone, adjunction and tensor-retract arguments.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`AlgebraicGeometry.ProEtale.CondensedRing.condensed_wcontractible_projective_calculus`
(node `lem-zl-condensed-wcontractible-projective-calculus`). The item has zero sorry.

Added zero holes and split off zero statements. The delivered dependency module retains
its one existing named hole:
`AlgebraicGeometry.ProEtale.CondensedRing.condensed_component_pullback_compatibility`
(node `lem-zl-condensed-component-pullback-compatibility`). Its conclusion gains the
canonical scalar normalization described above; no claim is made that this retained
hole is closed. All private helpers in the item are proved. The model contains no sorry.

The result is a proof from existing named dependencies, including that repaired
component theorem; it does not assert that the item's transitive axioms are sorry-free.

## No longer needed

Removed proof-only imports:
`WeilConjectures.Algebra.Homology.BoundedFlatKFlat` and
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, and the redundant
`Mathlib.Algebra.Homology.HomotopyCategory.KProjective` (already imported by
`Mathlib.Algebra.Homology.DerivedCategory.KProjective`).
The ordinary change-of-rings universal pair is unnecessary: the specified scalar functor
is already a left adjoint, and the existing exact-right-adjoint K-flat representative
API computes it directly. Thus nodes `lem-pur-derived-change-of-rings` and
`lem-pc-module-bounded-flat-kflat` are no longer direct proof dependencies of this item.
The proof uses the established bounded-flat K-flat API directly instead of the separate
acyclic-tensor theorem. Their modules and declarations remain in the library; no global
withdrawal is proposed, since they may have other consumers.

No other dependency from the original cone/evaluation route is pruned, and no module
is withdrawn. Added only proof imports for the derived-adjunction representative API,
the existing scalar-adjunction construction, extension preserving K-flat quasi-isos,
and Mathlib finite tensor products. No new public proof imports.

The additional generic tools are `lem-sfb-exact-right-adjoint-kflat-representative`,
`lem-weil-pbc-derived-module-scalar-adjunction`, and
`lem-pc-extension-kflat-quasi-iso`. They supply the representative comparison for the
already fixed left adjoint; none bypasses a mathematical step of the unit. No unit
node supplies that normalized left-adjoint API. The original ordinary-change-of-rings
node instead chooses another universal derived functor, adding an avoidable comparison.
No maintainer `tool_uses` approval is added or changed by this packet.

## Where the brief, the DAG or earlier work was wrong

The evaluation theorem exposed a natural scalar comparison along a composite ring map,
but its component section-ring isomorphism had no scalar-normalization equation. The
DAG's final step asserted that this composite was the explicit point-pullback scalar
map, which did not follow from the old Lean interface. The interface repair adds that
missing canonical compatibility, as the original proof text and HRS source require.
The new condition strengthens a comparison-data proposition; it changes neither lisse
nor perfectness nor any coefficient ring or derived tensor construction.

The ordinary change-of-rings node states a universal derived functor and not a direct
comparison with this item's chosen left adjoint. Using the existing normalized
left-adjoint representative theorem avoids that unnecessary identification layer.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
