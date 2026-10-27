## What changed

Proved `AlgebraicGeometry.point_tangent_separation_closed_immersion` with its public
signature and all five public imports unchanged. The repair also exposes the existing proved
`AlgebraicGeometry.generatingSections_pair` in
`Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed`, keeping its type and proof,
and records it in that module's existing DAG node. There are no definition or
target changes. The helper's visibility change is documented in
`coord/changes/R2-generatingSections-pair-public.md`.

The proof constructs finite-dimensionality using proper cohomology, proves that each
basis generates by the stalk-span criterion, and compares the selected projective
morphism with the native chart construction to obtain a coordinate-preserving twist
isomorphism. The assigned module privately imports
`Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed` and uses its existing pair
theorem. Both duplicate private helpers (`generatingSections_pair` and
`nativeHom_eq_generatingSections`) are removed from the assigned module; the
native-map comparison remains private in its original module.

Point separation is proved using coordinate ratios. For tangent separation the proof
uses the explicit differential and zero formulas: a vector in its kernel composes to
a morphism factoring through the target residue-field point. Its pullback of every
vanishing coordinate ratio is zero. The basis expansion writes the separating section
as such a ratio times a generating section on a chart. The chart pulls back to the
whole dual-number spectrum, and adjunction uniqueness compares native pullback with
the tensor-pullback unit in the hypothesis, yielding the required contradiction.

The final step follows the shorter existing unramified route: closed-fibre injectivity
and properness imply finiteness, cotangent surjectivity implies unramifiedness, and the
proved finite-unramified one-point criterion yields closed immersions on a target
open cover. The finite-local-stalk and cokernel-support arguments are unnecessary.
The original unit route (generation, projective map, properness/finite fibres,
tangent separation, closed immersion, very ampleness) is preserved.

Added private proof imports for generating sections, invertible stalks, nonvanishing,
closed-point rationality, evaluation of residue-field points, rational unramifiedness,
and the finite-unramified one-point criterion. Updated the declaration's proof
explanation and the node's proof, dependencies and proof origin to match the code.

Validation: the repaired two-module packet is compiled through `lcompile.py --all`
and checked by `deliver3.py` before delivery. There are no
`sorry` tokens in the delivered module. Edge cases do not require nonempty X or a
nonempty coordinate set: the generation and open-cover arguments include empty
schemes, and the zero-dimensional V case is excluded by generation whenever X has
a closed point. No extra nonemptiness or positivity hypothesis was introduced.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.point_tangent_separation_closed_immersion`
(node `lem-sc-point-tangent-separation-closed-immersion`).

Added 0 holes; split off 0 statements. No sorry remains in the assigned module, and
there are no new Lean modules. The existing shared pair theorem and its
native-map comparison remain fully proved; the interface repair adds no hole. This is a proof from existing declarations, including
`cotangent_surjective_of_tangent_injective` and the existing proper-cohomology and
projective-construction APIs; their remaining upstream obligations are unchanged.

## No longer needed

Removed private imports:

- `Sheaf.AlgebraicGeometry.InfiniteClosedPointsInterClosureSingleton`:
  no separate infinitely-many-specializations argument is needed; the proved
  `ClosedFibreSingleton` lemma uses the Jacobson closure argument.
- `Sheaf.RingTheory.SurjectiveOfFiniteOfCotangent`: replaced the finite local-ring
  surjectivity step with the proved unramified and finite one-point criteria.
- `WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed`:
  no cokernel/support reduction is needed in this route.
- `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple` and
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`: redundant direct imports;
  the unchanged public imports already provide these required definitions.

The proof no longer needs nodes
`lem-sc-finite-type-nonclosed-closure-closed-points`,
`lem-sc-point-tangent-finite-local-cotangent-surjective`, or
`lem-weil-pbc-finite-type-module-support-closed`. The node's direct
`def-weil-finite-integral-morphism` reference from the cokernel step is also removed;
finite morphisms remain part of the retained finite-neighbourhood criterion.
Removed only the obsolete support-closed entry from top-level `tool_uses`, retaining
the order of the other existing approvals. No new approval entry was added.

These are dependencies unnecessary for this proof, not requests to delete adopted
source declarations or to withdraw modules still required by other consumers.
No library module is withdrawn in this delivery. The duplicate local pair and
native-map proofs are no longer needed: the existing pair theorem is imported
and reused. This is proof deduplication, not withdrawal of either theorem from
its original module.

## Where the brief, the DAG or earlier work was wrong

The original DAG route is mathematically usable, but its finite-local-stalk and
cokernel-support steps are longer than the now-proved unramified route. The proof
also makes explicit the coordinate and adjunction comparisons hidden by the sentence
“tangent separation makes the differential injective.” The DAG is updated accordingly.
There is no statement or definition dispute and no forced adaptation.

The returned delivery c3cdf37bf2a incorrectly duplicated two private lemmas
already proved in `CompleteLinearSystemClosed`. The current repair removes both
copies, exposes the existing pair theorem in place, and uses it by a private
import. Its original private native-map comparison is retained unchanged.
The corresponding visibility change and consumer checks are recorded in
`coord/changes/R2-generatingSections-pair-public.md`.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
