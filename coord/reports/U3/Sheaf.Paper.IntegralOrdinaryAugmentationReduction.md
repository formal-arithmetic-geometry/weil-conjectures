## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.integral_ordinary_augmentation_reduction`
by a proof using the source principal-reduction product comparison, successor lifts,
and Milnor pro-isomorphism criterion. The original signature and public imports are
unchanged. The added proof imports are `Sheaf.Paper.IntegralOrdinaryAugmentationMilnor` and
`Sheaf.CategoryTheory.PrincipalMilnorAugmentationReduction`. The latter states and
proves the general principal Milnor reduction criterion over an arbitrary site.
No existing module besides the assigned item is changed. The new presentation module
publicly imports only the principal tower definitions; the proved criterion imports
`Complete.Reduction`.

The proof tensors both limiting product fans by the first principal quotient, proves
by product extensionality that the tower shifts and product map commute with this
functor, and transports both distinguished triangles. It then uses the existing
`DerivedCategory.exists_lift_whiskerRight_derivedCompletionCone` to supply both
successor identities. Both squares for the actual augmentation are verified after
reduction, including the boundary square and the shift comparison. The source
`CategoryTheory.Pretriangulated.isIso_of_proIso` proves invertibility. Finally the
canonical coefficient isomorphism between the quotients by I^1 and I identifies this
reduction functor with exactly `DerivedCategory.reductionModIdeal` by naturality.

The one remaining step is an **unreduced** normalized Milnor presentation. It asserts
no invertibility and mentions no reduction of the augmentation. It supplies the
ordinary quotient-to-principal-tower comparison, the two Milnor triangles, and the
normalization of both squares. Its source, full argument in words, and explicit
statement are in the new module and node. Thus the Milnor/tensor/pro-isomorphism
argument is proved rather than restated as another isomorphism obligation.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.ProEtale.integral_ordinary_augmentation_reduction`
(`lem-sfb-integral-ordinary-augmentation-reduction`). There are zero holes in the
assigned module. The private primality/nonzerodivisor helper is also proved.
`DerivedCategory.isIso_reductionModIdeal_of_principalMilnorMorphism`
(`lem-sfb-principal-milnor-augmentation-reduction`) is a proved new theorem with no
hole; it isolates the reduction argument over an arbitrary site.

New hole added:
`AlgebraicGeometry.ProEtale.integral_ordinary_augmentation_milnor`
(`lem-sfb-integral-ordinary-augmentation-milnor`), the whole proof of the sole public
theorem in its new module. Exactly one hole is added and one is closed. This is a
decomposition, with zero net hole reduction, not a claim of an axiom-free proof of
the original theorem. No data definition is selected from the new theorem: its
existential data are eliminated only inside a theorem proof. All three modules
compiled together through `lcompile.py --all`. The concrete tensor proof was
optimized using the source bundled tensor instances and a proved private exact-functor
lemma; development profiling options were removed before delivery.

## No longer needed

No module is withdrawn and no original import is removed. No source declaration
or unit route is pruned. The original exact-products and normalized strict-Roos
dependencies are needed by the remaining unreduced presentation; they move under
its node rather than disappearing. The product comparison, successor lifts, and
Milnor pro-isomorphism criterion remain dependencies of the proved general lemma
and are used in Lean.
The original strict-augmentation and interface imports still supply the statement
and its actual constructed map.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The planned argument separates into an unreduced
normalization and a reduced pro-isomorphism argument. The latter uses the existing
source declarations directly. The proof does not infer equality of derived-limit
maps from their level projections; the unreduced presentation expressly retains
the boundary square, and the proof checks its image using shift naturality.

The source principal tower starts at exponent zero, while the ordinary presentation
starts at exponent one. The remaining presentation explicitly inserts the initial
zero quotient, and its documented proof identifies the signed Roos coordinates
under this insertion. This permits use of the source successor lifts at their
original indices. Zero complexes and the empty scheme require no extra hypothesis.

## New nodes

`lem-sfb-integral-ordinary-augmentation-milnor`, in
`dag/nodes/sec-six-functors-basics/`, records the unreduced regular-quotient Milnor
presentation with both squares for the specified ordinary augmentation. Its module
is `Sheaf.Paper.IntegralOrdinaryAugmentationMilnor`. Its source is Stacks 099M and
0940/0941; LeanSearch, LeanFinder, Loogle and grep searches found the generic
triangle/product tools, but no theorem identifying this augmented quotient limit.
The original node's proof, proof dependencies and proof origin now follow the Lean
argument. No change record is needed: no existing public interface is changed.

`lem-sfb-principal-milnor-augmentation-reduction` records the proved general criterion
in `Sheaf.CategoryTheory.PrincipalMilnorAugmentationReduction`. It combines the
existing source product comparison, successor lifts and Milnor pro-isomorphism
criterion, retaining both squares for the given map. It has no ordinary quotient
normalization hypothesis beyond those squares, and no new hole. Its separate module
keeps the tensor structures in the source's general site context.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
