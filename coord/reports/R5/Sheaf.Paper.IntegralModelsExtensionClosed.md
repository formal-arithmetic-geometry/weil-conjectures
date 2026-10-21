## What changed

`Sheaf.Paper.IntegralModelsExtensionClosed` now has a complete proof of
`AlgebraicGeometry.ProEtale.integralModels_extension_closed` from the stated dependencies
and the new slice-model comparison below. All existing public statements and definitions
are unchanged. No source-library file is changed.

The denominator hypothesis already supplies the integral short exact numerator and its
scalar-extended short exact sequence. The proof uses those witnesses directly. A private
sectionwise calculation makes multiplication by a nonzero constant an automorphism.
A second private argument twists the rational inclusion by the inverse automorphism,
uses naturality of `extClass`, and applies the injective direction of
`ext_one_extension_classification` to identify the middle objects. The uniformizer is
proved nonzero from the recorded DVR facts.

For constructibility of the integral middle object, an exact equivalence carries its
short exact sequence to a distinguished degree-zero triangle. The complete category is
triangulated, so its middle object lies in the category. The reverse constructibility
comparison gives the desired integral model.

`Sheaf.Paper.ContinuousIntegralConstructibleComparison` proves
`AlgebraicGeometry.ProEtale.continuousIntegralConstructibleComparison`. It explicitly
converts covering families to covering sieves using `overMap` and `overFunctorMap`, and
converts a covering sieve back to its family of arrows. It then uses the existing
stratified-perfect characterization and the degree-zero single/homology isomorphism.
Zero homology outside degree zero, and the zero-model case, are proved explicitly.

`Sheaf.Paper.ContinuousIntegralCoefficientComparison` proves
`AlgebraicGeometry.ProEtale.continuousIntegralCoefficientComparison`. Restricting the
WithAbs equivalence to valuation subrings gives an isometry and an isomorphism of
continuous-function sheaves. The normalized quotient equivalences identify the finite
coefficient towers. Their limit, the actual completion comparison, and the normalized
continuous coefficient completion give the coefficient-sheaf isomorphism. The proof
checks its constant-scalar square after every finite projection, using the constant-sheaf
adjunction and pointwise residue formulas. This result needs no geometric hypotheses.

`Sheaf.Paper.ContinuousIntegralSliceModelComparison` isolates the remaining comparison
of ordinary finite scalar models on one slice after an immersion. Its statement has no
Ext groups, short exact sequences, finite stratifications, derived categories, dimension
bound, or invertibility assumption. Its complete source-based proof is in the docstring
and DAG. It includes torsion and zero finite presentations. It takes the normalized
ring and coefficient-sheaf isomorphisms as inputs; the module equivalence used in the
statement is explicitly restriction along the given coefficient isomorphism. Thus the
remaining hole contains no existential choice of a module equivalence.

The four delivered modules compile together through `lcompile.py --all`. The target
statement has not changed, and no public definition takes data from an unproved theorem.
All new private constructions are built explicitly from the recorded normalized maps.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.integralModels_extension_closed` (node
`lem-weil-pbc-integral-models-extension-closed`). The assigned module has zero remaining
`sorry` occurrences.

Added and proved
`AlgebraicGeometry.ProEtale.continuousIntegralConstructibleComparison` (node
`lem-weil-pbc-continuous-integral-constructible-comparison`), including its covering and
homology arguments. Also added and proved
`AlgebraicGeometry.ProEtale.continuousIntegralCoefficientComparison` (node
`lem-weil-pbc-continuous-integral-coefficient-comparison`), including its scalar
normalization. All private helpers in the delivered modules are proved.

One new hole remains:
`AlgebraicGeometry.ProEtale.continuousIntegralSliceModelComparison`, in its own module and
node `lem-weil-pbc-continuous-integral-slice-model-comparison`. Its proof is exactly
`by sorry`. The unresolved part is the coherent transport of constant scalar tensor
models across the continuous/completed coefficient isomorphism and immersion pullback
on each slice. This is a genuine coefficient-presentation result, not an integral-model
existence statement or a repackaged extension-closure hypothesis.

Thus this is a decomposition: one original hole closed, one lower hole added, net zero
holes closed. It is not claimed as an unconditional proof with only the three standard
axioms. The already existing unfinished dependencies of the stratified characterization
are unchanged.

## No longer needed

Removed the assigned module's proof imports
`Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction` and
`Sheaf.CategoryTheory.ScalarLocalizationSheafExact`. Scalar localization exactness is
unnecessary for this proof because `_hsurj` already supplies the extended short exact
sequence. The original public imports and file-level universe header are preserved.
The dependency `lem-weil-pbc-scalar-localization-sheaf-exact` is removed from
the item's `proof_deps`.

`def-weil-pbc-module-localization-away` is unnecessary in the proof: the unchanged Lean
hypothesis already expands the denominator and numerator representatives. It is removed
from `proof_deps`; its historical statement-dependency entry is preserved.

The continuous coefficient immersion-restriction theorem is unnecessary as a direct
import of the assigned module, but remains a mathematical dependency of the new
slice-model comparison. It is not globally withdrawn. The integral stratified-perfect
characterization remains needed through the proved constructibility comparison; its
proof import moves there. The Mathlib short-exact single triangle and the injective
Ext-one classification remain needed.

No existing module or declaration is deleted. No source-library declaration is pruned.
The three new comparison modules are the only new modules needed by the final proof.

## Where the brief, the DAG or earlier work was wrong

The plan's first three steps reconstruct numerator representatives and exact scalar
extension that are already explicit in `_hsurj`; this duplication is unnecessary.

The plan's constructibility step identified the continuous local models with the
completed models in prose. These are distinct Lean coefficient presentations, with
different ULift placements and a coefficient change after immersion pullback. They are
not definitionally equal. The new slice-model theorem records precisely this missing
comparison, while the covering-family/sieve conversion and the degree-zero derived
argument are proved here. No statement is disputed or weakened.

The unit route is preserved: the argument still uses the integral stratified-perfect
characterization for constructibility and Ext-one classification for the denominator
argument. The local paper was checked at Definition 6.8.10, Proposition 6.8.11(3),
Lemma 6.5.8(1), and the final paragraph of Lemma 6.8.13. Edge cases considered were empty
schemes and slices, zero endpoints, zero extension classes, exponent zero, and torsion
finitely presented integral modules.

## New nodes

`lem-weil-pbc-continuous-integral-constructible-comparison`: the proved comparison between
continuous constructibility and membership of the degree-zero object in the completed
constructible category. Its proof combines the slice comparison, covering-sieve
arguments, and the existing characterization.

`lem-weil-pbc-continuous-integral-slice-model-comparison`: the remaining ordinary
coefficient/pullback/tensor model comparison on a single slice. It is strictly below the
assigned extension argument and has its own complete natural-language proof and source.

`lem-weil-pbc-continuous-integral-coefficient-comparison`: the proved isomorphism of
continuous and completed coefficient sheaves, normalized on the actual constant scalar
map. The remaining slice theorem uses this normalization as its explicit hypothesis.

No new node changes a definition or an existing statement, so no statement-change
record or consumer adaptation is needed. The existing item's proof fields are updated
to match the implemented route.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
