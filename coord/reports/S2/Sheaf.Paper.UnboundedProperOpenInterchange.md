## What changed

Replaced the original anonymous hole in
`AlgebraicGeometry.Etale.unboundedProperOpenInterchange` by a construction and a complete
combination proof. Its signature is unchanged. All writes are in this sandbox; the adopted
`WeilConjectures` source tree is unchanged.

The sheaf comparison is constructed from proper-support composition. The proof of
invertibility of its unbounded derived comparison uses pointwise finite cohomological
dimension and the existing open-extended-injective acyclicity theorem. The argument resolves
an arbitrary K-injective by a termwise-injective K-injective complex and transports the unit
isomorphism along their homotopy equivalence. This avoids module-to-abelian comparison and a
global fibre-dimension bound.

The right-derived universal property constructs the derived natural isomorphism and proves
its normalization on every homotopy object. A separate proved abstract calculation derives
the requested formula for every K-injective representative and every replacement map.
The normalization uniquely determines the natural transformation by right-derived uniqueness.
A private generic record stores the constructed derived isomorphism and its proved unit and
representative normalizations. Its constructor builds the right-derived natural isomorphism
directly. The final proof reads these fields and combines the normalized families with the
separate coherence results. The resolution argument first obtains an abstract complex with
injective terms, avoiding repeated unfolding of the functorial resolution's construction.

Added the five new modules listed below. The composition module proves vertical pasting
from support normalization and unit normalization, identifying the adjunction-defined
geometric compositors with the universal-property compositors. The pasting module proves
both identity clauses by monic support inclusions and right-derived uniqueness. The other
three modules isolate separate source results, with complete natural-language proofs.

The entire sandbox is checked through `lcompile.py --all`; each file uses the normal
60-second server limit. No library build, source-library mutation, or consumer adaptation
is included. The final delivery command performs the required independent mechanical checks.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Etale.unboundedProperOpenInterchange`
(node `lem-amb-unbounded-proper-open-interchange`). There are zero holes in the item module.
This is a decomposition, not a net hole reduction: one original hole is closed and three
strictly smaller source obligations are added. Each assumes already constructed normalized
families and establishes only one independent coherence result; none asserts their existence
or repackages the entire original conclusion.

Also proved, without local holes:

- `AlgebraicGeometry.Etale.unboundedProperOpenComposition_of_normalization`: vertical
  composition is proved; horizontal composition comes from the separate Tag 0F7D lemma.
- `AlgebraicGeometry.Etale.unboundedProperOpenPasting_of_normalization`: the composition
  clauses and both identity normalizations; the identity arguments are proved here.
- Private helpers `exists_sheafComparison`, `exists_termwise_injective_resolution`,
  `derivedUnit_of_termwise_injective_resolution`,
  `openExtension_derivedUnit_isIso`, `comparison_representative`, `constructedDerivedComparison`,
  together with the composition and identity
  calculations in the new modules.

Every remaining `sorry` introduced by this delivery:

- `AlgebraicGeometry.Etale.unboundedProperOpenAdjunctionNormalization_of_normalization`,
  node `lem-amb-unbounded-proper-open-adjunction-normalization`, Stacks Tag 0F7B(b):
  identify the specified exact exchange with the inverse adjunct of the normalized comparison.
- `AlgebraicGeometry.Etale.unboundedProperOpenHorizontalComposition_of_normalization`,
  node `lem-amb-unbounded-proper-open-horizontal-composition`, Stacks Tag 0F7D:
  horizontal pasting with the specified descended open-extension compositors.
- `AlgebraicGeometry.Etale.unboundedProperOpenBaseChange_of_normalization`,
  node `lem-amb-unbounded-proper-open-base-change`, Stacks Tag 0F7F:
  the arbitrary cartesian-face cube identity with the specified exchange maps.

The packet therefore has three holes, all named public theorems with proof body exactly
`by sorry`. There are no axioms, private holes, or holes in definitions. The remaining
obligations do not cancel arbitrary exchange maps and do not assume inverse image preserves
K-injectives. Empty opens, the zero coefficient ring, identity squares, noncartesian main
squares, and unbounded representatives preserve all stated hypotheses and equations.

## No longer needed

The item no longer imports the following modules (new statement modules also omit these
old proof imports):

- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`
- `Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex`
- `Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound`
- `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChangeUnderivedCompatibility`
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`
- `WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.BaseChange.Square`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`

The proof uses the existing pointwise finite-cd source API instead of the planned global
finite-cd route. The following former approved tool uses are removed from the item node;
these are pruned from this proof route, not withdrawn or deleted from the shared library:

- `lem-fin-finite-type-fibre-dimension-bound`
- `lem-kun-finite-cd-acyclic-complex`
- `lem-kun-proper-torsion-cd-bound`
- `lem-weil-pbc-affine-scheme-qcqs`
- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-module-abelian-derived-direct-image-comparison`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-open-immersion-base-change`
- `lem-weil-pbc-proper-base-change`

In particular, the global fibre-dimension bound, the global proper torsion bound, and the
forgotten-module derived comparison are not needed by the constructed interchange. Public
imports of the original item are preserved. No source-library declaration is removed and no
module is withdrawn. The separate coherence nodes retain all the dependencies their own
source arguments need. No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found and no target or definition was weakened. The DAG's global
cohomological-dimension construction was a longer route than the already proved pointwise
source theorem and conservativity of geometric inverse images. Its replacement is recorded
in the item node and the docstring.

The bounded-below proper/open coherence modules do not establish the unbounded clauses.
They supplied useful proof patterns for vertical pasting and the identity calculations, but
are not imported. The three retained obligations are precisely separate source lemmas; their
proofs still require the canonical-map calculations, not merely invertibility of abstract
functors. There is no rework entry or requested definition repair for this item.

## New nodes

`lem-amb-unbounded-proper-open-adjunction-normalization`, module
`Sheaf.AlgebraicGeometry.UnboundedProperOpenAdjunctionNormalization`, is the cartesian
adjunction-normalization part of Stacks Tag 0F7B(b), for already normalized families.

`lem-amb-unbounded-proper-open-horizontal-composition`, module
`Sheaf.AlgebraicGeometry.UnboundedProperOpenHorizontalComposition`, is Stacks Tag 0F7D
for the same unit-normalized families, with exactly the specified open compositors.

`lem-amb-unbounded-proper-open-composition`, module
`Sheaf.AlgebraicGeometry.UnboundedProperOpenComposition`, proves vertical composition and
combines it with the preceding horizontal result. Its vertical argument is complete Lean.

`lem-amb-unbounded-proper-open-pasting`, module
`Sheaf.AlgebraicGeometry.UnboundedProperOpenPasting`, combines composition with two proved
identity clauses. Its statement and proof use unit normalization on homotopy objects.

`lem-amb-unbounded-proper-open-base-change`, module
`Sheaf.AlgebraicGeometry.UnboundedProperOpenBaseChange`, is Stacks Tag 0F7F for already
normalized families. All five nodes inherit chapter `sec-smooth-purity` and unit `sk-prop-an`.
Their records include the Lean signatures, source proofs, and Mathlib searches by LeanSearch,
LeanFinder/Loogle, and source grep. The first preflight required adding the distinct LeanSearch
kind; Loogle and LeanFinder together did not satisfy that requirement.
The change record `coord/changes/unbounded-proper-open-proof-context.md` documents the
added elaboration-context commands that preflight classifies as visible changes. Its consumer
inventory lists the complete downstream import scan and current holders. No existing
definition, public statement, or public import is changed, and no consumer is adapted.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
