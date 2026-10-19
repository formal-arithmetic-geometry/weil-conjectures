## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientHeart_essentiallySmall` in
`Sheaf.Paper.CoefficientHeartSmall`, preserving its full signature and all four public imports.
The proof works directly with internal modules and finite presentations. Private, proved
helpers show that small local model families and jointly monomorphism-reflecting left
adjoints give essential smallness by embedding objects into products of right-adjoint images.
Mathlib well-poweredness bounds their subobjects. Apply this first over covers, then over
finite stratifications. The qcqs branch identifies the desired constructible property.

The cover argument uses existing abelian localization and conservativity. The stratum
argument uses the proved private `abDetectMaps` via `import all
Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport`, and the canonical underlying-sheaf
comparison `profinitePointModuleForgetPullbackIso`. This preserves the unit's finite
stratification, small local data, and small gluing-data argument. It replaces explicit
matrix descent by the equivalent subobject bound already used by the reviewed DAG plan.
No definitions, public signatures, or consumer modules were changed. The file-scope universe
and open-command additions are documented with their complete consumer inventory in
`coord/changes/coefficient-heart-small-proof-scope.md`, as required by the delivery gate. The new DAG copy
records the actual proof. Its obsolete four `tool_uses` approvals are withdrawn; the new
uses of the point comparison and joint abelian detection are generic infrastructure tools.

Validation: the resumed worker checked this sandbox against the current source and
recompiled the single file through lcompile.py on 2026-10-19: it passed cleanly in
3.7 seconds. The public theorem signature is textually identical to the current source;
the DAG's proof dependencies equal the union of its seven steps' uses. The delivery gate
supplies the axiom probe. Empty X and empty strata are covered by joint detection for an empty jointly
surjective family. Rank zero is covered by the zero-rank finite-free presentations. Cover
indices need not be finite: they have the fixed small universe, and products are obtained
by shrinking the Grothendieck category's limits. No arbitrary data is selected from an
unproved mere-existence theorem: representative families use proved Mathlib smallness;
cokernels and products are canonical categorical constructions.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.coefficientHeart_essentiallySmall`
(node `det-lem-coefficient-heart-small`). Added 0 holes; split off 0 statements.
There are 0 `sorry`s left in the delivered module and no other delivered Lean modules.
This proves the item from existing library declarations; their transitive unfinished
proofs are unchanged. Every private helper in this file is proved.

## No longer needed

Removed proof imports:

- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.SheafTensor`
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`
- `WeilConjectures.CategoryTheory.ModuleObjects.Free`
- `Mathlib.LinearAlgebra.Basis.VectorSpace`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Sheaf.Paper.LatticeSheafBasic`
- `Sheaf.Paper.CoefficientHeartCommonStratification`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal`
- `Sheaf.Paper.CartesianCoefficients`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`

The proof no longer uses the following original declared proof dependencies:

- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`
- `def-weil-sheaf-of-modules-category`
- `sk-def-sfb-sheaf-tensor`
- `def-constructible-stratification`
- `def-sfb-padic-subfield-condensed-ring`
- `sk-def-sfb-qlbar-condensed`
- `lem-weil-pbc-vector-space-free`
- `def-weil-pbc-sheafification`
- `lem-weil-pbc-lattice-free-scalar-extension`
- `det-lem-coefficient-heart-common-stratification`
- `lem-weil-proetale-weakly-etale-localization`
- `sk-prop-sfb-cartesian-coefficients`
- `def-weil-pbc-sites-and-cohomology`

Internal/sectionwise-module equivalence and the separate sheaf-tensor API are unnecessary
because the proof stays in the existing internal-module category. Vector-space bases,
field identification, scalar extension of free lattices, and sheafification of coordinate
maps are unnecessary because all finite presentations are already a small family. Explicit
weakly-etale localization and site-covering-axiom interfaces are replaced by the proved
source localization/conservativity API. Common-refinement and lisse-preservation are
unnecessary: work with the given stratification and detect zero maps by its actual
immersions. All four old top-level tool approvals (internal equivalence, lattice-free
extension, weakly-etale localization, cartesian coefficients) are removed as obsolete.
These are dependencies pruned from this item's route; no claim is made that every removed
module is now globally unreachable from every target.

The earlier sandbox's SmallnessScratch was moved outside lean/ into scratch/; it is not a
library module and is not delivered. No existing library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox node incorrectly claimed the theorem follows from
`essentiallySmallSelf`. Its own ambient object universe is u+2, whereas the required bound
is u+1, so that argument does not apply. It has been replaced by the actual finite-model
and subobject proof. The earlier Lean attempt had a named-universe argument error, an
incorrect conditional rewrite, misplaced theorem documentation, and a conjunction
projection error. These are repaired.

Its conversion from Scheme.Stratification to FiniteLocallyClosedStratification caused a
kernel deterministic timeout through expansion of pulled-back coefficient structures.
The final proof uses the existing finite joint-detection API for the actual immersions,
so the conversion is unnecessary. There is no timeout increase or file split.

The statement, unit route, and actual condensed coefficients remain unchanged. The proof
shows that field-specific reduction to finite free models is unnecessary for smallness:
smallness of finite presentations suffices even over a general commutative condensed ring.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
