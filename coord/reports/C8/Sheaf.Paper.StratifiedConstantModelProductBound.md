## What changed

Proved `AlgebraicGeometry.ProEtale.StratifiedConstantModels.exists_stratified_constant_model_product_bound`
from the existing scalar-local-model representative statement, finite quasi-compact
abelian-sheaf detection, and joint-adjunction model embedding. The proof chooses the
families simultaneously and forgets constructibility of the finite strata to form the
required index. Joint zero detection proves that the canonical product lift is monic;
its projection equations are the specified adjunction-unit components.

For the image clause, the proof constructs the actual sectionwise linear ranges of a
monomorphism, transports the sheaf condition along the natural linear bijection, and
lifts that isomorphism through the fully faithful forgetful functor. It constructs the
empty stratification explicitly and proves the empty product zero by its projections.
Public statements and mathematical constructions are retained. `stratumAt` becomes
an abbreviation with its identical body; so does `product`. This lets dependent type
comparisons reduce stratum projections before expanding coefficient-ring constructions.
The generic structural helpers retain predicates abstractly when forgetting
constructibility and packing label tuples into `Index`. This avoids kernel expansion
of pullback coefficient constructions during dependent projection comparisons.
The change record is
`coord/changes/C8-stratumAt-reducibility.md`. A local
`backward.isDefEq.respectTransparency false` elaboration setting and local
irreducibility attributes keep coefficient and sheaf tensor constructions from being
expanded during dependent type comparisons.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.StratifiedConstantModels.exists_stratified_constant_model_product_bound`
(node `lem-sfb-stratified-constant-model-product-bound`). No holes added or split off;
no sorry remains in the delivered module. The existing dependency
`AlgebraicGeometry.ProEtale.proetale_scalar_local_model_representatives` remains a
separate library item. No new dependency theorem is introduced.

## No longer needed

Removed private imports:

- `Sheaf.AlgebraicGeometry.WeaklyEtaleStability`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.Algebra.Module.FinitePresentation`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.CategoryTheory.LocallyPrescribedModulesSmall`
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`

The scalar representative dependency encapsulates the site and local-model smallness
arguments. The broader planned stratum detector is replaced by the proved finite
quasi-compact abelian-sheaf detector used directly. These modules are not withdrawn.

`lem-sfb-small-site-image-subsheaf-representatives`
(`Sheaf.CategoryTheory.SmallSiteImageSubsheafRepresentatives`) is not required by this
proof. Its single-universe interface does not specialize directly to the mixed-universe
pro-etale site. The concrete range proof uses Mathlib's presheaf submodules and works
with these site universes directly. No claim of global unreachability is made.

The declared dependency `lem-sfb-noetherian-stratified-model-product-embedding`
(`Sheaf.Paper.NoetherianStratifiedModelProductEmbedding`) is not needed here.
Applying the joint-adjunction lemma directly takes the exact product of this statement;
it avoids reindexing the supplied families through `LocallyClosedModelDomain` and
transporting a separately selected limit cone. Its finite-detection argument is used
in a private helper with arbitrary coefficients.

The empty-case proof no longer needs `def-weil-pbc-proetale-site` as a proof dependency;
the site remains part of the statement's dependencies. No module is withdrawn.

Removed obsolete direct `tool_uses` entries:

- `sk-lem-pe-weakly-etale-stability`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-sfb-proetale-object-inverse-image-restriction`
- `lem-sfb-locally-prescribed-modules-small`
- `lem-weil-pbc-module-sheaves-limits-sectionwise`
- `lem-weil-pbc-noetherian-stratum-detection`

The entries for locally Noetherian quasi-separatedness, cartesian coefficients and
joint-adjunction embeddings are retained.

## Where the brief, the DAG or earlier work was wrong

The DAG's abstract image-code theorem uses site and coefficient universes all equal,
whereas this item has morphisms in `u` and site objects and sections in `u + 1`.
The sectionwise range argument supplies the stated image clause directly.

The interrupted work was retained. The launcher refreshed `.budget.start` on resume
(original start 1792759233.3171637, refreshed start 1792773449.0892236); no budget
metadata was edited by the worker, and the original assignment deadline is retained.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
