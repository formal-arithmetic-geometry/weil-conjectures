## What changed

Proved `AlgebraicGeometry.Scheme.finiteLocalSystemsType` with its existing signature unchanged. The proof chooses representative labels on the given trivializing cover, descends them through Mathlib's fpqc sheaf of continuous maps to the discrete label type, constructs the clopen fibres, and restricts the original covering to each fibre. Empty members are handled by proving every module sheaf on their slice is zero.

Three supporting results are fully proved. `finiteLocalSystemsType_coproduct` glues morphisms along the disjoint open cover, without a smallness hypothesis on the arbitrary index type R. `proEtaleConstantModule_restrict` restricts the module-sheafification unit along `Over.map`, transposes it on the smaller slice, and proves invertibility after forgetting to additive sheaves. `proEtaleConstantModule_model_rigidity` recovers both coefficient modules as the fibre of the same module sheaf at a geometric point of the overlap. Scalar restriction constructs a fixed-coefficient module sheaf, so the resulting fibre isomorphisms are linear. This reuses the existing geometricPoint construction in ProEtaleFiniteModelStalks via a proof-only `import all`.

The independent coefficient universe is handled by Mathlib's `preservesFilteredColimitsOfSize_shrink` and an explicit application of its concrete additive sheafification instance. No coefficient-size hypothesis was added. All existing public imports and theorem signatures are unchanged. The DAG proof and proof_deps follow the actual descent, geometric-fibre and restriction route.

Validation: `lcompile.py --all` compiled all three delivery modules without errors or warnings (rigidity 12.5 s, restriction reused its compiled artifact, main theorem 4.2 s). A resumed `lcompile.py --all` also passed for the retained files. Text comparison confirms the assigned theorem signature is unchanged; every Lean line is at most 100 characters. The resumed axiom probe compiled in 1.8 s: the coproduct theorem uses only `propext`, `Classical.choice` and `Quot.sound`; the main theorem, restriction and rigidity additionally reach `sorryAx` through existing named library obligations. No new axiom or hole was introduced.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.finiteLocalSystemsType` (node `det-pe-finite-local-systems-type`). Added zero holes; no sorry remains anywhere in the three delivery modules.

Also fully proved:

- `AlgebraicGeometry.Scheme.finiteLocalSystemsType_coproduct` (node `det-pe-finite-local-systems-type-coproduct`);
- `AlgebraicGeometry.Scheme.proEtaleConstantModule_restrict` (node `lem-pe-constant-module-restriction-universes`);
- `AlgebraicGeometry.Scheme.proEtaleConstantModule_model_rigidity` (node `lem-pe-constant-module-model-rigidity-universes`).

There are no holed definitions or private holed declarations. Existing named proof dependencies in the library retain their own proof obligations; this delivery does not claim that their transitive closure is axiom-free.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections`, `Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf`, `Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable`, `Sheaf.AlgebraicGeometry.ProEtaleFiniteConstantHom`, `Sheaf.CategoryTheory.SiteCoveringAxioms`, `Mathlib.AlgebraicGeometry.Sites.Fpqc`, and `Mathlib.AlgebraicGeometry.Limits`. The last two are already available through retained public imports. Added proof imports of the two helper modules, Mathlib's scheme continuous-map sheaf, and the source library's pro-etale empty-cover theorem.

The implemented proof no longer uses nodes `def-weil-pbc-site-comparison-morphism`, `lem-weil-pbc-constant-sheaf-maps-global-sections`, `lem-cbc-comparison-pullback-sections`, `lem-weil-pbc-sets-etale-inverse-image-constant-sheaf`, `lem-galois-constant-sheaf-sets-representable`, `det-pe-finite-local-systems-hom`, `def-weil-pbc-sites-and-cohomology`, or `lem-weil-pbc-scheme-coproduct-family`. Direct fpqc continuous-map descent replaces the etale/pro-etale comparison route for label descent. Geometric fibres replace finite Hom comparison in rigidity. Direct gluing replaces the scheme-coproduct existence theorem and also covers large label types. Removed the obsolete corresponding tool_uses approvals from the node copy. These are dependencies pruned from this argument; other parents may still need their modules.

## Where the brief, the DAG or earlier work was wrong

The retained sandbox report described one outstanding rigidity hole. That obligation is now proved. The initial dry run rejected its proposed split as too early; no split is now proposed. A later dry run required LeanSearch in addition to Loogle/LeanFinder and source grep for each new node; the missing searches have now been run and their results recorded.

The original eight-step plan mixes coefficient universes: `finiteConstantHom_constant` works in the tied universe t+1, while the assigned statement allows an independent coefficient universe. Geometric fibres give the needed rigidity without finite presentation, and the universe-polymorphic scalar/sheaf bridge is fully formalized here. The scheme coproduct exists for this particular decomposition even when the label type is not Small; direct gluing avoids adding that hypothesis. The existing `AlgebraicGeometry.Scheme.proEtale_model_type_opens` in `ProEtaleModelTypePartition` was also checked: it treats fixed-coefficient `ModuleCat`-valued sheaves in the tied universe t+1, whereas this item uses intrinsic modules over the constant ring sheaf and an independent coefficient universe. Its geometric-point construction is reused through `ProEtaleFiniteModelStalks`; scalar restriction and the universe-polymorphic fibre comparison supply the missing bridge here. No unit statement or unit-level proof step is bypassed: this item still constructs the model-type decomposition required in the finite-local-systems unit.

## New nodes

`lem-pe-constant-module-restriction-universes`: proved restriction of a localized constant model along an arbitrary pro-etale slice arrow, preserving the original model.

`lem-pe-constant-module-model-rigidity-universes`: proved recovery of an isomorphism of coefficient modules from two local trivializations and a pair of overlap points. Its proof constructs scalar restriction and the sheafification-unit fibre comparison and reuses the existing geometric-point construction. The empty case cannot supply the required overlap points; arbitrary module models and independent coefficient sizes are allowed.

`det-pe-finite-local-systems-type-coproduct`: proved the coproduct universal property of an arbitrary indexed clopen decomposition, including empty pieces and unrestricted index universe. No existing definition or statement was changed, so no change record is needed.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
