## What changed

Proved `AlgebraicGeometry.Etale.isIso_etaleSumExtensionTensorComparison` without changing its
statement or either canonical comparison definition. The proof transports the source-library
etale derived projection formula to exact termwise inverse image; the counit equation follows
from naturality and the right triangle identity. All helpers are private and proved.

Pruned unused imports and updated the node proof to this shorter route. Added an attachment
node for the already proved source theorem, without adding a Lean module or any assumption.
Change record: `coord/changes/etale-sum-extension-tensor-prune.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_etaleSumExtensionTensorComparison`
(node `lem-asd-etale-sum-extension-tensor`). Added 0 holes; split off 0 holes; 0 `sorry` remain
in the item or any delivered file. Both original definitions remain constructed and unchanged.
The source theorem used is already proved; no pending Sheaf theorem supplies this proof.

Validation: the final item compiled without warnings (9.0 seconds). The delivery dry run
passed compilation, axiom probing and static preflight (CODEX review required for the import
pruning and attachment node). Both direct consumers were compiled against the new module in
an isolated overlay: TensorMateEtalePrecomp passed in 42.3 seconds; EtaleRhoMonoidalMate passed
in 13.1 seconds with diagnostic profiling. Earlier timeouts prompted a comparison with the
unchanged Rho baseline (53.6 seconds); profiling showed only 1.5 seconds of elaboration and
1.75 seconds of instance search, with no new unresolved goal. The final unprofiled Rho check also passed in 17.5 seconds. No consumer source is changed. Original public signatures and both
definition bodies were also checked byte-for-byte against the shared source.

## No longer needed

The old explicit K-flat resolution, totalization, generator calculation and two-variable descent
are supplied internally by the existing source projection theorem. They are not repeated here.
The following direct imports are removed (this does not assert global unreachability):

- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `Sheaf.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.AlgebraicGeometry.Scheme`
- `Mathlib.RingTheory.Noetherian.Defs`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
- `Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Paper.EtaleSumTensorTotalization`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`

All 18 former proof-dependency edges are replaced by the proved source attachment:

- `def-kun-derived-tensor`
- `def-pc-tensor-complex-sheaves`
- `def-weil-pbc-etale-sum-extension`
- `def-weil-pbc-sheafification`
- `lem-pc-kflat-resolution`
- `lem-pc-sites-sheaf-tensor-bilinear-universal`
- `lem-pur-cochain-pullback-tensor-coherence`
- `lem-pur-etale-sum-flat-kflat`
- `lem-pur-etale-sum-tensor-totalization`
- `lem-pur-kflat-total-tensor-model`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-etale-restriction-injectives`
- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-weil-pbc-localization-universal-property`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `prop-weil-pbc-inverse-image-modules-exact`

The old top-level `tool_uses` entries are withdrawn because this proof no longer directly invokes
those statements. Statement dependencies remain unchanged: the statement retains all its
original notions, canonical maps and fold counit. No module is withdrawn from the repository.

## Where the brief, the DAG or earlier work was wrong

The old plan is mathematically valid, but duplicates a projection formula already proved in
`WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect`. Monoidal transport and
projection/internal-hom conjugacy allow its use with the exact derived adjunction in the item;
the counit compatibility is then formal. No statement dispute or weakened conclusion occurs.
The unit has no bound realized statement or proof steps, so no unit-level route is bypassed.
The interrupted scratch work's experimental holes were removed, not delivered.

## New nodes

`lem-pur-source-etale-derived-projection` attaches the existing proved
`AlgebraicGeometry.Etale.isIso_projectionMap_derivedEtaleLowerShriek` in SitePerfect. Its source
proof uses K-flat resolution, the cochain projection formula and naturality. Mathlib semantic,
name and textual searches did not find this etale theorem; blueprint/DAG searches found no
existing attachment for this exact source declaration. It is a generalization of the
invertibility part used here, not a renamed copy of the assigned theorem, and creates no hole.

The launcher clock metadata changed across interrupted attempts (previously saved start
1792426803.0886858, resumed start 1792437943.0889897). The worker did not modify `.budget` or
use that reset to defer proof work; this delivery has a complete proof and no split-off holes.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
