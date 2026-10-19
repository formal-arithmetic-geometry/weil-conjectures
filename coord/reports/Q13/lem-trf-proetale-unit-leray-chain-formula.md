## Worker report

Repair of return L at immutable head `3d3dc164808d` (H4, with H3 consequence).
The saved packet was inspected and the prescribed initial `deliver2.py --no-push`
was started before editing. This repair keeps the theorem and all previously accepted
orientations and hypotheses, and replaces the different adjunction identified by review.
The delivery is `lean/Sheaf/AlgebraicGeometry/ProEtaleUnitLerayChainFormula.lean`.
The sole postponed theorem is
`AlgebraicGeometry.Scheme.proEtale_unit_leray_chain_formula`.

The private `proEtaleUnitLerayPushforward` and `proEtaleUnitLerayAdjunction` are deleted.
The statement now uses exactly `proEtaleConstantRingPullback A h`,
`proEtaleConstantRingPushforward A h`, `proEtaleConstantRingAdjunction A h`, and
`proEtaleConstantRingDerivedPullback A h` from the dependency's recorded module
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`. Both e and eta_h use that
same adjunction. No extra assumption or comparison equality is required from callers.

The terminal iso has real data. `proEtaleUnitLerayDirectImageIso` identifies the
recorded pushforward with the already published `proEtaleConstantModuleDirectImage`:
the coefficient comparison is the adjunct of rho, and taking its adjunct back gives
rho by `Equiv.apply_symm_apply`. It is therefore equality of the actual sectionwise
pushforward constructions, not an arbitrary right-adjoint isomorphism.
`proEtaleUnitLerayTerminalIso` then uses the published
`sfIntrinsicDirectImageComparison h A`, uniquely normalized on scalar-unit sections,
and the realization equivalence's actual counit and unit. Its last step is
`proEtaleUnitLerayFixedTerminalIso`, evaluating base change at the terminal object
with `PreservesTerminal.iso (proEtaleBaseChange h)`, i.e. X times_Y Y = X.
`proEtaleUnitLerayIso` is `Functor.rightDerivedFunctorCompIso'` of the recorded
pushforward and this terminal iso. No private adjunction is introduced along this path.

Clause-by-clause reading of the unchanged node statement:

- The arbitrary scheme morphism is `{X Y : Scheme.{u}} (h : X ⟶ Y)`.
  There are no properness, nonemptiness or other geometric assumptions.
- The finite commutative ring is `(A : Type u) [CommRing A] [Finite A]`.
  No nonzero or characteristic assumption is added.
- The small sites are `ProEt.topology X` and `ProEt.topology Y`, whose object
  universe is u+1 and morphism universe u; no universe equality is imposed.
- A_T and its modules are `proEtaleConstantRing T A` and
  `proEtaleRingModules T (proEtaleConstantRing T A)`.
  The operations use `proEtaleConstantRingComparison h A`, the isomorphism of
  the specified constant-section coefficient map, exactly as the dependency records.
- h^* and h_* are `proEtaleConstantRingPullback A h` and
  `proEtaleConstantRingPushforward A h`. Their module adjunction is
  `proEtaleConstantRingAdjunction A h`, normalized on the tensor-unit sections.
  Exactness is the recorded `proEtaleRingModulePullback_preservesFiniteLimits`
  and `proEtaleRingModulePullback_preservesFiniteColimits`.
- Lh^* is `proEtaleConstantRingDerivedPullback A h`, definitionally the exact
  termwise `mapDerivedCategory` of this same h^*. Rh_* is the same h_*'s
  `rightDerivedFunctor` via all-module K-injective resolutions.
- Gamma_T is `proEtaleUnitLeraySections A T`, the published canonical realization
  inverse followed by `Sheaf.Γ`. Its codomain is
  `ModuleCat.{u+1} (ULift.{u+1,u} A)`, the common coefficient lift accepted in
  the return; this preserves all A-modules and maps. Its source is the recorded
  intrinsic module category, and no new coefficient category is defined.
- RGamma is `rightDerivedFunctor`, with its canonical K-injective evaluation;
  `DerivedCategory.Q` is localization at quasi-isomorphisms.
- I and J are `CochainComplex ... ℤ`, with `[I.IsKInjective] [J.IsKInjective]`.
  They are unbounded and need not be termwise injective.
- j is any map from
  `((proEtaleConstantRingPullback A h).mapHomologicalComplex (.up ℤ)).obj I`
  to J, with no `QuasiIso` or `IsIso` assumption.
- a_I and a_J are `rightDerivedFunctorObjQIso I` and `... J`, with hom from
  RGamma(Q I) to Q(Gamma I). c_I is
  `(proEtaleConstantRingPullback A h).mapDerivedCategoryFactors.hom.app I`,
  oriented from Lh^*(Q I) to Q(h^* I).
- e is `proEtaleUnitLeraySectionUnit A h`: sections of the recorded module
  adjunction unit followed by `proEtaleUnitLerayTerminalIso` at h^*F.
- w is the degreewise mapped e followed by Gamma_X(j), written as
  `NatTrans.mapHomologicalComplex ... |>.app I` composed with the mapped j.
- The left side is a_I.hom, then Q(w), then a_J.inv. This is exactly the
  node's right-to-left composite a_J inverse Q(w) a_I.
- eta_h is the unit of
  `(proEtaleConstantRingAdjunction A h).mapDerivedCategoryRightDerivedAdjunction`.
- lambda is `(proEtaleUnitLerayIso A h).hom`, oriented
  RGamma_Y(Rh_* N) to RGamma_X(N), with the real terminal normalization above.
- The right side composes RGamma_Y(eta_h), lambda at
  `(proEtaleConstantRingDerivedPullback A h).obj (DerivedCategory.Q.obj I)`,
  and RGamma_X(c_I followed by Q(j)). This is the stated equality in the common
  lifted D(A). Nothing inverts j, and there is no additional conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `ProEtale.finiteCoefficientInverseImageMap_isIso` and its constant-section
  normalization, retained as the named coefficient dependency import.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the four recorded
  `proEtaleConstantRing*` operations/adjunction named above, and
  `proEtaleConstantRingComparison`. Their definitions specialize the published
  ring-sheaf operations, and the derived adjunction uses
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicDirectImageComparison`, whose unique scalar-section normalization
  was read, and reexported `sfIntrinsicModuleEquivalence`.
- `Mathlib.CategoryTheory.Sites.GlobalSections`: `Sheaf.Γ`,
  `Sheaf.ΓNatIsoSheafSections`, `sheafSections`; `PreservesTerminal.iso`
  evaluates the actual base-change functor at the terminal object.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- Stated proof dependencies retain their imports:
  `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`:
  `CategoryTheory.preDerivedAdjunctionGeneral`;
  `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`:
  `Functor.kInjectiveDerivedMapComputation`;
  `Sheaf.CategoryTheory.KInjectiveTotalDerived`:
  `exists_rightDerived_of_enough_isKInjective`;
  `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`.
  The upstream `Adjunction.preservesKInjectiveComplexes` supplies preservation
  for the recorded direct image, and `rightDerivedFunctorCompIso'` derives Leray.

The theorem docstring retains all six natural-language proof steps: preserve
K-injectivity, transpose j using the recorded adjunction, identify its derived
adjunct, compute derived sections on K-injectives, normalize Leray using the
terminal iso, then substitute and cancel. Only the main theorem has `sorry`.
All auxiliary definitions have real data, including their structural proof fields.

Edge cases: the zero ring A, empty schemes, zero complexes, j=0, identity j,
arbitrary non-quasi-isomorphic j, and unbounded complexes remain covered. The
recorded coefficient comparison and the equivalences apply in all these cases;
base change preserves the terminal object also for empty schemes. No boundedness,
nontriviality, invertibility of j or termwise injectivity was introduced.

Searches made on 2026-10-17 UTC:

- LeanSearch via msearch.py: `K-injective derived global sections pullback
  adjunction unit Leray chain representative`; 8 general results including
  `Adjunction.derivedη` and `Functor.totalRightDerivedUnit`, no specialized formula.
- LeanFinder via msearch.py: `Derived global sections adjunction unit Leray
  isomorphism K-injective chain map formula`; 8 results, including generic
  `Adjunction.derived_unit`, `derived'_unit`, and `derivedη_fac_app`, no match.
- Loogle via msearch.py: `CategoryTheory.Adjunction.derived_unit`; one generic
  derived-unit formula, no sections/Leray specialization.
- Mathlib grep via msearch.py: `leray|Leray`, CategoryTheory; zero hits.
- Direct rg of Mathlib CategoryTheory and the full upstream WeilConjectures tree:
  `unit.*leray|leray.*chain` and the node id; no matching statement.
- Direct rg of side `lean/Sheaf`: `unit_leray`, `Leray|leray` in pro-etale
  modules, and sections searches. The abelian etale analogue
  `Sheaf.Paper.EtaleKInjectiveUnitLeray.etaleKInjective_unit_leray` concerns a
  different site and coefficient category. Torsion-point Leray is likewise
  not the present arbitrary scheme morphism. Neither is rebound as this item.


Repair searches and source checks on 2026-10-17 UTC:

- `rg` in `lean/Sheaf/AlgebraicGeometry/ProEtale*.lean` for
  `proEtaleRingModuleDirectImage`, `Terminal|terminal|globalSections`, and
  `sfIntrinsicModuleEquivalence` located the recorded sectionwise pushforward,
  the existing realization equivalence and its direct-image comparison.
- Read `ProEtaleConstantRingOperations.lean`, `ProEtaleOperations.lean`,
  `ProEtaleOperationsCanonicalAdjunction.lean`, `ProEtaleInverseImage.lean`, and
  `SfIntrinsicRealizationTransport.lean` in full. The existing normalized
  direct-image comparison is reused, not restated.
- `rg` of Mathlib `CategoryTheory/Adjunction/Basic.lean` located the formulas
  `homEquiv_apply` and `homEquiv_symm_apply`; cancellation identifies the exact
  coefficient map of the recorded direct image with rho.
- Reopened local Stacks `sites-cohomology.tex`, `lemma-adjoint` and
  `remark-before-Leray`, and `derived.tex`,
  `lemma-pre-derived-adjoint-functors-general` and
  `lemma-adjoint-preserve-K-injectives`; the unit and terminal normalizations
  agree with the source.
- `scompile.py --source Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula`
  reports that no module source is published under this path. The delivery
  wrapper refreshes/rebases against current newtargets-dag. The sandbox node is
  reconstructed from the current read-only base, changing only `lean`.

No statement dispute, statement correction, new node or dependency module.
Only the item's `lean` record changes, including the verbatim signature and
complete declaration list. The private pushforward/adjunction names are absent.

## Second reading by Q13

Author self-check against the node and repaired file, not an independent review;
no agents were started, as required. The maintainer supplies independent review.

Return L is repaired: the type of j, c_I, Lh^*, the ordinary unit in e and the
derived unit all reference the exact recorded operations. The helper named
`proEtaleUnitLerayPushforward_preservesKInjective` is only an instance for the
recorded pushforward; it defines no functor or adjunction. The terminal iso's
source is that recorded pushforward followed by Gamma_Y. Its coefficient-map
identification is adjunction cancellation; its published realization comparison
is section-normalized, and its last map evaluates X times_Y Y = X. Leray is
derived from that actual iso. There is no arbitrary comparison or new assumption.

Rechecked each clause above, especially a_I/a_J/c_I/Leray orientations and Lean's
left-to-right composition; j=0 and non-quasi-isomorphic j remain legal. The
module keeps the accepted u+1 scalar lift and independent site universes.
All declaration names in lean.declarations were regenerated from the repaired
file, deleting the private functor, adjunction and private additivity instance.
No change to the natural-language statement is needed.

## Compilation

Prescribed `scompile.py Q13 lem-trf-proetale-unit-leray-chain-formula` on the
single repaired delivered module exited 0, with no errors or warnings:

```text
sandbox Sheaf/Stage2/Sandbox0.lean [25.8 s]
library Sheaf/AlgebraicGeometry/ProEtaleUnitLerayChainFormula.lean [9.5 s]
```

Both used the wrapper's private overlay and the unchanged 60-second file limit.
`autoImplicit false` binds all universes and variables explicitly. The main
theorem is the sole `sorry`; all source lines have at most 100 characters.
Dry-run/preflight and final delivery evidence follow through the prescribed wrapper.
