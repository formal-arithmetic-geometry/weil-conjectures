## Worker report

The module `Sheaf.CategoryTheory.CechCoefficientDerivedComparison` states
`CategoryTheory.cech_coefficient_derived_comparison`, with one postponed theorem and
real helper constructions. No mathematical statement correction is made.
The existing element-site and coherent-model definition nodes are added to stmt_deps
because the theorem uses their recorded constructions directly.

Hypothesis-by-hypothesis correspondence:

- Small sites/topoi and the common coefficient universe are `{C Y : Type u}`,
  `[SmallCategory C]`, `[SmallCategory Y]`, `J`, `L`; set sheaves, ring sections and
  module fibres are all in `u`. Independent derived morphism universes are
  `wX`, `wXp`, `wY`, `wYp`, `wS`, `wSp`, with localization instances including slices.
  A larger ambient universe can be chosen before these small presentations; no
  equality between derived localization universes is imposed.
- The four commutative ring sheaves are `R R' S S' : Sheaf ... RingCat`, with the
  four sectionwise commutativity predicates `_hR`, `_hR'`, `_hS`, `_hS'`.
- Ringed morphisms are the recorded `RingedToposMorphism` objects `f`, `f'`.
  Cartesian coefficients are `[IsIso f.ringMap]`, `[IsIso f'.ringMap]`.
  The exact module inverse images are `fInverse`, `fInverse'`, their additive,
  finite-limit/finite-colimit instances and `_adj`, `_adj'`.
- The same underlying geometric morphism is expressed by `hi`, `hd`; the
  structural coefficient square is `_coefficient_square`, with the explicit
  transport by `hi`. The scalar maps are `φ : R' ⟶ R`, `ψ : S' ⟶ S`.
- Every scalar functor is precisely `SheafOfModules.restrictScalars`.
  `cechCoefficientRingMap φ A` is the actual whiskered ring map on the element
  site. The finite-limit/finite-colimit assumptions state the exactness already
  asserted in the node, for base and localized scalar functors.
- The specified commutation identifications are `E : CechCoefficientCommutations`.
  `base_underlying` fixes the base comparison using `f.underlying` and
  `f'.underlying`; `pull_sections` fixes identity on every section;
  `push_counit` fixes the push comparison as the counit mate. `E.image` and
  `E.column` are explicit composites of those identifications. Thus these are
  not arbitrary unconstrained comparison arrows.
- `D`, `D'` are the recorded coherent models. Their nerve is `sheafCoverNerve V`,
  i.e. the actual Cech nerve of `V → 1`. Cover-specific derived conclusions
  quantify over `V` and `_hV : Epi (terminal.from V)`; map construction,
  independence and refinement in fact work for any sheaf `V`.
- `M`, `I : InjectiveResolution M`, and `I' : InjectiveResolution (T_X M)`
  give exactly the two nonnegative injective resolutions. Their maps are `I.ι`
  and `I'.ι`, extended with `ComplexShape.embeddingUpNat` for unbounded Q.
- `RF`, `RG` package ordinary total right-derived functors with their units and
  Mathlib `IsRightDerivedFunctor` universal property, not merely arbitrary
  functors. `γ` and `_hγ : CechCoefficientUnitEquation ...` express the node's
  conditional canonical comparison from lem-sfb-exact-square-right-derived-unit.
  The unit equation is imposed on every integer-indexed complex, with canonical
  `mapDerivedCategoryFactors` transports. No invertibility of γ is required.

Conclusion-by-conclusion correspondence:

- The first conjunct supplies a chain map `t` and
  `IsCechCoefficientResolutionLift`, exactly `Q(Ta) ≫ Q(t) = Q(c)`.
  The canonical single-complex identification is included before `I'.ι`.
- The second conjunct says any two such lifts have `Nonempty (Homotopy t₀ t₁)`.
- `maps V t : CechCoefficientMapData ...` supplies an actual bicomplex map
  and total chain map for every t. `components` fixes each (n,q) component to
  `cechCoefficientComponent`, the base comparison, localization comparison,
  and direct image of t in the order of proof step 3.
- `total_components` fixes every diagonal inclusion equation, precisely the
  canonical finite-biproduct total comparison. The recorded bicomplex/total
  has Cech degree first and differential d_Cech + (-1)^n d_I.
- `b`, `b'` obey `D.IsAugmentation`, `D'.IsAugmentation`: the localization
  unit in degree (0,q), followed by its total inclusion, and no other component.
- `eI`, `eJ` are isomorphisms fixed by `IsCechResolutionComparison`: e ≫ RF(Qa)
  equals the right-derived unit. This is exactly the inverse of the usual
  RF(Qa) followed by inverse unit resolution isomorphism. `eJ` includes the
  canonical scalar degree-zero/extension transport in its augmentation.
- The first cover-specific conclusion is the node's total augmentation square,
  in Lean's left-to-right composition order. It includes the exact-localization
  comparison before Q of the extended total map, and the corresponding source
  transport before `eJ.inv`.
- The next conclusion is `IsCechCoefficientColumnComparison` for every simplex.
  It uses `D.push A ⋙ f.modules`, `D'.push A ⋙ f'.modules`, the actual scalar
  functor on the localized ring, `E.column A`, and the localizations of a,c,t.
  The predicate supplies right-derived pairs and the unit-defined canonical γ,
  normalized resolution isomorphisms, and exactly the derived comparison
  equation. `cechCoefficientLocalizedMap` uses `E.pull` followed by restriction
  of the same t, so it is the column of the prescribed bicomplex formula.
- Choice independence is equality after Q for the total and every column.
- The last conjunct is the chain-level total refinement square and every
  (n,q) column refinement square for any actual sheaf map `r : W ⟶ V`, using
  `Arrow.mapCechNerve` and the recorded image functors. Applying Q gives all
  derived refinement squares. The uniquely normalized augmentations and actual
  nerve restrictions retain compatibility with units, identities and composition.
- There is no hypothesis that scalar restriction preserves injectives or that
  γ, the column comparisons, or the total coefficient map are invertible.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`,
  with Mathlib `GrothendieckTopology`/`Sheaf` for the actual topoi presentations.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`,
  especially `ringMap`, `modules`, `underlying`.
- `Sheaf.CategoryTheory.RingedSheafSliceConstruction`: `elementProjection`,
  `elementRing`, `elementModulePullback` (the landed definition node
  def-sfb-element-site-localization). Mathlib's recorded `overFunctor` applies
  to representable localization; the existing element-site constructions cover
  the arbitrary sheaf localizations in this item without copying that notion.
- `Sheaf.CategoryTheory.CoherentCechImageModel`: `sheafCoverNerve`,
  `CoherentCechImageModel`, `bicomplex`, `total`, `totalRefinement`, `IsAugmentation`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` and its additive instance.
- `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`:
  `CategoryTheory.InjectiveResolution`, including `cocomplex`, `ι`, `quasiIso`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`; the size node is a metaconvention.
- `WeilConjectures.CategoryTheory.DoubleComplexTotal` and Mathlib total complexes:
  `HomologicalComplex₂`, `total`, `ιTotal`; no second total construction.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded
  arbitrary-quasi-isomorphism right-derived convention, unit and resolution
  comparison. Helper records package the same universal pair and normalization
  and permit every choice of that unique-up-to-isomorphism pair.
- `Sheaf.CategoryTheory.ExactSquareRightDerivedUnit`:
  `Functor.exactSquare_rightDerived_unit`, the proof dependency that supplies
  the canonical γ characterized by the helper's explicit unit equation.
- Proof imports include `CechInjectiveColumnModel` (`cech_injective_column_model`,
  `cechColumnRestrictComplex`), `RingedSiteKInjectiveResolutionsOfUniverses`
  (`SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`)
  and Mathlib `CochainComplex.IsKInjective.Qh_map_bijective`.

Edge cases checked before writing: M=0 and zero coefficient rings require no
nonzero hypotheses; V=1 yields the degenerate nerve and normalized unit maps;
empty sheaves are admitted whenever the terminal map is epi (including the
degenerate topos); n=0, q=0 use the (0,q) inclusion and positive vertical sign;
negative degrees are genuinely zero by extension; every total diagonal is finite;
identity scalar maps and identity refinements retain the specified comparisons.
The signed homotopy at q=0 has degree -1 target zero. None of these cases is
excluded by a positivity, nonempty-index or injective-preservation hypothesis.

Searches actually made (msearch.py; exact logs in sandbox searches.jsonl):

- LeanFinder: scalar restriction/Cech derived comparison and augmentation/refinement
  queries returned eight complex-index restriction results, no matching theorem.
- Loogle: `SheafOfModules.restrictScalars, HomologicalComplex₂.totalMap` returned
  no hits and unknown totalMap; the existing total API is `total.map`.
- Mathlib grep: `(cech|Cech).*(scalar|coefficient)|(scalar|coefficient).*(cech|Cech)`
  returned zero hits, both globally and in CategoryTheory.
- LeanSearch: exact scalar restriction/derived Cech comparison returned the existing
  `SheafOfModules.restrictScalars` and presheaf/module restriction constructions,
  which are reused, but no coherent augmentation-and-derived-column theorem.
- Direct rg of WeilConjectures and Sheaf for coefficient/Cech combinations and the
  blueprint id found specialized etale coefficient and affine Cech statements;
  none handles arbitrary ring sheaves, coherent element-site slices and this
  canonical right-derived coefficient square. The proposed declaration names
  were also checked against the source tree and upstream name index.

Read the cited source at derived.tex lemma-right-derived-exact-functor (015F)
and lemma-K-injective (070I): exact functors preserve quasi-isomorphisms, and
maps to K-injectives are computed in the homotopy category. The additional
coherent Cech coefficient argument is the explicitly agent-authored extension
in the node's seven proof steps, reproduced in the theorem docstring.

No STATEMENT-DISPUTED issue, new definition node, or dependency repair is needed.
Every theorem proof remains sorry; helper definitions have real data.
The module uses autoImplicit false and explicit universe declarations.

Validation: compiled through the prescribed scompile.py wrapper under the
unchanged 60-second per-file limit. Expected sorry warnings only are permitted.
The worker delivers directly; the maintainer supplies the independent reading.

## Second reading by Q110

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
