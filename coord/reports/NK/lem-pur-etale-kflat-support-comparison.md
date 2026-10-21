## Worker report

The comparison module states `AlgebraicGeometry.Etale.KFlatSupportComparison.etale_kflat_support_comparison` with `sorry`. Its helpers, in `EtaleKFlatSupportData`, are explicit constructions from existing ordinary-etale, cochain and derived-category interfaces. The item statement is unchanged. The new definition node `def-pur-etale-kflat-support-data` owns the canonical diagram data; there are no dependency repairs. The item gains only this definition in `stmt_deps`.

Hypothesis and clause audit:

- Schemes and closed/open pair: `i : Z ⟶ P`, `[IsClosedImmersion i]`, `j : U ⟶ P`, `[IsOpenImmersion j]`, and `hij : Set.range i.base = (Set.range j.base)ᶜ`.
- Finite commutative rings and unital map: `A B : Type (u + 1)`, `[CommRing A]`, `[CommRing B]`, `[Finite A]`, `[Finite B]`, and `φ : A →+* B`. The zero ring is allowed.
- The ordinary small etale module derived categories are the recorded `DerivedCategoryModule A P`, namely `DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u+1} A))`. No pro-etale category or condensed realization is substituted.
- `L : DerivedCategory.Plus ...` includes exactly bounded-below L. `_hTL`, `_hRTL`, `_hRL` and `_hTRL` are the other four stated cohomological boundedness hypotheses, each written `∃ n : ℤ, ... .IsGE n`. No strict bound on the representing complexes or on Q is assumed.
- `I`, `[I.IsKInjective]`, `[∀ n, Injective (I.X n)]` and `e : DerivedCategory.Q.obj I ≅ L.obj` give the specified representative, for every representing isomorphism.
- `Q`, augmentation `π` to the single complex on `scalarCoefficientSheaf φ P`, `[QuasiIso π]`, `hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q` and `_hQf : ∀ n, ObjectProperty.flat (Q.X n)` give the chosen flat-term K-flat resolution. The latter two are the existing monoidal-category predicates for precisely K-flatness and exact tensor by each term; the commutative coefficient tensor is symmetric. This uses the ModuleCat-valued encoding of the recorded derived categories, rather than privately rebuilding ring-sheaf modules.
- `F`, `η : 𝟭 _ ⟶ F`, its K-injective and termwise-injective object instances and its quasi-isomorphism instances express a functorial replacement. The upstream `kInjectiveResolutionFunctor` and `toKInjectiveResolution` are such a choice. The theorem allows every such choice. N is literally `Q ⊗ I`, J is `F.obj (Q ⊗ I)`, a is `η.app (Q ⊗ I)`.
- The support rows are exactly `etaleSupportSequence`, using the dependency's `closedUpperShriek` counit and open adjunction unit. `totalTensorSequence Q (etaleSupportSequence ... I)` applies `tensorLeft Q` to this row; `hTop` and `hBottom` assert their short exactness, equivalent to degreewise short exactness of complexes.
- `IsRightMap`, via `IsTotalAdjunct`, fixes the last map on each summand of every total degree: its component is `tensorAdjunct` of the ordinary inverse-image/direct-image adjunction, applied to the summand inclusion followed by `a.f n`. This is the displayed last arrow: restrict Q, evaluate the open counit, and apply j^*a. These values determine the total map uniquely and do not assert that j_* preserves infinite direct sums.
- `m` is an actual `ShortComplex` morphism, with prescribed middle and last components. Its two commutative-square fields and uniqueness assertion specify the induced kernel map. No arbitrary completion of triangle squares is chosen.
- Both `triangleOfSES` membership clauses assert distinguishedness. The explicit `triangleOfSESδ` equation asserts compatibility of the natural connecting arrows. The canonical `triangleOfSES.map hTop hBottom m` consequently is the complete triangle morphism.
- `tensorModel` uses the localized Koszul symmetry, the existing one-sided K-flat tensor comparison, the augmentation π, the representative e, the published `scalarTensorFunctor_eq` transport and the normalized `scalarTensorIso`. `replacementIso` uses exactly the inverse of Q(a). The displayed conjugated middle-map equation is the identity on Res(TL).
- `sourceThirdModel` and `targetThirdModel` use the dependency's actual `etaleSupportThirdComparison`. The equation on Q(m.τ₃) identifies the map with `restrictedProjection`, which restricts the specified B-linear `coefficientProjection` and applies the canonical restriction/direct-image and restriction/inverse-image comparisons. `coefficientProjection` is the normalized published `scalarMate` followed by the inverse scalar/pullback comparison. It is exactly T Rj_*j^*L → Rj_*j^*TL.
- `IsIso (Q.map m.τ₃) → IsIso (Q.map m.τ₁)` is the final implication. The last clause expresses naturality for every chain map f and comparison diagram on its target, using the same functor F and its map `F.map (Q ◁ f)`. Together with SES-boundary naturality this includes the connecting square.
- Every chain complex and chain morphism in the diagram is A-linear. B appears only in coefficient sheaves, derived scalar extension and the B-linear coefficient projection; no strict B-action on Q is specified.

Dependency declarations inspected:

- `def-weil-pbc-scheme-conventions`: `convention`, `scheme/morphism conventions`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `lem-pur-sheaf-ring-derived-coefficient-adjunction`: `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`, `SheafOfModules.sheafRingDerivedCoefficientAdjunction`.
- `lem-pc-kflat-resolution`: `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `lem-pur-kinjective-degreewise-existence`: `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`, `CochainComplex.injective_kInjectiveResolutionFunctor_obj_X`.
- `lem-pur-etale-injective-support-sequence`: `Sheaf.AlgebraicGeometry.EtaleInjectiveSupportSequence`, `AlgebraicGeometry.Etale.etale_injective_support_sequence`.
- `lem-weil-pbc-kflat-fixed-tensor-triangulated`: `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`, `SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated`.
- `lem-pur-etale-scalar-mate-projection`: `Sheaf.Paper.PurEtaleScalarMateProjection`, `AlgebraicGeometry.Etale.scalarMate_restrict_eq_projection`.
- `def-pc-flat-sheaf-modules`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`.
- `lem-pc-module-filtered-colimits-tensor`: `WeilConjectures.Algebra.Homology.FilteredColimitsTensor`, `SheafOfModules.filteredColimitsTensorComplex`.
- `def-pc-tensor-complex-sheaves`: `Mathlib.Algebra.Homology.BifunctorShift`, `CochainComplex.mapBifunctor`.
- `lem-pur-cochain-pullback-tensor-coherence`: `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`, `CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`.
- `prop-weil-pbc-inverse-image-modules-exact`: `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`, `AlgebraicGeometry.etaleInverseImageModulesExact`.
- `lem-weil-pbc-termwise-adjunction-homotopy`: `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`, `CategoryTheory.Adjunction.mapHomotopyCategory`.
- `lem-weil-pbc-complex-ses-triangle`: `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`, `DerivedCategory.triangleOfSESδ`.
- `lem-sp-etale-derived-chain-transpose`: `Sheaf.AlgebraicGeometry.EtaleDerivedChainTranspose`, `AlgebraicGeometry.Etale.etaleDerivedChainTranspose`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `def-kun-projection-formula-map`: `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`, `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`.
- `lem-sbc-canonical-restrict-scalars-functor-comparisons`: `Sheaf.Paper.EtaleUnboundedRestrictionComparison`, `AlgebraicGeometry.Etale.scalarRestrictionDirectImageMap`.
- `lem-sf-triangle-morphism-iso`: `Mathlib/CategoryTheory/Triangulated/Pretriangulated.lean`, `CategoryTheory.Pretriangulated.isIso₂_of_isIso₁₃`.

The proof-only imports retain the recorded proof plan. Cochain tensor, adjunction, exact pullback, projection formula, SES triangles and two-of-three triangle isomorphisms are imported through the relevant dependency modules. The general ring-sheaf scalar and resolution interfaces are retained as public imports of the recorded statement dependencies; the theorem uses the established equivalent constant-module-sheaf encoding specified by def-weil-pbc-derived-categories.

Edge cases checked before stating: empty Z (support kernel zero), empty U (restriction quotient zero), both empty, I=0, A=B with Q=A[0], the zero ring, non-flat Z/4→Z/2, and unbounded coefficient resolutions Q. None is excluded by universes, nontriviality, nonemptiness, ring flatness or strict complex bounds. Infinite total sums are direct sums. The source's extra bounded-below hypotheses are retained even where chain-level constructions do not use them. No statement dispute or source correction.

Searches:

- msearch leanfinder, query “Tensor a K flat resolution with the injective support sequence gives a morphism of support triangles”: 8 hits, generic SES boundary, Tor, resolutions and injective computations; no ordinary-etale coefficient support diagram.
- msearch loogle, query `DerivedCategory.triangleOfSES`: 12 hits, exact matches for the generic SES triangle API used here; no coefficient-support comparison.
- msearch grep, query `support.*[Tt]ensor|[Tt]ensor.*[Ss]upport`: 3 irrelevant Mathlib hits (finitely-supported tensor products and module support).
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the same concepts found existing support, projection and tensor tools but no actual K-flat coefficient-support comparison; rg for the exact node id returned no declaration. No private replacement of these existing tools was written.

## Second reading by NK

The dispatcher assigned a sole worker and explicitly prohibited starting other agents. This section records an author rereading, not an invented independent review; the maintainer supplies the independent review after delivery. I checked the complete hypothesis/clause mapping above against the node and file. In particular I checked that the actual A-injective support rows, rather than restrictions of B-injective rows, are used; that the inverse Q(a) fixes the middle identification; that the coefficient map is specified by the normalized mate; and that the connecting-arrow equation is present. Compile feedback is repaired before delivery.

## New nodes

`def-pur-etale-kflat-support-data` defines the canonical total-tensor support row, its action on maps, the summand characterization of its quotient comparison, and the normalized derived identifications and coefficient projection. These are real constructions, with no postponed theorem or chosen arbitrary arrow. They are in `Sheaf.AlgebraicGeometry.EtaleKFlatSupportData`; the comparison theorem imports that module. The new node names the data the item's own expanded support-diagram proof needs. Separating the definition from the theorem also gives independent per-file compiler checks. Its blueprint ancestor is null, as `blueprint_refs.py ancestor` reports for the launcher-created seed; its `via` adds the assigned item to the existing path.

For the new node I searched with LeanSearch (canonical total tensor support sequence and adjunct comparison), LeanFinder (canonical K-flat tensor comparison data), Loogle (adjunction homEquiv, tensor summands and K-flat comparison), Mathlib grep (KFlatSupport/tensor-support), and rg on all DAG nodes, WeilConjectures and Sheaf for IsTotalAdjunct/IsRightMap/KFlatSupportData. The search records and results are copied into the new node. Results are generic adjunction/flatness APIs or the assigned statement's descriptions, with no preexisting definition of these combined normalized data. Each generic API is reused. `blueprint_refs.py search support.*comparison` found no blueprint node.

The second reading also checked the new definition against the source's construction: the summand equation includes both ordinary pullback tensor comparisons and the counit; tensorModel includes signed interchange and the actual coefficient augmentation; replacementIso is the inverse localized a; and the restricted projection retains both canonical restriction comparisons. No helper definition has sorry data.

Verification: both modules have compiled separately through scompile.py against the published library. The data module has no sorry, and the comparison module has exactly the assigned theorem with sorry. The first dry run found an overlong docstring line, which was wrapped. The next check compiled cleanly and caught a metadata signature truncated at a local let; the record now contains the complete verbatim theorem signature. The corrected dry run and delivery follow.
