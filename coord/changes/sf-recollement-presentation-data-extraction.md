# SfRecollementPresentation and canonical localization data

## Reason

The geometric realization and generic derived-localization lemmas require the existing
presentation data. Extracting that data avoids a circular import of the theorem module.
No existing signature, definition body, instance priority, visibility or target changes.
The original module publicly imports the new data module. All old public imports remain
available through that module. No adopted source-library module is changed.

## Old

The following source blocks move from the item module to the new data module
with their signatures and bodies verbatim. The surrounding variable context is unchanged.

```lean
/-- The canonical inverse-image coefficient map, adjoint to the completed structural
map. Source: blueprint proof step 3; Stacks 098T
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementCoefficientMap {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
    (sfCompletedCoefficientMap l E f)

/-- The actual completed coefficient comparison is invertible.
Source: blueprint proof step 3; Stacks 098T
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: this is exactly PurCompactSupport.completedPullMap. Its existing isomorphism
theorem applies to the same completed structural map and adjunction. -/
@[instance] theorem sfRecollementCoefficientMap_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (sfRecollementCoefficientMap l E f) := by
  exact PurCompactSupport.completedPullMap_isIso l E f

/-- The normalized ordinary integral module adjunction.
Source: blueprint proof steps 3 and 7; Stacks 03D2, 07A6
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingModuleAdjunction f (completedIntegralCommRingSheafUnrestricted l E Y)
    (completedIntegralCommRingSheafUnrestricted l E X)
    (asIso (sfRecollementCoefficientMap l E f))

/-- The closed term on module sheaves, before taking its derived functor.
Source: blueprint proof step 7; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleClosed {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  proEtaleRingModulePullback i (completedIntegralCommRingSheafUnrestricted l E X)
      (completedIntegralCommRingSheafUnrestricted l E Z)
      (asIso (sfRecollementCoefficientMap l E i)) ⋙
    proEtaleRingModuleDirectImage i (completedIntegralCommRingSheafUnrestricted l E X)
      (completedIntegralCommRingSheafUnrestricted l E Z)
      (asIso (sfRecollementCoefficientMap l E i))

/-- The closed unit, on actual completed-coefficient module sheaves.
Source: blueprint proof step 7; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleUnit {Z X : Scheme.{u}} (i : Z ⟶ X) :
    𝟭 (scalarReductionSource.{u, u} l E X) ⟶ sfRecollementModuleClosed l E i :=
  (sfRecollementModuleAdjunction l E i).unit

/-- The open term is the kernel of the closed unit. The ringed localization sequence
identifies this exact kernel, with its inclusion, with j!j* and its counit.
Source: blueprint proof steps 1 and 7; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleOpen {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  kernel (sfRecollementModuleUnit l E i)

/-- The specified open counit in the kernel presentation.
Source: blueprint proof step 7; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfRecollementModuleCounit {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  kernel.ι (sfRecollementModuleUnit l E i)

private def sfRecollementKernelIso
    {C D : Type*} [Category* C] [Category* D] [Abelian D]
    {F G H : C ⥤ D} (ε : F ⟶ G) (η : G ⟶ H)
    (hs : ∀ M, Mono (ε.app M) ∧
      (ComposableArrows.mk₂ (ε.app M) (η.app M)).Exact) :
    F ≅ kernel η := by
  have hz : ε ≫ η = 0 := by
    ext M
    exact (hs M).2.toIsComplex.zero 0
  let k := KernelFork.ofι ε hz
  have hk : IsLimit k := by
    apply evaluationJointlyReflectsLimits
    intro M
    apply (KernelFork.isLimitMapConeEquiv ..).2
    have : Mono (ε.app M) := (hs M).1
    let T := ComposableArrows.mk₂ (ε.app M) (η.app M)
    have he := (T.exact₂_iff (hs M).2.toIsComplex).1 (hs M).2
    change (ShortComplex.mk (ε.app M) (η.app M) _).Exact at he
    exact he.fIsKernel
  exact ((kernelIsKernel η).conePointUniqueUpToIso hk).symm

/-- Exactness and additivity of both localization terms.
Source: blueprint proof steps 1, 3--7; Stacks 09AH, 09BM
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: profinite coefficients identify ordinary inverse image with restriction.
Ringed open-closed localization identifies the kernel term with open extension of
restriction and the closed term with closed direct image of restriction. All four
module functors are exact and additive; these properties pass to their composites
and across the kernel identification. -/
theorem sfRecollementModule_exact {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    (sfRecollementModuleOpen l E i).Additive ∧
    PreservesFiniteLimits (sfRecollementModuleOpen l E i) ∧
    PreservesFiniteColimits (sfRecollementModuleOpen l E i) ∧
    (sfRecollementModuleClosed l E i).Additive ∧
    PreservesFiniteLimits (sfRecollementModuleClosed l E i) ∧
    PreservesFiniteColimits (sfRecollementModuleClosed l E i) := by
  classical
  let W : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let : TopologicalSpace.NoetherianSpace W.toScheme :=
    W.ι.isOpenEmbedding.isInducing.noetherianSpace
  let U : X.ProEt := ProEt.mk W.ι
  have : IsOpenImmersion U.hom := inferInstanceAs (IsOpenImmersion W.ι)
  have : QuasiCompact U.hom := inferInstanceAs (QuasiCompact W.ι)
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let S := completedIntegralCommRingSheafUnrestricted l E Z
  let c := asIso (sfRecollementCoefficientMap l E i)
  obtain ⟨q, ⟨eq⟩, ai, aj, _, _, _, _, hOl, hOc, hCl, hCc, hs, _⟩ :=
    proEtale_ringed_open_closed i U W.range_ι R
  have : PreservesFiniteLimits (proEtaleRingedExtensionByZero U R) := hOl
  have : PreservesFiniteColimits (proEtaleRingedExtensionByZero U R) := hOc
  have : PreservesFiniteLimits (proEtaleRingedDirectImage i R) := hCl
  have : PreservesFiniteColimits (proEtaleRingedDirectImage i R) := hCc
  have hi := (proEtale_immersion_inverseImage_preservesLimits i).2.2 R
  have : (proEtaleModuleInverseImage i R).Additive := hi.choose
  have : (proEtaleRingedDirectImage i R).Additive := ai.right_adjoint_additive
  have hj := (proEtale_immersion_inverseImage_preservesLimits U.hom).2.2 R
  have : (proEtaleModuleInverseImage U.hom R).Additive := hj.choose
  have : PreservesFiniteLimits (proEtaleModuleInverseImage U.hom R) :=
    hj.choose_spec.1
  have : PreservesFiniteColimits (proEtaleModuleInverseImage U.hom R) :=
    hj.choose_spec.2.1
  have : q.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : (SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients R) U).Additive :=
    Functor.additive_of_iso eq
  have : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients R) U) :=
    preservesFiniteLimits_of_natIso eq
  have : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients R) U) :=
    preservesFiniteColimits_of_natIso eq
  have : (proEtaleRingedExtensionByZero U R).Additive :=
    Functor.additive_of_preserves_binary_products _
  let e := AlgebraicGeometry.Scheme.coefficientTransport i R S c
  let a := ai.comp e.symm.toAdjunction
  let eK : sfRecollementModuleOpen l E i ≅ kernel ai.unit :=
    AlgebraicGeometry.Scheme.unitKernelIsoOfLeftIso (sfRecollementModuleAdjunction l E i) a
      (AlgebraicGeometry.Scheme.pullbackComparison i R S c ai) ≪≫
      (AlgebraicGeometry.Scheme.unitKernelCompEquivalenceIso ai e.symm).symm
  let eO := sfRecollementKernelIso aj.counit ai.unit
    (fun M ↦ ⟨(hs M).1, (hs M).2.2⟩)
  have : (kernel ai.unit).Additive := Functor.additive_of_iso eO
  have : PreservesFiniteLimits (kernel ai.unit) := preservesFiniteLimits_of_natIso eO
  have : PreservesFiniteColimits (kernel ai.unit) := preservesFiniteColimits_of_natIso eO
  have hOa := Functor.additive_of_iso eK.symm
  have hOl := preservesFiniteLimits_of_natIso eK.symm
  have hOc := preservesFiniteColimits_of_natIso eK.symm
  have : PreservesFiniteLimits (proEtaleRingModuleDirectImage i R S c) :=
    preservesFiniteLimits_of_natIso (AlgebraicGeometry.Scheme.directImageComparison i R S c).symm
  have : PreservesFiniteColimits (proEtaleRingModuleDirectImage i R S c) :=
    preservesFiniteColimits_of_natIso (AlgebraicGeometry.Scheme.directImageComparison i R S c).symm
  refine ⟨hOa, hOl, hOc, ?_, ?_, ?_⟩ <;>
    dsimp only [sfRecollementModuleClosed] <;> infer_instance

/-- Exact open functor's additive structure. Source: Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleOpen_additive {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] : (sfRecollementModuleOpen l E i).Additive :=
  (sfRecollementModule_exact l E i).1

/-- Exact open functor's left exactness. Source: Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleOpen_limits {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    PreservesFiniteLimits (sfRecollementModuleOpen l E i) :=
  (sfRecollementModule_exact l E i).2.1

/-- Exact open functor's right exactness. Source: Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleOpen_colimits {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    PreservesFiniteColimits (sfRecollementModuleOpen l E i) :=
  (sfRecollementModule_exact l E i).2.2.1

/-- Exact closed functor's additive structure. Source: Stacks 09BM
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleClosed_additive {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] : (sfRecollementModuleClosed l E i).Additive :=
  (sfRecollementModule_exact l E i).2.2.2.1

/-- Exact closed functor's left exactness. Source: Stacks 09BM
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleClosed_limits {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    PreservesFiniteLimits (sfRecollementModuleClosed l E i) :=
  (sfRecollementModule_exact l E i).2.2.2.2.1

/-- Exact closed functor's right exactness. Source: Stacks 09BM
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
instance sfRecollementModuleClosed_colimits {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsNoetherian X] :
    PreservesFiniteColimits (sfRecollementModuleClosed l E i) :=
  (sfRecollementModule_exact l E i).2.2.2.2.2

/-- The two functorial vertices and the prescribed first two arrows of a recollement
triangle. This is only presentation data, without an existence or vanishing assertion.
Source: blueprint displayed open-closed triangle
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
structure SfRecollementPresentation (C : Type w) [Category.{w₁} C] where
  openTerm : C ⥤ C
  closedTerm : C ⥤ C
  counit : openTerm ⟶ 𝟭 C
  unit : 𝟭 C ⟶ closedTerm

/-- Distinguished completion, all integer-shift Hom vanishing, uniqueness of the third
arrow, and its naturality for every morphism. Source: blueprint statement, order 1851
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRecollementConclusion {C : Type w} [Category.{w₁} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [shiftAdditive : ∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (P : SfRecollementPresentation C) : Prop :=
  (∀ K : C, ∃! δ : P.closedTerm.obj K ⟶ (P.openTerm.obj K)⟦(1 : ℤ)⟧,
    Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C) ∧
  (∀ (K : C) (m : ℤ), Subsingleton ((P.openTerm.obj K)⟦m⟧ ⟶ P.closedTerm.obj K)) ∧
  ∀ (K L : C) (f : K ⟶ L)
    (δ : P.closedTerm.obj K ⟶ (P.openTerm.obj K)⟦(1 : ℤ)⟧)
    (δ' : P.closedTerm.obj L ⟶ (P.openTerm.obj L)⟦(1 : ℤ)⟧),
    Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C →
    Triangle.mk (P.counit.app L) (P.unit.app L) δ' ∈ distTriang C →
    P.closedTerm.map f ≫ δ' = δ ≫ (shiftFunctor C (1 : ℤ)).map (P.openTerm.map f)

/-- The finite presentation uses precisely the dependency's two adjunction maps.
Source: blueprint finite-stage paragraph; Stacks 09AH
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfFiniteRecollementPresentation {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A] :
    SfRecollementPresentation (proEtaleDerivedCategory X A) where
  openTerm := sfIntrinsicDerivedPullback A j ⋙ sfIntrinsicDerivedOpen A j
  closedTerm := sfIntrinsicDerivedPullback A i ⋙ proEtaleConstantDerivedDirectImage i A
  counit := (exceptionalOpenAdjunction j A).counit
  unit := (finiteRecollementDerivedAdjunction i A).unit

/-- The conclusion on a full constructible subcategory of an ambient derived category.
Distinguishedness is tested in the ambient category, as in the recorded finite
recollement definition; the outer vertices are required to remain constructible.
Source: blueprint statement (blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRecollementConclusionOn {C : Type w} [Category.{w₁} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (P : SfRecollementPresentation C) (S : ObjectProperty C) : Prop :=
  (∀ (K : C), S K → S (P.openTerm.obj K) ∧ S (P.closedTerm.obj K) ∧
    (∃! δ : P.closedTerm.obj K ⟶ (P.openTerm.obj K)⟦(1 : ℤ)⟧,
      Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C) ∧
    ∀ m : ℤ, Subsingleton ((P.openTerm.obj K)⟦m⟧ ⟶ P.closedTerm.obj K)) ∧
  ∀ (K L : C), S K → S L → ∀ (f : K ⟶ L)
    (δ : P.closedTerm.obj K ⟶ (P.openTerm.obj K)⟦(1 : ℤ)⟧)
    (δ' : P.closedTerm.obj L ⟶ (P.openTerm.obj L)⟦(1 : ℤ)⟧),
    Triangle.mk (P.counit.app K) (P.unit.app K) δ ∈ distTriang C →
    Triangle.mk (P.counit.app L) (P.unit.app L) δ' ∈ distTriang C →
    P.closedTerm.map f ≫ δ' = δ ≫ (shiftFunctor C (1 : ℤ)).map (P.openTerm.map f)

/-- Positive-level specialization with the recorded finiteness proof supplied
internally, so finiteness is not an extra theorem hypothesis.
Source: blueprint finite-stage paragraph
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def sfFiniteRecollementAt {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] (n : ℕ) (hn : 1 ≤ n) :
    SfRecollementPresentation (proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  sfFiniteRecollementPresentation i j (Padic.coefficientExtensionRing l E n)

private theorem sfConstantDirectImageEq (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleConstantRingPushforward A f = proEtaleConstantModuleDirectImage f A := by
  unfold proEtaleConstantRingPushforward proEtaleRingModuleDirectImage
    proEtaleConstantModuleDirectImage proEtaleConstantRingComparison
  rw [proEtaleConstantModulePullback_ring_direct]

private theorem sfFiniteConstructibleIso
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    {K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)}
    (e : K ≅ L) (h : intrinsicFiniteTorsionConstructible l E n hn X L) :
    intrinsicFiniteTorsionConstructible l E n hn X K := by
  let A := Padic.coefficientExtensionRing l E n
  have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let H := DerivedCategory.homologyFunctor (proEtaleRingModules X (proEtaleConstantRing X A))
  constructor
  · apply h.1.subset
    intro r hr hz
    exact hr (hz.of_iso ((H r).mapIso e))
  · intro r
    have hr := h.2 r
    rw [proEtaleModuleRestriction_constructible_iff] at hr ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction X A).mapIso ((H r).mapIso e)).symm hr

/-- The Noetherian structure supplied by the finite-type structure map over a field.
Source: blueprint proof step 1; Stacks 01T6
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: a field is Noetherian; the structure morphism is locally of finite type,
so its source is locally Noetherian. Quasi-compactness over the compact spectrum
of the field makes the source compact, giving the Noetherian structure. -/
theorem sfRecollementNoetherian (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    IsNoetherian X := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  exact ⟨⟩

/-- The open complement has its inherited finite-type structure over k and is a
quasi-compact open immersion. Source: blueprint proof step 1; Stacks 01T6
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: X is Noetherian by finite type over the field. Every open subset of each
Noetherian affine is quasi-compact and a finite union of principal opens. Their
coordinate rings are finitely generated by adjoining inverses. These covers give
finite type over k; Noetherian quasi-compactness also gives quasi-compactness of j. -/
theorem sfRecollementOpenFiniteType (k : Type u) [Field k]
    {U X : Scheme.{u}} [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))] :
    LocallyOfFiniteType (U ↘ Spec (.of k)) ∧
      QuasiCompact (U ↘ Spec (.of k)) ∧ QuasiCompact j := by
  have : IsNoetherian X := sfRecollementNoetherian k X
  have : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := inferInstance
  have : LocallyOfFiniteType (U ↘ Spec (.of k)) := by
    rw [← comp_over j (Spec (.of k))]
    infer_instance
  have : QuasiCompact (U ↘ Spec (.of k)) := by
    rw [← comp_over j (Spec (.of k))]
    infer_instance
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- A normalized integral presentation uses the exact sheaf kernel and closed term,
with their actual sheaf maps on every representative complex. This pins down the
arrows, not just the isomorphism classes of the three vertices.
Source: blueprint proof steps 3--7 (blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfIntegralRecollementNormalization {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (hX : IsNoetherian X)
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X)) : Prop :=
  letI := hX
  ∃ (a : (sfIntegralConstructible l E X).ι ⋙
        (sfRecollementModuleOpen l E i).mapDerivedCategory ≅
      P.openTerm ⋙ (sfIntegralConstructible l E X).ι)
    (c : (sfIntegralConstructible l E X).ι ⋙
        (sfRecollementModuleClosed l E i).mapDerivedCategory ≅
      P.closedTerm ⋙ (sfIntegralConstructible l E X).ι),
    ∀ (B : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ)
      (hB : sfIntegralConstructible l E X (DerivedCategory.Q.obj B)),
      a.hom.app ⟨DerivedCategory.Q.obj B, hB⟩ ≫
          (P.counit.app ⟨DerivedCategory.Q.obj B, hB⟩).hom =
        (sfRecollementModuleOpen l E i).mapDerivedCategoryFactors.hom.app B ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (F := sfRecollementModuleOpen l E i)
              (G := 𝟭 (scalarReductionSource.{u, u} l E X))
              (sfRecollementModuleCounit l E i) (.up ℤ)).app B) ∧
      (P.unit.app ⟨DerivedCategory.Q.obj B, hB⟩).hom ≫
          c.inv.app ⟨DerivedCategory.Q.obj B, hB⟩ ≫
          (sfRecollementModuleClosed l E i).mapDerivedCategoryFactors.hom.app B =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (F := 𝟭 (scalarReductionSource.{u, u} l E X))
            (G := sfRecollementModuleClosed l E i)
            (sfRecollementModuleUnit l E i) (.up ℤ)).app B)

/-- Rational presentations are obtained from exactly the integral functors and maps
by the recorded raw localization. The two comparison squares retain the prescribed
counit and unit. Source: blueprint proof step 10
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRationalRecollementNormalization (X : Scheme.{u})
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X))
    (Q : SfRecollementPresentation (sfRationalConstructibleCategory l E X)) : Prop :=
  (∀ K, Q.openTerm.obj K = ⟨P.openTerm.obj K.obj⟩ ∧
    Q.closedTerm.obj K = ⟨P.closedTerm.obj K.obj⟩) ∧
  ∃ (a : sfRationalConstructibleLocalization l E X ⋙ Q.openTerm ≅
      P.openTerm ⋙ sfRationalConstructibleLocalization l E X)
    (c : sfRationalConstructibleLocalization l E X ⋙ Q.closedTerm ≅
      P.closedTerm ⋙ sfRationalConstructibleLocalization l E X),
    (∀ K, a.hom.app K ≫
        (sfRationalConstructibleLocalization l E X).map (P.counit.app K) =
      Q.counit.app ((sfRationalConstructibleLocalization l E X).obj K)) ∧
    ∀ K, Q.unit.app ((sfRationalConstructibleLocalization l E X).obj K) ≫ c.hom.app K =
      (sfRationalConstructibleLocalization l E X).map (P.unit.app K)

/-- Identification of the integral kernel presentation with the recorded completed
operations. Constructibility of the restricted pullback is included in the witness.
The closed term is the recorded integral direct image of the completed pullback: a
vertex of the specified Roos triangle of the finite-image tower, R lim Res_n Ri_{*,n}.
Exact countable products supply the derived-category products of that tower.
Source: blueprint proof steps 3--7
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfIntegralRecollementVertices
    (k : Type u) [Field k] (hk : IsUnit (l : k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))]
    (P : SfRecollementPresentation (sfIntegralConstructibleCategory l E X)) : Prop :=
  letI : LocallyOfFiniteType (U ↘ Spec (.of k)) := (sfRecollementOpenFiniteType k j).1
  letI : QuasiCompact (U ↘ Spec (.of k)) := (sfRecollementOpenFiniteType k j).2.1
  letI : QuasiCompact j := (sfRecollementOpenFiniteType k j).2.2
  (∀ K : sfIntegralConstructibleCategory l E X,
    ∃ h : sfIntegralConstructible l E U ((integralDerivedPullback l E j).obj K.obj),
      Nonempty (P.openTerm.obj K ≅ sfIntegralCompactSupportValue l E k hk
        (Compactification.ofIsOpenImmersion j) ⟨_, h⟩)) ∧
  letI : HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E X)) :=
    integralOperationsDerivedCountableProducts l E X
  ∀ K : sfIntegralConstructibleCategory l E X,
    ∃ L : SfIntegralDirectImage l E i ((integralDerivedPullback l E i).obj K.obj),
      Nonempty ((P.closedTerm.obj K).obj ≅ L.obj)

/-- The common-stage presentation is the descent of the actual rational presentations.
Naturality covers every common-stage representative, rather than only maps from one
fixed coefficient field. The comparison squares specify the descended counit and unit.
Source: blueprint proof step 11
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfCommonStageRecollementNormalization (X : Scheme.{u})
    (Q : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation (GeneralAlgebraicallyClosedCoefficients.Stage l Ω X L))
    (R : SfRecollementPresentation (generalAlgebraicallyClosedConstructibleCategory l Ω X)) :
    Prop :=
  (∀ K, R.openTerm.obj K = ⟨K.stage, (Q K.stage).openTerm.obj K.obj⟩ ∧
    R.closedTerm.obj K = ⟨K.stage, (Q K.stage).closedTerm.obj K.obj⟩) ∧
  ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ (a : GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) L ⋙
          R.openTerm ≅ (Q L).openTerm ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion L)
      (c : GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) L ⋙
          R.closedTerm ≅ (Q L).closedTerm ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion L),
      (∀ K, a.hom.app K ≫ (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
          ((Q L).counit.app K) =
        R.counit.app ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K)) ∧
      ∀ K, R.unit.app ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K) ≫
          c.hom.app K = (GeneralAlgebraicallyClosedCoefficients.inclusion L).map ((Q L).unit.app K)

/-- Exactness for the shift structure on the specified geometric Frobenius functor.
The shift structure is included as data because its interface was not previously
exported by the recorded pullback module. Source: blueprint proof steps 12 and 16
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRecollementFrobeniusExact
    {C : Type w} [Category.{w₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (G : C ⥤ C) (s : G.CommShift ℤ) : Prop :=
  letI := s
  G.IsTriangulated

/-- All three arrows are morphisms of the recorded fixed pairs. The outer Weil
isomorphisms are uniquely characterized by the first two commuting squares; the third
uses the induced shift of the open Weil structure.
Source: blueprint statement and proof steps 12--16
(blueprint: prop-sf-open-closed-triangle-all-stages). -/
def SfRecollementWeilEquivariant
    {C : Type w} [Category.{w₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : SfRecollementPresentation C) (G : C ⥤ C) (s : G.CommShift ℤ) : Prop :=
  letI := s
  ∀ K : CategoryTheory.Endofunctor.IsoAlgebra G,
    ∃! ac : (G.obj (P.openTerm.obj K.carrier) ≅ P.openTerm.obj K.carrier) ×
        (G.obj (P.closedTerm.obj K.carrier) ≅ P.closedTerm.obj K.carrier),
      (G.map (P.counit.app K.carrier) ≫ K.str.hom =
        ac.1.hom ≫ P.counit.app K.carrier) ∧
      (G.map (P.unit.app K.carrier) ≫ ac.2.hom =
        K.str.hom ≫ P.unit.app K.carrier) ∧
      ∀ δ : P.closedTerm.obj K.carrier ⟶ (P.openTerm.obj K.carrier)⟦(1 : ℤ)⟧,
        Triangle.mk (P.counit.app K.carrier) (P.unit.app K.carrier) δ ∈ distTriang C →
        G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app (P.openTerm.obj K.carrier) ≫
            (shiftFunctor C (1 : ℤ)).map ac.1.hom = ac.2.hom ≫ δ

/-- Finite-type geometric fibres inherit the Noetherian structure used by the
integral presentation. Source: blueprint proof steps 1 and 12; Stacks 01T6
(blueprint: prop-sf-open-closed-triangle-all-stages).
Proof: finite type is stable under the base change defining the geometric fibre;
a finite-type scheme over the closure field is Noetherian. -/
theorem sfRecollementGeometricNoetherian (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    IsNoetherian (D.geometricFiber X₀).left := by
  have : IsLocallyNoetherian (D.geometricFiber X₀).left := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  have : QuasiCompact (D.geometricFiber X₀).hom := by
    dsimp [FiniteFieldDatum.geometricFiber]
    infer_instance
  have : CompactSpace (D.geometricFiber X₀).left :=
    QuasiCompact.compactSpace_of_compactSpace (D.geometricFiber X₀).hom
  exact ⟨⟩
```

## New

The same declarations, with the same names, signatures and definition bodies, are in
`lean/Sheaf/Paper/SfOpenClosedTriangleData.lean`. The original module reexports them by:

```lean
public import Sheaf.Paper.SfOpenClosedTriangleData
```

New proved API: `sfRecollementModule_closed_adjunction`,
`sfRecollementModuleDirect_exact`, and `sfRecollementModule_shortExact`.
These assert properties of the unchanged constructions. New generic presentation,
restriction and geometric-realization declarations live in new `Sheaf.Paper` modules.
No target definition changes meaning and no semantic target re-review is requested.
The independent reader should verify the extraction and public reexport directly.

## Users

`tools/downstream.py` lists the following 56 transitive consumers. Textual searches for
`SfRecollementPresentation`, `SfIntegralRecollementNormalization`,
`SfRecollementConclusion`, `sfRecollementModuleOpen`, and `sfRecollementModule_exact`
find no downstream direct use beyond this item. Every consumer receives the identical
names and definitions through its existing import; no consumer needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | V9 | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed | Unchanged declarations and public reexports; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Unchanged declarations and public reexports; no adaptation. |

## Status

landed 20261025T043310-L-1694419 2026-10-25 (merge of deliver/R3/Sheaf.Paper.SfOpenClosedTriangleAllStages)
