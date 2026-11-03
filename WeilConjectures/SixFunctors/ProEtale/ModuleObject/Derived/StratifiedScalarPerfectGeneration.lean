/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarPerfectStratification
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
import all WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.ConstructibleSheaf.Devissage
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Finite devissage of stratified scalar-perfect complexes

Source: latest blueprint, internal-Hom stability proof, first paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem perfect_of_iso {X : Scheme.{u}}
    {K L : DerivedCategory (supportModules Λ X)} (e : K ≅ L)
    (hK : IsLocallyConstantPerfectComplex Λ X K) :
    IsLocallyConstantPerfectComplex Λ X L := by
  obtain ⟨U, hU⟩ := hK
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨F, hb, hp, hG, ⟨eF⟩⟩ := hU i
  exact ⟨F, hb, hp, hG, ⟨(upperStar Λ (U.f i)).mapDerivedCategory.mapIso e.symm ≪≫ eF⟩⟩

private theorem perfect_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : DerivedCategory (supportModules Λ X))
    (hK : IsLocallyConstantPerfectComplex Λ X K) :
    IsLocallyConstantPerfectComplex Λ Y ((upperStar Λ f).mapDerivedCategory.obj K) := by
  obtain ⟨U, hU⟩ := hK
  let V := U.pullback₂ f
  refine ⟨V, fun i ↦ ?_⟩
  obtain ⟨F, hb, hp, hG, ⟨eF⟩⟩ := hU i
  let g := pullback.fst (U.f i) f
  let G := upperStarFromPointMod Λ (V.X i)
  let H := upperStarFromPointMod Λ (U.X i)
  have : H.PreservesZeroMorphisms := hG
  refine ⟨F, hb, hp, inferInstance, ⟨?_⟩⟩
  exact ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((upperStarComp Λ (V.f i) f).symm ≪≫
        upperStarCongr Λ (pullback.condition (f := U.f i) (g := f)).symm ≪≫
        upperStarComp Λ g (U.f i)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _).app K ≪≫
      (upperStar Λ g).mapDerivedCategory.mapIso eF ≪≫
      (upperStar Λ g).mapDerivedCategory.mapIso (H.mapDerivedCategoryFactors.app F).symm ≪≫
      ((Functor.mapDerivedCategoryCompIso H (upperStar Λ g)).symm ≪≫
        Functor.mapDerivedCategoryNatIso (upperStarFromPointModComp Λ g)).app
          (DerivedCategory.Q.obj F) ≪≫ G.mapDerivedCategoryFactors.app F

private theorem perfect_reduced_factors_immersion
    {X Y Z : Scheme.{u}} [IsReduced Z] (i : Y ⟶ X) [IsImmersion i]
    (f : Z ⟶ X) (h : Set.range f ⊆ Set.range i) : ∃ g : Z ⟶ Y, g ≫ i = f := by
  let f' := IsOpenImmersion.lift i.coborderRange.ι f
    (h.trans (by
      rw [Scheme.Opens.range_ι]
      change Set.range i ⊆ coborder (Set.range i)
      exact subset_coborder))
  have hf : f' ≫ i.coborderRange.ι = f := IsOpenImmersion.lift_fac _ _ _
  let hr : Set.range f' ⊆ Set.range i.liftCoborder := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := h ⟨z, rfl⟩
    refine ⟨y, i.coborderRange.ι.isEmbedding.injective ?_⟩
    exact (congrArg (fun k : Y ⟶ X ↦ k y) i.liftCoborder_ι).trans
      (hy.trans (congrArg (fun k : Z ⟶ X ↦ k z) hf).symm)
  obtain ⟨g, hg, -⟩ := IsClosedImmersion.existsUnique_fac_of_range_subset_range
    i.liftCoborder f' hr
  exact ⟨g, by rw [← i.liftCoborder_ι, ← Category.assoc, hg, hf]⟩

private theorem perfect_geometric_filtration (T : Scheme.{u}) [IsNoetherian T]
    (s : Scheme.Stratification T) :
    ∃ (n : ℕ) (V : Fin (n + 1) → T.Opens),
      Monotone V ∧ V 0 = ⊥ ∧ V (Fin.last n) = ⊤ ∧
      ∃ (Z : Fin n → Scheme.{u}) (i : ∀ k : Fin n, Z k ⟶ (V k.succ).toScheme),
        (∀ k, IsClosedImmersion (i k) ∧ IsReduced (Z k) ∧
          Set.range (i k) = {x | (V k.succ).ι x ∉ V k.castSucc}) ∧
        ∀ k, ∃ a : Fin s.n, ∃ g : Z k ⟶ s.domain a,
          g ≫ s.immersion a = i k ≫ (V k.succ).ι := by
  classical
  obtain ⟨n, V, hV0, hVn, hstep⟩ := s.toStratification.exists_chain_opens (⊥ : T.Opens)
  change Fin (n + 1) → T.Opens at V
  have hV : Monotone V := Fin.monotone_iff_le_succ.mpr fun k ↦ (hstep k).1
  have hc (k : Fin n) : ∃ (Z : Scheme.{u}) (i : Z ⟶ (V k.succ).toScheme),
      IsClosedImmersion i ∧ IsReduced Z ∧
        Set.range i = {x | (V k.succ).ι x ∉ V k.castSucc} := by
    let U := (V k.succ).ι ⁻¹ᵁ V k.castSucc
    let F : TopologicalSpace.Closeds (V k.succ).toScheme :=
      ⟨(U : Set (V k.succ).toScheme)ᶜ, U.isOpen.isClosed_compl⟩
    have h := Scheme.IdealSheafData.reduced_induced_closed_subscheme _ F
    exact ⟨_, _, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1⟩
  choose Z i hi hred hr using hc
  refine ⟨n, V, hV, hV0, hVn, Z, i, fun k ↦ ⟨hi k, hred k, hr k⟩, ?_⟩
  intro k
  have := hred k
  obtain ⟨a, ha⟩ := (hstep k).2
  have hs : Set.range (i k ≫ (V k.succ).ι) ⊆ Set.range (s.immersion a) := by
    rw [s.range_immersion]
    rintro _ ⟨z, rfl⟩
    apply ha
    refine ⟨by simp, ?_⟩
    have hz : i k z ∈ Set.range (i k) := Set.mem_range_self z
    rw [hr k] at hz
    exact hz
  obtain ⟨g, hg⟩ := perfect_reduced_factors_immersion (s.immersion a) _ hs
  exact ⟨a, g, hg⟩



omit [IsCommMonObj Λ] in
private theorem closed_exact {X Z : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteColimits (lowerStar Λ i) := by
  let U : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact U.ι := noetherian_qc U.ι
  exact closedSupport_lowerStarExact Λ i U.ι (by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm)

private theorem exact_functors_mem
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G H : C ⥤ D) [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : F ⟶ G) (b : G ⟶ H) (hab : a ≫ b = 0)
    (hs : ∀ M, (ShortComplex.mk (a.app M) (b.app M)
      (by simpa using congrArg (fun t ↦ t.app M) hab)).ShortExact)
    (K : DerivedCategory C) (Q : ObjectProperty (DerivedCategory D))
    [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]
    (hF : Q (F.mapDerivedCategory.obj K)) (hH : Q (H.mapDerivedCategory.obj K)) :
    Q (G.mapDerivedCategory.obj K) := by
  let B := (DerivedCategory.Q (C := C)).objPreimage K
  let e := (DerivedCategory.Q (C := C)).objObjPreimageIso K
  let S : ShortComplex (CochainComplex D ℤ) := ShortComplex.mk
    ((NatTrans.mapHomologicalComplex a (.up ℤ)).app B)
    ((NatTrans.mapHomologicalComplex b (.up ℤ)).app B) (by
      ext n
      simpa using congrArg (fun t ↦ t.app (B.X n)) hab)
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact S
    (fun n ↦ hs (B.X n))
  let eF := F.mapDerivedCategory.mapIso e.symm ≪≫ F.mapDerivedCategoryFactors.app B
  let eG := G.mapDerivedCategory.mapIso e.symm ≪≫ G.mapDerivedCategoryFactors.app B
  let eH := H.mapDerivedCategory.mapIso e.symm ≪≫ H.mapDerivedCategoryFactors.app B
  exact Q.prop_of_iso eG.symm (Q.ext_of_isTriangulatedClosed₂
    (DerivedCategory.triangleOfSES hS) (DerivedCategory.triangleOfSES_distinguished hS)
    (Q.prop_of_iso eF hF) (Q.prop_of_iso eH hH))

private theorem extension_compare {S X : Scheme.{u}} [IsNoetherian X]
    {a : S ⟶ X} (A B : GeneratorFactorization a) :
    Nonempty (generatorExtension Λ A ≅ generatorExtension Λ B) := by
  let F := generatorExtension Λ A
  let G := generatorExtension Λ B
  let R := upperStar Λ a
  have := generatorRestriction_isIso Λ A
  have := generatorRestriction_isIso Λ B
  let ηF : F ⋙ R ≅ 𝟭 _ := asIso (generatorRestriction Λ A)
  let ηG : G ⋙ R ≅ 𝟭 _ := asIso (generatorRestriction Λ B)
  have he (M : supportModules Λ S) : ∃ e : F.obj M ≅ G.obj M,
      R.map e.hom ≫ ηG.hom.app M = ηF.hom.app M := by
    obtain ⟨e⟩ := generatorExtension_reconstruct Λ B (F.obj M)
      (fun g hg ↦ generatorExtension_support Λ A g hg M)
    exact normalized_comparison_of_essImage G R (generatorExtension_fullyFaithful Λ B)
      ηG (F.obj M) M ⟨_, ⟨e⟩⟩ (ηF.app M)
  choose e he using he
  refine ⟨NatIso.ofComponents e (fun {M N} f ↦ ?_)⟩
  apply restrict_hom_injective_of_iso G R (generatorExtension_fullyFaithful Λ B) ηG
    (e M) (Iso.refl _)
  apply (Iso.cancel_iso_hom_right _ _ (ηG.app N)).1
  change R.map (F.map f ≫ (e N).hom) ≫ ηG.hom.app N =
    R.map ((e M).hom ≫ G.map f) ≫ ηG.hom.app N
  simp only [Functor.map_comp, Category.assoc]
  have hn : R.map (G.map f) ≫ ηG.hom.app N = ηG.hom.app M ≫ f :=
    ηG.hom.naturality f
  rw [he N, hn]
  simp only [← Category.assoc, he M]
  exact ηF.hom.naturality f

omit [IsCommMonObj Λ] in
private theorem empty_derived_zero (X : Scheme.{u}) [IsEmpty X]
    (K : DerivedCategory (supportModules Λ X)) : IsZero K := by
  apply (DerivedCategory.isZero_iff K).2
  intro n
  exact module_zero_of_empty _ _


/-- Open--closed localization gives finite triangulated generation from a scalar-perfect
stratification. Only finite extensions and isomorphisms are used.
Source: latest blueprint, internal-Hom stability, first proof paragraph
(blueprint: lem-sfb-stratified-scalar-perfect-generation).

Proof: refine the given stratification by a chain of opens from the empty open to X.
Give each difference its reduced closed structure inside the larger open. Its reduced
scheme factors through an original stratum, so pullback preserves its perfect scalar
models. Apply the natural open--closed short exact sequence to each degree of a
representative complex, then extend exactly to X. Its derived triangle has as third
term the extension of the restriction to that difference. Support reconstruction
identifies the two orders of open/closed extension. Induction along the finite chain
starts at the zero object and ends at the original complex. -/
theorem scalarPerfectStratification_generation (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (supportModules Λ X)) (hK : HasScalarPerfectStratification Λ X K)
    (Q : ObjectProperty (DerivedCategory (supportModules Λ X)))
    [Q.IsTriangulated] [Q.IsClosedUnderIsomorphisms]
    (hQ : ∀ (S Z : Scheme.{u}) (j : S ⟶ Z) (i : Z ⟶ X)
      [IsOpenImmersion j] [IsClosedImmersion i]
      (P : DerivedCategory (supportModules Λ S)),
      IsLocallyConstantPerfectComplex Λ S P →
      Q (((openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        (lowerStar Λ i).rightDerivedFunctor).obj P)) : Q K := by
  classical
  obtain ⟨s, hs⟩ := hK
  obtain ⟨n, V, hV, hV0, hVn, Z, i, hi, hg⟩ := perfect_geometric_filtration X s
  have hnoeth (r : Fin (n + 1)) : IsNoetherian (V r).toScheme := by
    have : TopologicalSpace.NoetherianSpace (V r).toScheme :=
      (V r).ι.isEmbedding.isInducing.noetherianSpace
    exact ⟨⟩
  let F (r : Fin (n + 1)) := upperStar Λ (V r).ι ⋙ openImmersionLowerShriek Λ (V r).ι
  have hF (r : Fin (n + 1)) : Q ((F r).mapDerivedCategory.obj K) := by
    induction r using Fin.induction with
    | zero =>
      have : IsEmpty (V 0).toScheme := by
        rw [hV0]
        exact ⟨fun x ↦ x.property⟩
      exact Q.prop_of_iso ((Functor.mapDerivedCategoryCompIso _ _).app K).symm
        (Q.prop_of_isZero ((openImmersionLowerShriek Λ (V 0).ι).mapDerivedCategory.map_isZero
          (empty_derived_zero Λ _ _)))
    | succ r ih =>
      have : IsNoetherian (V r.succ).toScheme := hnoeth _
      have : IsClosedImmersion (i r) := (hi r).1
      have : IsReduced (Z r) := (hi r).2.1
      have : TopologicalSpace.NoetherianSpace (V r.castSucc).toScheme :=
        (V r.castSucc).ι.isEmbedding.isInducing.noetherianSpace
      have : QuasiCompact (V r.castSucc).ι := noetherian_qc _
      have : QuasiCompact (V r.succ).ι := noetherian_qc _
      have : QuasiCompact ((V r.succ).ι ⁻¹ᵁ V r.castSucc).ι := by
        have : TopologicalSpace.NoetherianSpace
            (((V r.succ).ι ⁻¹ᵁ V r.castSucc).toScheme) :=
          ((V r.succ).ι ⁻¹ᵁ V r.castSucc).ι.isEmbedding.isInducing.noetherianSpace
        exact noetherian_qc _
      have : PreservesFiniteColimits (lowerStar Λ (i r)) := closed_exact Λ (i r)
      obtain ⟨d, hd, ⟨ed⟩⟩ := exists_openFiltrationSuccessor Λ _ _
        (hV (Fin.castSucc_le_succ r)) (i r) (hi r).2.2
      have hdmono (M : supportModules Λ X) : Mono (d.app M) := by
        have := mono_condensed_counit Λ (V r.castSucc).ι M
        exact mono_of_mono_fac (congrArg (fun t ↦ t.app M) hd)
      have : Mono d := NatTrans.mono_of_mono_app d
      let H := upperStar Λ (V r.succ).ι ⋙ upperStar Λ (i r) ⋙
        lowerStar Λ (i r) ⋙ openImmersionLowerShriek Λ (V r.succ).ι
      have : (cokernel d).Additive := Functor.additive_of_iso ed.symm
      have : PreservesFiniteLimits (cokernel d) := preservesFiniteLimits_of_natIso ed.symm
      have : PreservesFiniteColimits (cokernel d) :=
        preservesFiniteColimits_of_natIso ed.symm
      let a := i r ≫ (V r.succ).ι
      have : IsImmersion a := inferInstance
      have : QuasiCompact a := by
        have : TopologicalSpace.NoetherianSpace (Z r) :=
          (i r).isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
        exact noetherian_qc a
      let A : GeneratorFactorization a :=
        .inl ⟨(V r.succ).toScheme, i r, (V r.succ).ι, rfl, inferInstance, inferInstance⟩
      let B : GeneratorFactorization a :=
        .inr ⟨a.image, a.toImage, a.imageι, a.toImage_imageι,
          inferInstance, inferInstance⟩
      have : PreservesFiniteColimits (lowerStar Λ a.imageι) := closed_exact Λ a.imageι
      have : (generatorExtension Λ A).Additive := by
        change (lowerStar Λ (i r) ⋙ openImmersionLowerShriek Λ (V r.succ).ι).Additive
        infer_instance
      have : (generatorExtension Λ B).Additive := by
        change (openImmersionLowerShriek Λ a.toImage ⋙ lowerStar Λ a.imageι).Additive
        infer_instance
      have : PreservesFiniteLimits (generatorExtension Λ A) := by
        change PreservesFiniteLimits
          (lowerStar Λ (i r) ⋙ openImmersionLowerShriek Λ (V r.succ).ι)
        infer_instance
      have : PreservesFiniteColimits (generatorExtension Λ A) := by
        change PreservesFiniteColimits
          (lowerStar Λ (i r) ⋙ openImmersionLowerShriek Λ (V r.succ).ι)
        infer_instance
      have : PreservesFiniteLimits (generatorExtension Λ B) := by
        change PreservesFiniteLimits
          (openImmersionLowerShriek Λ a.toImage ⋙ lowerStar Λ a.imageι)
        infer_instance
      have : PreservesFiniteColimits (generatorExtension Λ B) := by
        change PreservesFiniteColimits
          (openImmersionLowerShriek Λ a.toImage ⋙ lowerStar Λ a.imageι)
        infer_instance
      let P := (upperStar Λ (i r)).mapDerivedCategory.obj
        ((upperStar Λ (V r.succ).ι).mapDerivedCategory.obj K)
      obtain ⟨b, g, hga⟩ := hg r
      have hP : IsLocallyConstantPerfectComplex Λ (Z r) P := by
        apply perfect_of_iso Λ ((Functor.mapDerivedCategoryCompIso _ _).app K)
        apply perfect_of_iso Λ ((Functor.mapDerivedCategoryNatIso
          ((upperStarComp Λ (i r) (V r.succ).ι).symm ≪≫
            (upperStarCongr Λ hga).symm ≪≫ upperStarComp Λ g (s.immersion b))).symm.app K)
        apply perfect_of_iso Λ ((Functor.mapDerivedCategoryCompIso _ _).app K).symm
        exact perfect_pullback Λ g _ (hs b)
      have hB := hQ (Z r) a.image a.toImage a.imageι P hP
      have hB' : Q ((generatorExtension Λ B).mapDerivedCategory.obj P) := by
        exact Q.prop_of_iso ((Functor.mapDerivedCategoryCompIso _ _).app P).symm
          (Q.prop_of_iso ((lowerStar Λ a.imageι).rightDerivedFunctorIsoMapDerivedCategory.app
            ((openImmersionLowerShriek Λ a.toImage).mapDerivedCategory.obj P)) hB)
      obtain ⟨e⟩ := extension_compare Λ A B
      have hA := Q.prop_of_iso ((Functor.mapDerivedCategoryNatIso e).app P).symm hB'
      have hH : Q (H.mapDerivedCategory.obj K) := by
        exact Q.prop_of_iso
          ((Functor.mapDerivedCategoryCompIso _ _).app K ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).app
              ((upperStar Λ (V r.succ).ι).mapDerivedCategory.obj K)).symm hA
      have hC := Q.prop_of_iso ((Functor.mapDerivedCategoryNatIso ed).app K).symm hH
      let SC := ShortComplex.mk d (cokernel.π d) (cokernel.condition d)
      have hSC : SC.ShortExact := { exact := ShortComplex.exact_cokernel d }
      exact exact_functors_mem (F r.castSucc) (F r.succ) (cokernel d)
        d (cokernel.π d) (cokernel.condition d)
        (fun M ↦ hSC.map_of_exact ((evaluation _ _).obj M)) K Q ih hC
  have : IsIso (V (Fin.last n)).ι := by
    rw [hVn]
    exact inferInstanceAs (IsIso X.topIso.hom)
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction Λ (V (Fin.last n)).ι).counit :=
    by
      have (M : supportModules Λ X) := iso_condensed_counit Λ (V (Fin.last n)).ι M
      exact NatIso.isIso_of_isIso_app _
  exact Q.prop_of_iso
    ((Functor.mapDerivedCategoryNatIso
      (asIso (openImmersionLowerShriekUpperStarAdjunction Λ (V (Fin.last n)).ι).counit) ≪≫
        Functor.mapDerivedCategoryIdIso _).app K) (hF (Fin.last n))

end AlgebraicGeometry.ProEtale.CondensedRing
