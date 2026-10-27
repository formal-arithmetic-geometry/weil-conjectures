/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q20 and E6
-/
module

public import Sheaf.Paper.ContinuousRationalRealizationData
import Sheaf.Paper.RationalModuleRealizationFunctor
import Sheaf.Paper.ConstructibleRationalHomComparison
import Sheaf.Paper.RationalContinuousFiniteFreeCriterion
import Sheaf.Paper.RationalContinuousFiltrationModels
import Sheaf.Paper.RationalContinuousPullbackTransport
import Sheaf.Paper.RationalContinuousSliceTransport
import Sheaf.Paper.RationalContinuousComparisonCoherence
import Sheaf.Paper.RationalRealizationScalarCoherence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.CategoryTheory.Triangulated.CohomologyComparisonPasting

/-! # Continuous rational derived realization

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15
(blueprint: lem-per-continuous-rational-derived-realization).

The data declarations are reexported from `ContinuousRationalRealizationData`.
-/


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] pbcRationalCoefficientEquiv pbcIntegralDatum
  reductionDerivedChange completedAdicDerivedChange
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory

section Ambient

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

private def ambientCohomologyIso (q : ℤ) :
    DerivedCategory.TStructure.t.truncGELE q q ⋙ shiftFunctor (DerivedCategory C) q ≅
      DerivedCategory.homologyFunctor C q ⋙ DerivedCategory.singleFunctor C 0 := by
  let t := DerivedCategory.TStructure.t (C := C)
  let Φ := t.truncGELE q q
  let S := DerivedCategory.singleFunctor C q
  let H := DerivedCategory.homologyFunctor C q
  have hΦ : ∀ X, S.essImage (Φ.obj X) := by
    intro X
    let M := Φ.obj X
    have : M.IsLE q := inferInstanceAs (t.IsLE M q)
    have : M.IsGE q := inferInstanceAs (t.IsGE M q)
    obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE M q
    exact ⟨Y, ⟨e.symm⟩⟩
  let L := S.essImage.lift Φ hΦ
  let Φ' := L ⋙ S.toEssImage.inv
  let e₁ : Φ' ⋙ S ≅ Φ :=
    Functor.isoWhiskerLeft L (Functor.isoWhiskerLeft S.toEssImage.inv S.toEssImageCompι.symm ≪≫
      Functor.isoWhiskerRight S.toEssImage.asEquivalence.counitIso S.essImage.ι ≪≫
      Functor.leftUnitor _) ≪≫ S.essImage.liftCompιIso Φ hΦ
  let e₂ : Φ ⋙ H ≅ Φ' :=
    Functor.isoWhiskerRight e₁.symm H ≪≫
      Functor.isoWhiskerLeft Φ' (DerivedCategory.singleFunctorCompHomologyFunctorIso C q) ≪≫
        Functor.rightUnitor _
  let α : t.truncLE q ⋙ H ⟶ H := Functor.whiskerRight (t.truncLEι q) H
  let β : t.truncLE q ⋙ H ⟶ Φ ⋙ H :=
    Functor.whiskerLeft (t.truncLE q) (Functor.whiskerRight (t.truncGEπ q) H)
  have (X : DerivedCategory C) : IsIso (α.app X) := by
    dsimp [α]
    have h := DerivedCategory.isIso_homologyFunctor_map_truncLTι_app X (q + 1) q (by omega)
    have eq : (t.truncLEι q).app X =
        ((t.truncLEIsoTruncLT q (q + 1) rfl).app X).hom ≫
          (t.truncLTι (q + 1)).app X := by
      simp
    rw [eq, H.map_comp]
    infer_instance
  have (X : DerivedCategory C) : IsIso (β.app X) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app _ q q le_rfl
  have : IsIso α := NatIso.isIso_of_isIso_app _
  have : IsIso β := NatIso.isIso_of_isIso_app _
  let e : Φ ≅ H ⋙ S :=
    e₁.symm ≪≫ Functor.isoWhiskerRight (e₂.symm ≪≫ (asIso β).symm ≪≫ asIso α) S
  exact Functor.isoWhiskerRight e (shiftFunctor _ q) ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft H ((DerivedCategory.singleFunctors C).shiftIso q 0 q (by omega))

end Ambient

private def coefficientEncoding (X : Scheme.{u}) :
    AlgebraicGeometry.ProEtale.latticeCoefficientSheaf X
      (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅
      rationalCoefficientSheaf l X E := by
  let := coefficientExtensionNormedField l E
  let e := WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E)
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  have hei : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  exact
    { hom := ⟨{
        app := fun _ ↦ CommRingCat.ofHom
          { toFun := fun f ↦ ⟨fun x ↦ ULift.up (e (f.down x)),
                continuous_uliftUp.comp (he.continuous.comp f.down.continuous)⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun _ ↦ CommRingCat.ofHom
          { toFun := fun f ↦ ULift.up ⟨fun x ↦ e.symm (f x).down,
                hei.continuous.comp (continuous_uliftDown.comp f.continuous)⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by ext V f; rfl
      inv_hom_id := by ext V f; rfl }

private theorem coefficientEncoding_normalization (X : Scheme.{u}) (U : X.ProEtᵒᵖ)
    (f : C(U.unop.left, WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))
    (x : U.unop.left) :
    rationalCoefficientValue l E X U ((coefficientEncoding l E X).hom.hom.app U (ULift.up f)) x
      = WithAbs.ofAbs (f x) := by
  rfl

private theorem constant_normalization (X : Base.{u} l) (U : X.scheme.ProEtᵒᵖ) (a : E) :
    (rationalModuleConstantMap l E X.scheme).hom.app U
      ((toSheafify (ProEt.topology X.scheme)
        ((Functor.const X.scheme.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))).app U
          (ULift.up a)) =
      (scalarSections l E X.scheme a).val U := by
  change (((toSheafify (ProEt.topology X.scheme)
      ((Functor.const X.scheme.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} E)))) ≫
        (rationalModuleConstantMap l E X.scheme).hom).app U) (ULift.up a) = _
  change ((((sheafificationAdjunction (ProEt.topology X.scheme)
    CommRingCat.{u + 1}).homEquiv _ _)
      (rationalModuleConstantMap l E X.scheme)).app U) (ULift.up a) = _
  rw [rationalModuleConstantMap, Equiv.apply_symm_apply]
  rfl
private theorem realizationLinear_eq (X : Base.{u} l) (s : RationalModuleRealization l E X.scheme) :
    s.moduleLinear = moduleLinear l E X.scheme := by
  have h : s.moduleLinear.homModule = (moduleLinear l E X.scheme).homModule := by
    funext M N
    apply Module.ext'
    intro a f
    apply SheafOfModules.hom_ext
    ext U x
    exact (s.scalar_normalization M N f a U x).trans (by
      rw [constant_normalization l E X]
      rfl)
  have ext (a b : Linear E (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)))
      (h : a.homModule = b.homModule) : a = b := by
    cases a
    cases b
    cases h
    rfl
  exact ext _ _ h

set_option backward.isDefEq.respectTransparency true in
private def realizationIntegralComparison (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (s : RationalModuleRealization l E X) :
    pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙ s.J ≅
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) ⋙
        pbcDerivedExtend (s.integralIso.hom ≫ s.inclusion) := by
  letI := s.moduleLinear
  letI : Linear E (DerivedCategory (pbcModules X (rationalCoefficientSheaf l X E))) :=
    DerivedCategory.instLinear E _
  refine NatIso.ofComponents (fun K ↦ eqToIso (s.objects K)) ?_
  intro K L f
  have h := s.fractions K L f 0
  simp only [pow_zero, inv_one, map_one, one_smul] at h
  change s.J.map ((pbcRationalization X (pbcIntegralDatum l E)
    (pbcUniformizer l E)).map f) ≫ eqToHom (s.objects L) =
      eqToHom (s.objects K) ≫
        (pbcDerivedExtend (s.integralIso.hom ≫ s.inclusion)).map f.hom
  rw [h]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem preserve0 (X : Base.{u} l)
    (s : RationalModuleRealization l E X.scheme)
    (K : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)) :
    ((localizedT l E X).le 0 K → (s.J.obj K).IsLE 0) ∧
      ((localizedT l E X).ge 0 K → (s.J.obj K).IsGE 0) := by
  let t := localizedT l E X
  let B := pbcAdicCompletion X.scheme (pbcIntegralDatum l E)
  let R := rationalCoefficientSheaf l X.scheme E
  let φ := s.integralIso.hom ≫ s.inclusion
  have := s.ordinary_exact.1
  have := s.ordinary_exact.2
  have hz (L : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)) (r : ℤ)
      (h : IsZero ((DerivedCategory.homologyFunctor _ r).obj L.obj)) :
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        (s.J.obj ((pbcRationalization X.scheme (pbcIntegralDatum l E)
          (pbcUniformizer l E)).obj L))) := by
    let a := (s.cohomology r).app L.obj
    have he : s.J.obj ((pbcRationalization X.scheme (pbcIntegralDatum l E)
        (pbcUniformizer l E)).obj L) = (pbcDerivedExtend φ).obj L.obj := s.objects L
    rw [he]
    exact ((pbcExtend φ).map_isZero h).of_iso a
  constructor
  · intro hk
    obtain ⟨L, hL, ⟨e⟩⟩ := (pbc_localized_tstructure X.scheme l E).choose_spec.1 K |>.1.mp hk
    have hL' : L.obj.IsLE 0 :=
      (ObjectProperty.tStructure_isLE_iff
        (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))
        (pbcAmbientTStructure X.scheme l E) L 0).mp ⟨hL⟩
    have hq : (s.J.obj ((pbcRationalization X.scheme (pbcIntegralDatum l E)
        (pbcUniformizer l E)).obj L)).IsLE 0 :=
      (DerivedCategory.isLE_iff _ _).mpr (fun r hr ↦
        hz L r (DerivedCategory.isZero_of_isLE L.obj 0 r hr))
    exact DerivedCategory.TStructure.t.isLE_of_iso (s.J.mapIso e).symm 0
  · intro hk
    obtain ⟨L, hL, ⟨e⟩⟩ := (pbc_localized_tstructure X.scheme l E).choose_spec.1 K |>.2.mp hk
    have hL' : L.obj.IsGE 0 :=
      (ObjectProperty.tStructure_isGE_iff
        (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))
        (pbcAmbientTStructure X.scheme l E) L 0).mp ⟨hL⟩
    have hq : (s.J.obj ((pbcRationalization X.scheme (pbcIntegralDatum l E)
        (pbcUniformizer l E)).obj L)).IsGE 0 :=
      (DerivedCategory.isGE_iff _ _).mpr (fun r hr ↦
        hz L r (DerivedCategory.isZero_of_isGE L.obj 0 r hr))
    exact DerivedCategory.TStructure.t.isGE_of_iso (s.J.mapIso e).symm 0

private theorem preserve (X : Base.{u} l)
    (s : RationalModuleRealization l E X.scheme)
    (K : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
    (r : ℤ) :
    ((localizedT l E X).le r K → (s.J.obj K).IsLE r) ∧
      ((localizedT l E X).ge r K → (s.J.obj K).IsGE r) := by
  let t := localizedT l E X
  let a := DerivedCategory.TStructure.t (C :=
    pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
  have := s.shift
  constructor
  · intro hk
    have hk' : t.IsLE K r := ⟨hk⟩
    have hshift : t.IsLE (K⟦r⟧) 0 := t.isLE_shift K r r 0 (by omega)
    have hj : a.IsLE (s.J.obj (K⟦r⟧)) 0 :=
      (preserve0 l E X s (K⟦r⟧)).1 hshift.le
    have hq : a.IsLE ((s.J.obj K)⟦r⟧) 0 :=
      a.isLE_of_iso (show s.J.obj (K⟦r⟧) ≅ (s.J.obj K)⟦r⟧ from
        (s.J.commShiftIso r).app K) 0
    exact (a.isLE_of_shift (s.J.obj K) r r 0 (by omega))
  · intro hk
    have hk' : t.IsGE K r := ⟨hk⟩
    have hshift : t.IsGE (K⟦r⟧) 0 := t.isGE_shift K r r 0 (by omega)
    have hj : a.IsGE (s.J.obj (K⟦r⟧)) 0 :=
      (preserve0 l E X s (K⟦r⟧)).2 hshift.ge
    have hq : a.IsGE ((s.J.obj K)⟦r⟧) 0 :=
      a.isGE_of_iso (show s.J.obj (K⟦r⟧) ≅ (s.J.obj K)⟦r⟧ from
        (s.J.commShiftIso r).app K) 0
    exact (a.isGE_of_shift (s.J.obj K) r r 0 (by omega))

private theorem realizationBounds (X : Base.{u} l)
    (s : RationalModuleRealization l E X.scheme) (hs : s.J.FullyFaithful)
    (K : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E))
    (r : ℤ) :
    ((localizedT l E X).le r K ↔ (s.J.obj K).IsLE r) ∧
      ((localizedT l E X).ge r K ↔ (s.J.obj K).IsGE r) := by
  let t := localizedT l E X
  let a := DerivedCategory.TStructure.t (C :=
    pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
  have := hs.faithful
  have := s.additive
  have : s.J.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive _
  constructor
  · refine ⟨(preserve l E X s K r).1, fun hk ↦ ?_⟩
    have h : t.IsLE K r := (t.isLE_iff_orthogonal r (r + 1) rfl K).mpr (by
      intro Y f hY
      have hy := (preserve l E X s Y (r + 1)).2 hY.ge
      apply s.J.map_injective
      rw [s.J.map_zero]
      exact a.zero (s.J.map f) r (r + 1) (by omega))
    exact h.le
  · refine ⟨(preserve l E X s K r).2, fun hk ↦ ?_⟩
    have h : t.IsGE K r := (t.isGE_iff_orthogonal (r - 1) r (by omega) K).mpr (by
      intro Y f hY
      have hy := (preserve l E X s Y (r - 1)).1 hY.le
      apply s.J.map_injective
      rw [s.J.map_zero]
      exact a.zero (s.J.map f) (r - 1) r (by omega))
    exact h.ge


private theorem realizationImage (X : Base.{u} l)
    (s : RationalModuleRealization l E X.scheme)
    (hf : s.J.Full) (hi : s.J.Faithful)
    (C : DerivedCategory (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))) :
    IsDerivedConstructible l E X.scheme (coefficientEncoding l E X.scheme) C ↔
      ∃ K, Nonempty (s.J.obj K ≅ C) := by
  have criterion := rationalContinuousFiniteFreeCriterion l E X
    (coefficientEncoding l E X.scheme) (coefficientEncoding_normalization l E X.scheme)
  constructor
  · rintro ⟨⟨a, b, ha, hb⟩, hc⟩
    have := ha
    have := hb
    obtain ⟨_, K, _, ⟨e⟩, _⟩ := RationalConeModels.bounded_model l E X.scheme s hf hi
      (fun F hF ↦ rationalContinuousFiltrationModels l E X s F hF) C a b
      (fun r hr ↦ hr.elim
        (fun h ↦ DerivedCategory.isZero_of_isGE C a r h)
        (fun h ↦ DerivedCategory.isZero_of_isLE C b r h))
      (fun r ↦ (criterion _).mp (hc r))
    exact ⟨(pbcRationalization X.scheme (pbcIntegralDatum l E)
      (pbcUniformizer l E)).obj K, ⟨e⟩⟩
  · rintro ⟨⟨K⟩, ⟨e⟩⟩
    obtain ⟨⟨a, b, ha, hb⟩, hc⟩ := s.constructible K
    let q : (pbcDerivedExtend (s.integralIso.hom ≫ s.inclusion)).obj K.obj ≅ C :=
      (eqToIso (s.objects K)).symm ≪≫ e
    have := ha
    have := hb
    refine ⟨⟨a, b, DerivedCategory.TStructure.t.isGE_of_iso q a,
      DerivedCategory.TStructure.t.isLE_of_iso q b⟩, fun r ↦ ?_⟩
    apply (criterion _).mpr
    obtain ⟨t, ht⟩ := hc r
    refine ⟨t, fun j ↦ ?_⟩
    have := ht j
    exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1}
      ((proEtaleModuleInverseImage (t.immersion j)
        (rationalCoefficientSheaf l X.scheme E)).mapIso
          ((DerivedCategory.homologyFunctor _ r).mapIso q))

private theorem realizationHeart (X : Base.{u} l)
    (s : RationalModuleRealization l E X.scheme) (hs : s.J.FullyFaithful)
    (hf : s.J.Full) (hi : s.J.Faithful)
    (K : PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)) :
    (localizedT l E X).heart K ↔
      ∃ F : pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E),
        IsConstructible l E X.scheme (coefficientEncoding l E X.scheme) F ∧
          Nonempty (s.J.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj F) := by
  constructor
  · intro hK
    have hle := (realizationBounds l E X s hs K 0).1.mp hK.1
    have hge := (realizationBounds l E X s hs K 0).2.mp hK.2
    have := hle
    have := hge
    obtain ⟨F, ⟨e⟩⟩ :=
      DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (s.J.obj K) 0
    have hc := (realizationImage l E X s hf hi _).mpr ⟨K, ⟨e⟩⟩
    have hc0 := hc.2 0
    have q := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)) 0).app F
    have criterion := rationalContinuousFiniteFreeCriterion l E X
      (coefficientEncoding l E X.scheme) (coefficientEncoding_normalization l E X.scheme)
    obtain ⟨t, ht⟩ := (criterion _).mp hc0
    refine ⟨F, (criterion _).mpr ⟨t, fun j ↦ ?_⟩, ⟨e⟩⟩
    have hq : ((proEtaleModuleInverseImage (t.immersion j)
        (rationalCoefficientSheaf l X.scheme E)).obj
        ((DerivedCategory.homologyFunctor _ 0).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))).IsFiniteLocallyFree := ht j
    exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1} (h := hq)
      ((proEtaleModuleInverseImage (t.immersion j)
        (rationalCoefficientSheaf l X.scheme E)).mapIso q)
  · rintro ⟨F, _, ⟨e⟩⟩
    have hle : (s.J.obj K).IsLE 0 :=
      DerivedCategory.TStructure.t.isLE_of_iso e.symm 0
    have hge : (s.J.obj K).IsGE 0 :=
      DerivedCategory.TStructure.t.isGE_of_iso e.symm 0
    exact ⟨(realizationBounds l E X s hs K 0).1.mpr hle,
      (realizationBounds l E X s hs K 0).2.mpr hge⟩

private def realizationCohomology (X : Base.{u} l)
    (s : RationalModuleRealization l E X.scheme) (hs : s.J.FullyFaithful) (r : ℤ) :
    pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
        localizedCohomology l E X r ⋙ s.J ≅
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E)) ⋙
        DerivedCategory.homologyFunctor
          (pbcModules X.scheme (pbcAdicCompletion X.scheme (pbcIntegralDatum l E))) r ⋙
        pbcExtend (s.integralIso.hom ≫ s.inclusion) ⋙
          DerivedCategory.singleFunctor _ 0 := by
  let t := localizedT l E X
  let ta := DerivedCategory.TStructure.t (C :=
    pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E))
  have := s.triangulated
  letI : s.J.IsTExact t ta :=
    ⟨fun K n h ↦ (realizationBounds l E X s hs K n).1.mp h.le,
      fun K n h ↦ (realizationBounds l E X s hs K n).2.mp h.ge⟩
  let H := ta.truncGELE r r ⋙ shiftFunctor _ r
  let q : localizedCohomology l E X r ⋙ s.J ≅ s.J ⋙ H :=
    Triangulated.TStructure.truncationCohomologyComparison t ta s.J r
  let Q := pbcRationalization X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E)
  let S := DerivedCategory.singleFunctor
    (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)) 0
  let Hr := DerivedCategory.homologyFunctor
    (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme E)) r
  let i := ObjectProperty.ι
    (PbcIsBoundedConstructibleComplete X.scheme (pbcIntegralDatum l E))
  let D := pbcDerivedExtend (s.integralIso.hom ≫ s.inclusion)
  exact Functor.isoWhiskerLeft Q q ≪≫
    Functor.isoWhiskerLeft Q (Functor.isoWhiskerLeft s.J (ambientCohomologyIso r)) ≪≫
    (Functor.associator Q s.J (Hr ⋙ S)).symm ≪≫
    Functor.isoWhiskerRight (realizationIntegralComparison l E X.scheme s) (Hr ⋙ S) ≪≫
    Functor.associator i D (Hr ⋙ S) ≪≫
    Functor.isoWhiskerLeft i ((Functor.associator D Hr S).symm ≪≫
      Functor.isoWhiskerRight (s.cohomology r) S ≪≫ Functor.associator _ _ _)

private def realizationAt (X : Base.{u} l)
    (s : RationalModuleRealization l E X.scheme) : At l E X := by
  have hcomparison := (constructibleRationalHomComparison l E X.scheme).2 s
  have hf := hcomparison.2.1
  have hi := hcomparison.2.2
  have := hf
  have := hi
  let hs := Functor.FullyFaithful.ofFullyFaithful s.J
  have hlin : s.J.Linear E := by
    have h := s.linear
    rw [realizationLinear_eq l E X s] at h
    exact h
  have := hlin
  exact
    { topNoetherian := inferInstance
      encoding := coefficientEncoding l E X.scheme
      encoding_normalization := coefficientEncoding_normalization l E X.scheme
      strata_criterion := rationalContinuousFiniteFreeCriterion l E X
        (coefficientEncoding l E X.scheme) (coefficientEncoding_normalization l E X.scheme)
      integralIso := s.integralIso
      finiteIso := s.finiteIso
      finite_normalization := s.finite_normalization
      integral_normalization := s.integral_normalization
      localizationIso := s.localizationIso
      localization_normalization := s.localization_normalization
      inclusion := s.inclusion
      inclusion_normalization := s.inclusion_normalization
      J := s.J
      additive := s.additive
      linear := hlin
      shift := s.shift
      triangulated := s.triangulated
      fully_faithful := fun K L ↦ hs.map_bijective K L
      image := realizationImage l E X s hf hi
      integral := realizationIntegralComparison l E X.scheme s
      fractions := fun K L f a ↦ by
        have h : a • (pbcRationalization X.scheme (pbcIntegralDatum l E)
            (pbcUniformizer l E)).map f =
            (pbcRationalCoefficientEquiv l E a) •
              (pbcRationalization X.scheme (pbcIntegralDatum l E)
                (pbcUniformizer l E)).map f := by
          let M := (pbcRationalization X.scheme (pbcIntegralDatum l E)
            (pbcUniformizer l E)).obj K
          let N := (pbcRationalization X.scheme (pbcIntegralDatum l E)
            (pbcUniformizer l E)).obj L
          let action := Module.compHom (M ⟶ N) (pbcRationalCoefficientEquiv l E).symm.toRingHom
          change a • _ = @SMul.smul E (M ⟶ N) action.toSMul
            ((pbcRationalCoefficientEquiv l E) a) _
          change a • _ = (pbcRationalCoefficientEquiv l E).symm
            ((pbcRationalCoefficientEquiv l E) a) • _
          rw [RingEquiv.symm_apply_apply]
        rw [h, s.J.map_smul]
      t_bounds := realizationBounds l E X s hs
      heart := realizationHeart l E X s hs hf hi
      cohomology := realizationCohomology l E X s hs }

private theorem fieldChange_exists
    (A B : Type u) [Field A] [Field B] [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (X : Base.{u} l)
    (sA : RationalModuleRealization l A X.scheme)
    (sB : RationalModuleRealization l B X.scheme) :
    Nonempty (FieldChange l A B i X (realizationAt l A X sA) (realizationAt l B X sB)) := by
  obtain ⟨b⟩ := rationalRealizationScalarCoherence l A B i X.scheme sA sB
  exact ⟨
    { coefficient := b.coefficient
      normalized := b.coefficient_normalization
      square := by
        simpa only [realizationAt, rationalPullScalar, Category.assoc] using b.coefficient_square
      comparison := by simpa only [realizationAt] using b.theta
      integral_normalization := by
        dsimp only [realizationAt, realizationIntegralComparison,
          NatIso.ofComponents_hom_app, eqToIso.hom, id_eq]
        have general (χ : pbcAdicCompletion X.scheme (pbcIntegralDatum l A) ⟶
            rationalCoefficientSheaf l X.scheme B)
            (hχ : rationalPullScalar l A sA ≫ b.coefficient = χ)
            (hχ' : pbcScalarCoefficientMap l A B i X.scheme ≫
              rationalPullScalar l B sB = χ) :
            ∀ K : PbcBoundedConstructibleComplete X.scheme (pbcIntegralDatum l A),
              b.theta.hom.app ((pbcRationalization X.scheme (pbcIntegralDatum l A)
                  (pbcUniformizer l A)).obj K) ≫
                (pbcDerivedExtend b.coefficient).map (eqToHom (sA.objects K)) ≫
                (pbcReductionNormalization (rationalPullScalar l A sA) b.coefficient
                  χ hχ K.obj).hom =
                eqToHom (sB.objects
                  ((pbcEmbeddingIntegralTensor l A B i X.scheme
                    X.dimension X.prime_unit).obj K)) ≫
                (pbcReductionNormalization (pbcScalarCoefficientMap l A B i X.scheme)
                  (rationalPullScalar l B sB) χ hχ' K.obj).hom := by
          subst χ
          exact b.integral_normalization
        exact general _ (Category.assoc _ _ _) (by
          simpa only [rationalPullScalar, Category.assoc] using b.coefficient_square) }⟩

/-- Continuous rational derived realization, simultaneously with its normalized
pullback, coefficient-extension and site-restriction compatibilities.

Source: Bhatt--Scholze, Proposition 6.8.14(2), Lemma 6.8.2(1), Proposition 6.8.11(3),
Definition 6.8.8, Remark 6.8.15
(blueprint: lem-per-continuous-rational-derived-realization).

Proof plan (the node’s complete steps):

1. Write $\mathcal C_X=D^b_c(X,A)$ for the completed-coefficient category, including its
compatible etale-origin witnesses. The coefficient datum defines
$B_X=\varprojlim_n(A/\varpi^n)_X$ as a ring sheaf with its specified projections. The
continuous-coefficient restriction lemma identifies this ring with $V\mapsto C(|V|,A)$, and
identifies its sheafified localization at $\varpi$ with $V\mapsto C(|V|,E)$. The identifications
preserve constant sections and quotient projections and commute with locally closed restriction.
All categories below are categories of module sheaves over these actual ring sheaves.
Uses: def-weil-pbc-bounded-constructible-complete, def-weil-pbc-adic-coefficient-datum,
lem-weil-pbc-continuous-coefficients-immersion-restriction.

2. The integral stratified-perfect characterization applies to $X$: it assumes exactly a finite
coefficient field, a noetherian finite-dimensional scheme, and invertibility of $\ell$. It says
that $K\in\mathcal C_X$ if and only if $K$ is bounded and its cohomology, on a finite
stratification, is locally $B_S\otimes_A N$ for finitely presented $A$-modules $N$. Equivalently
its local models are $B_S\otimes_A^L P$ with $P$ perfect. In particular it puts such integral
sheaves in degree zero in $\mathcal C_X$, and supplies closure under shifts, cones, truncations
and cohomology. This step concerns the integral category only; it does not yet identify its
rationalization with the target category.
Uses: lem-weil-pbc-integral-stratified-perfect-characterization.

3. Scalar localization of module sheaves is exact by the localization/inverse-image coherence
lemma, applied to the identity geometric morphism with $R=B_X,t=\varpi$. Its termwise derived
functor is $F_X(K)=E_X\otimes^L_{B_X}K$, as also given by derived change of rings. Exactness
implies $\mathcal H^r(F_XK)=E_X\otimes_{B_X}\mathcal H^r(K)$: an exact functor preserves the
kernels, images and quotients defining cohomology. On a stratum $h:S\to X$ the
continuous-coefficient restriction lemma gives $h^{-1}B_X\cong B_S$ and $h^{-1}E_X\cong E_S$,
and the coherence lemma (for $h$) commutes $h^{-1}$ with localization; so on an integral local
model this sheaf is $E_S\otimes_A N$. A finitely presented module over the DVR $A$ has a finite
presentation; after tensoring the presentation with the field $E$, its cokernel is a
finite-dimensional vector space, so the last sheaf is locally finite free. Thus $F_XK$ lies in
$D_{\mathrm{cons}}(X,E_X)$. Since $\varpi$ acts invertibly after $F_X$, the fraction relation
defines $J_X(f/\varpi^n)=\varpi^{-n}F_X(f)$, respecting addition, identities and composition.
Raw scalar localization is triangulated with distinguished triangles isomorphic to integral
image triangles; hence the triangulated functor $F_X$ induces a triangulated $E$-linear functor
$J_X$ into the ambient $D(\operatorname{Mod}(E_X))$.
Uses: lem-weil-pbc-localization-inverse-image-coherence,
lem-weil-pbc-continuous-coefficients-immersion-restriction, lem-pur-derived-change-of-rings,
def-weil-derived-cohomology-sheaves, def-weil-pbc-rational-category,
lem-weil-linear-scalar-localization-triangulated.

4. For $K,L\in\mathcal C_X$, verify the Hom-continuity hypothesis of the scalar-localization Hom
lemma. Integral bounded-below compactness gives the global-derived-Hom coproduct comparison for
every countable family with a common lower bound, including its shift by any integer $q$. Take
$H^0$ and use the global-sections/internal-Hom comparison to identify
$H^0R\operatorname{Hom}(K,M)$ with $\operatorname{Hom}_{D(B_X)}(K,M)$. Countable sums of
$A$-modules are exact, since finite-support coordinates preserve kernels and surjections; their
termwise sums represent derived sums by the countable-sums lemma. Thus $H^0$ of their sum is the
sum of their $H^0$'s. These observations give precisely the Hom/coproduct hypothesis, and
boundedness makes $L$ bounded below. The scalar-localization Hom lemma, with $R=B_X,t=\varpi$,
now gives
$$\operatorname{Hom}_{D(B_X)}(K,L[q])[1/\varpi]\cong\operatorname{Hom}_{D(E_X)}(F_XK,F_XL[q]),\quad
f/\varpi^n\longmapsto\varpi^{-n}F_X(f).$$ At $q=0$ the left side is the raw category's Hom
group. The lemma's identity and composition clauses prove full faithfulness of $J_X$. The target
here is $D(E_X)$, not $D(B_X)$.
Uses: lem-weil-pbc-integral-constructible-bounded-below-compactness,
lem-pur-rhom-global-sections, lem-kun-derived-countable-sums-exact,
lem-weil-pbc-scalar-localization-derived-hom, def-weil-pbc-rational-category.

5. Apply the directed-triangulated-image lemma with the singleton preorder, source the raw
rationalized category, identity transition, and functor $J_X$ to the ambient $D(E_X)$. Step 3
gives a triangulated functor and Step 4 gives every arrow between its image objects an actual
lift; these are the lemma's hypotheses at the unique common stage. Its conclusion makes the
essential image closed under zero, shifts and distinguished triangles. If $L$ is a lisse
$E_X$-sheaf, the lisse-lattice lemma produces a constructible $B_X$-module $N$ with
$E_X\otimes_{B_X}N\cong L$. Step 2 puts $N[0]$ in $\mathcal C_X$, with completeness and
compatible etale origins. Hence all lisse sheaves in degree zero belong to the essential image.
Uses: lem-weil-pbc-directed-triangulated-image,
lem-weil-pbc-lisse-e-constructible-integral-lattice,
lem-weil-pbc-integral-stratified-perfect-characterization.

6. Let $F$ be a constructible $E_X$-module sheaf. To use the finite-model stratum-filtration
tool, take the condensed ring $C(-,E)$. The continuous-coefficient realization identifies its
pulled ring on every scheme with the continuous ring sheaf, naturally for coefficient maps. The
internal/sectionwise module equivalence preserves underlying sheaves and actions. Thus a finite
free model $E_S^r$ is exactly the tool's finite constant local model $E_S\otimes_E E^r$. This
identification is used only for the sheaf filtration, never to infer membership in the completed
integral category. Choose the finite noetherian affine cover of $X$. The affine-noetherian-space
lemma makes each member noetherian. A descending closed chain stabilizes on each of these
finitely many members, hence stabilizes globally. Thus $|X|$ is noetherian, and the filtration
lemma applies and gives a finite filtration of $F$ with quotients $v_{k!}(t_k)_*L_k$, where
$v_k:V_k\hookrightarrow X$ is qcqs open and $t_k:S_k\hookrightarrow V_k$ is reduced closed. Each
local model of $L_k$ is a finitely presented $E$-module, hence a finite-dimensional vector
space; therefore $L_k$ is lisse.
Uses: lem-sfb-finite-model-stratum-filtration, lem-weil-pbc-continuous-coefficient-realizations,
def-weil-pbc-internal-abelian-sheaf-module-equivalence,
lem-sc-affine-noetherian-underlying-space.

7. Each $S_k$ is noetherian, finite-dimensional and $\ell$-coprime: it is closed in the
noetherian open $V_k$, affine rings are quotients of noetherian rings, irreducible closed chains
have the dimension bound from $X$, and the inverse of $\ell$ survives in the quotient local
rings. Choose a constructible integral lattice $N_k$ for $L_k$ by the lisse-lattice lemma. The
ringed open-closed lemma supplies exact $v_{k!}$ and $(t_k)_*$, and their restrictions are $N_k$
on the supporting pieces and zero on the complements. Extending the finite stratification of
$N_k$ by those zero pieces proves $M_k=v_{k!}(t_k)_*N_k$ is an integral constructible sheaf;
Step 2 certifies $M_k[0]\in\mathcal C_X$, including the etale witnesses. Locally closed
coefficient restrictions are the maps of Step 1. Localization is the sequential sheaf colimit of
multiplication by $\varpi$, with fractions as transition classes. It commutes with $v_{k!}$
since that functor is a left adjoint, and with $(t_k)_*$ by the filtered-colimit clause of the
open-closed lemma on the qcqs $V_k$. Module colimits are the underlying abelian sheaf colimits.
Therefore $J_X(QM_k)\cong v_{k!}(t_k)_*L_k$.
Uses: lem-weil-pbc-noetherian-open-subscheme-noetherian,
lem-weil-pbc-lisse-e-constructible-integral-lattice, lem-weil-pbc-proetale-ringed-open-closed,
lem-weil-pbc-integral-stratified-perfect-characterization,
lem-weil-pbc-continuous-coefficients-immersion-restriction,
lem-weil-pbc-module-sheaves-colimits-forgetful, lem-weil-pbc-left-adjoint-preserves-colimits.

8. Induct over the finite filtration of Step 6, beginning with its zero term. Its short exact
sequence $0\to F_{k-1}\to F_k\to v_{k!}(t_k)_*L_k\to0$ is a distinguished triangle in $D(E_X)$
by the short-exact-sequence clause of the heart-triangle lemma for the ambient standard
t-structure. Step 7 and the induction hypothesis put its outer terms in the essential image. The
connecting morphism lifts by full faithfulness, and the cone closure in Step 5 puts $F_k$ in the
image. This proves that every constructible $E_X$-sheaf in degree zero has an integral derived
model; it does not assert a globally lisse integral lattice.
Uses: lem-weil-heart-short-exact-triangles, def-sbc-standard-tstructure-derived-category.

9. For $C\in D_{\mathrm{cons}}(X,E_X)$ choose a finite cohomological interval $[a,b]$ and induct
on its length. An object with zero cohomology is zero in the derived category. Otherwise its
standard truncation triangle has terms $\tau^{\leq b-1}C,C,\mathcal H^b(C)[-b]$. The first has a
shorter interval and the third lies in the image by Step 8 and shift closure. Step 5 gives
extension closure, or equivalently lifts the connecting arrow and takes its cone. Thus $C$ is in
the image. Together with Steps 3 and 4 this proves the asserted $E$-linear triangulated
equivalence. In particular the full target subcategory inherits the ambient distinguished
triangles; no idempotent envelope is introduced.
Uses: def-sbc-standard-tstructure-derived-category, lem-weil-heart-short-exact-triangles,
def-weil-abstract-derived-category.

10. The integral t-structure proposition identifies integral truncations and cohomology with the
ambient ones and keeps them in $\mathcal C_X$. The localized t-structure proposition gives
$\tau_E^{\leq m}QK\cong Q\tau_A^{\leq m}K$ and the analogous upper formula. Exact scalar
localization gives the cohomology formula of Step 3, so $J_X$ sends the two localized
degree-bound classes into the corresponding ambient degree-bound classes. In particular it is
t-exact in this direction, and $J_X(\mathcal H^r(QK))$ is $E_X\otimes_{B_X}\mathcal H^r(K)$
placed in degree zero.
Uses: prop-weil-pbc-integral-tstructure, prop-weil-localized-tstructure,
lem-weil-pbc-localization-inverse-image-coherence, def-weil-derived-cohomology-sheaves.

11. Conversely, if $J_X(QK)$ has no cohomology above $m$, then Step 3 and the integral
truncation formula show $J_X(Q\tau_A^{\geq m+1}K)$ has zero cohomology in every degree. It is
zero in the derived category, so full faithfulness implies $Q\tau_A^{\geq m+1}K=0$ (its identity
is zero). The localized truncation triangle then gives $Q\tau_A^{\leq m}K\cong QK$, putting $QK$
in the localized nonpositive class at $m$. The same argument with $\tau_A^{\leq m-1}K$ proves
the converse nonnegative bound. Hence both t-structures agree under $J_X$. Uniqueness of
truncation triangles, with their canonical units and counits, makes the truncation comparisons
natural. Intersecting the two degree bounds identifies the heart with all constructible
$E_X$-sheaves in degree zero, using Step 8 for their essential surjectivity.
Uses: prop-weil-pbc-integral-tstructure, prop-weil-localized-tstructure,
lem-weil-heart-short-exact-triangles, def-weil-abstract-derived-category.

12. Fix $g:X'\to X$ as in the statement. Use the actual structural map $c_g:g^{-1}B_X\to B_{X'}$
defined by its finite quotient components, not an assumed isomorphism. Pull back a supporting
stratification of $K\in\mathcal C_X$; its base changes form a stratification of $X'$. The
trivializing pro-etale covers pull back to covers by weakly etale base change and fpqc covering
stability. On each pulled-back cover, ordinary derived module pullback sends $B_S\otimes_A^L P$
to $B_{S'}\otimes_A^L P$: on the finite projective terms the balancing map is
$b'\otimes(b\otimes p)\mapsto b'c_g(b)\otimes p$, with inverse $b'\otimes p\mapsto
b'\otimes(1\otimes p)$. These maps commute with differentials. Derived pullback is computed on
K-flat flat-term resolutions; its tensor and composition comparisons identify this local
computation with the restriction of $Lg^*_{B}K$. Every new stratum is locally closed in the
noetherian finite-dimensional $X'$, so has the same scheme hypotheses. The stratified-perfect
characterization therefore gives $Lg^*_{B}K\in\mathcal C_{X'}$, including derived completeness
and compatible etale-origin witnesses.
Uses: def-weil-pbc-completed-pullback, lemma-constructible-pullback-stratification,
lem-weil-pbc-weakly-etale-composition-base-change, lem-galois-fpqc-covering-base-change,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-sfb-ringed-derived-monoidal-comparisons,
lem-weil-pbc-integral-stratified-perfect-characterization.

13. The specified comparison $\gamma_{g,K}:Lg^*_{B}K\to Lg^*_{\mathrm{comp}}K$ is the
quotient-tower completion unit by the completed-pullback definition and the constant/completed
comparison. Step 12 makes its source complete. Intrinsic completeness says its Koszul completion
unit is invertible, and the constant-completion equivalence identifies that unit with this
quotient-tower unit, including transitions. Thus $\gamma_{g,K}$ is invertible, naturally in $K$.
Apply localization/inverse-image coherence to $R=B_X,t=\varpi$. It identifies $g^{-1}E_X$ with
$(g^{-1}B_X)[1/\varpi]$, preserving the localization unit. The map $c_g$ sends $\varpi$ to
$\varpi$, so it extends to the structural map into $E_{X'}$. The ringed-topos derived pullback
composition comparison now gives $$J_{X'}(Q Lg^*_{B}K)\cong
E_{X'}\otimes^L_{g^{-1}E_X}g^{-1}(E_X\otimes^L_{B_X}K).$$ Both sides flatten to
$E_{X'}\otimes^L_{g^{-1}B_X}g^{-1}K$ by balancing. Composing this comparison with
$J_{X'}(Q\gamma_{g,K}^{-1})$ proves the displayed completed-pullback comparison. Its naturality
and the fraction rule let it descend to raw rationalizations.
Uses: def-weil-pbc-completed-pullback, def-weil-pbc-intrinsic-completion,
lem-weil-pbc-constant-completion-equivalence, lem-weil-pbc-localization-inverse-image-coherence,
lem-sfb-ringed-derived-monoidal-comparisons, def-weil-pbc-rational-category.

14. For composable scheme maps $X''\xrightarrow h X'\xrightarrow g X$, the structural maps
satisfy $c_{gh}=c_h\,h^{-1}c_g$ after the inverse-image composition comparison: composing with
each finite quotient projection gives the same finite constant-coefficient map, and the limit
universal property gives equality. The ambient derived pullback composition and identity
comparisons are those of the ringed-derived monoidal-comparison lemma.
Localization/inverse-image coherence identifies the comparison for $gh$ with the composite
comparisons for $g,h$, as an equation of natural transformations. On K-flat complexes the tensor
maps send a balanced representative $e''\otimes e'\otimes k$ to $e''h^{-1}(e')\otimes k$ in
either order; the identity sends $1\otimes k$ to $k$. These maps give the comparisons in Step
13. Under the natural completion units $\gamma$, completed pullback on this category is ordinary
pullback; conjugating by those isomorphisms gives exactly the same equations. The
finite-reduction and completion-unit comparisons used here preserve the quotient maps, so the
conjugation uses the specified units, not arbitrary identifications. This proves naturality,
identity and composition with the ambient composition comparisons stated in the item.
Uses: def-weil-pbc-completed-pullback, lem-weil-pbc-localization-inverse-image-coherence,
lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-pbc-constant-completion-equivalence.

15. For a finite extension $E\subset L$, put $A_L=\mathcal O_L$ and
$B_{L,X}=\varprojlim_n(A_L/\varpi_L^n)_X$. The raw scalar-extension proposition defines
$T_{L/E}$ by the actual integral change $C_{L/E,X}K=B_{L,X}\otimes^L_{B_{E,X}}K$ followed by
rationalization, and puts this object in the integral category under our scheme hypotheses.
Continuous-coefficient realization is natural for $A_E\to A_L$ and $E\to L$, so these are the
stated continuous ring maps. Apply the ambient derived pullback composition comparison to the
same-site coefficient maps. It gives
$$J_{L,X}(T_{L/E}QK)=L_X\otimes^L_{B_{L,X}}(B_{L,X}\otimes^L_{B_{E,X}}K)\cong
L_X\otimes^L_{B_{E,X}}K\cong L_X\otimes^L_{E_X}J_{E,X}(QK).$$ The maps flatten $(l\otimes
b)\otimes k$ to $lb\otimes k$, with inverses inserting $1$. They are canonical on K-flat
representatives, and the comparison lemma descends them to derived categories. The image of
every nonzero scalar of $E$ is invertible in $L$, so the equations also hold for the raw
morphisms $f/\varpi_E^n$.
Uses: prop-weil-pbc-scalar-extension, lem-weil-pbc-continuous-coefficient-realizations,
lem-sfb-ringed-derived-monoidal-comparisons.

16. For $E\subset L\subset M$ both routes in the coefficient associator comparison flatten
$m\otimes l\otimes k$ to $ml\otimes k$. For four fields the pentagon flattens all factors to
their ordered product; the unit inserts and removes $1$. The ringed-derived comparison lemma
makes these equations valid on derived complexes; the raw scalar-extension proposition
identifies these associators with its specified ones. To combine with $g:X'\to X$, the square of
the integral structural maps $c_g$ and coefficient change commutes, since on each quotient the
two composites are postcomposition of the same coefficient map and inverse image of the same
section. The continuous realization's coefficient naturality gives the localized square as well.
The last clause of the ringed-derived comparison lemma for isomorphic underlying geometric
composites identifies the two derived tensor routes. Its balanced map sends $l'\otimes b'\otimes
k$ to $l'b'\otimes g^{-1}k$ in either order. The completion-unit comparisons of Step 13 and the
scalar-extension/pullback comparison in the raw scalar-extension proposition preserve this
equation. Thus the realization comparison commutes with finite coefficient extension, successive
extensions, and their pullback and composition associators. No pair-category descent is used.
Uses: lem-sfb-ringed-derived-monoidal-comparisons, prop-weil-pbc-scalar-extension,
lem-weil-pbc-continuous-coefficient-realizations, lem-weil-pbc-constant-completion-equivalence.

17. For a locally closed immersion the coefficient isomorphism is precisely the
continuous-coefficient immersion restriction lemma. For an etale map $g:X'\to X$, use the weakly
etale localization equivalence $X'_{\mathrm{proet}}\simeq X_{\mathrm{proet}}/X'$. The inverse
image $g^{-1}$ of the pro-etale inverse-image definition is this slice restriction: for $U\to
X'$ in $X'_{\mathrm{proet}}$ with structure map $s$, the pair $(U\to X,(s,\mathrm{id}_U))$ is
initial in the indexing category $\mathcal I_U$, since any $(V,\phi)$ has $\phi=(s,a)$ with
$a=\mathrm{pr}_2\phi$ the unique $X$-morphism satisfying $u_g(a)(s,\mathrm{id})=\phi$; hence
$(u_{g,p}F)(U)=F(U\to X)$, already a sheaf on the slice, and no sheafification changes it.
Restriction to this slice evaluates a coefficient sheaf on the same underlying scheme $V$, so
sends $C(|V|,A)$ and $C(|V|,E)$ identically to the corresponding coefficient sheaves on $X'$. In
the finite-quotient description it restricts each constant quotient to the same quotient and
preserves the sectionwise limit, so the resulting coefficient map is exactly $c_g$, with the
constant-section normalizations. The same evaluation argument works for any site object $U\to
X$, without requiring $U$ itself to be noetherian. Inverse image with an identified coefficient
ring is exact by localization/inverse-image coherence; its termwise derived functor is ordinary
inverse image. Hence for the etale and locally closed morphisms the displayed module pullback is
exact inverse image, and on an arbitrary site object it restricts to exact site restriction. All
identifications preserve coefficient maps by their section formulas and Step 1.
Uses: lem-weil-pbc-continuous-coefficients-immersion-restriction,
lem-weil-proetale-weakly-etale-localization, lem-weil-pbc-localization-inverse-image-coherence,
def-weil-pbc-completed-pullback, def-weil-proetale-inverse-image. -/
theorem continuous_rational_derived_realization (l : ℕ) [Fact l.Prime] :
    Nonempty (Family.{u} l) := by
  let raw (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (X : Base.{u} l) : RationalModuleRealization l A X.scheme :=
    Classical.choice (rationalModuleRealizationFunctor l A X.scheme)
  let realization (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (X : Base.{u} l) := realizationAt l A X (raw A X)
  let along (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      {X Y : Base.{u} l} (g : X.scheme ⟶ Y.scheme) :=
    Classical.choice (rationalContinuousPullbackTransport l A g (realization A X)
      (realization A Y))
  let fieldChange (A B : Type u) [Field A] [Field B]
      [Algebra ℚ_[l] A] [Algebra ℚ_[l] B]
      [FiniteDimensional ℚ_[l] A] [FiniteDimensional ℚ_[l] B]
      (i : A →ₐ[ℚ_[l]] B) (X : Base.{u} l) :=
    Classical.choice (fieldChange_exists l A B i X (raw A X) (raw B X))
  obtain ⟨hc, hi, hf, hm⟩ :=
    rationalContinuousComparisonCoherence l realization along fieldChange
  exact ⟨
    { realization := realization
      along := along
      composition := fun A _ _ _ _ _ _ g h ↦ Classical.choice (hc A g h)
      identity := fun A _ _ _ X ↦ Classical.choice (hi A X)
      fieldChange := fieldChange
      fieldComposition := fun A B C _ _ _ _ _ _ _ _ _ i j X ↦
        Classical.choice (hf A B C i j X)
      mixed := fun A B _ _ _ _ _ _ i _ _ g ↦ Classical.choice (hm A B i g)
      siteRestriction := fun A _ _ _ X U ↦
        Classical.choice (rationalContinuousSliceTransport l A X.scheme U) }⟩

end AlgebraicGeometry.Scheme.ContinuousRational
