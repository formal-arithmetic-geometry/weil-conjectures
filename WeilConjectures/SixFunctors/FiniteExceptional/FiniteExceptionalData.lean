/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaPairingData

public import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
import WeilConjectures.SixFunctors.Exceptional.ExceptionalFiniteOperations
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaFiniteTrace
public import WeilConjectures.SixFunctors.Exceptional.ExceptionalFiniteRestrictionAdjunction
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionModels

/-!
# Finite exceptional inverse image and quotient coefficients

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
lem-coef-finite-exceptional and its proof (blueprint: lem-coef-finite-exceptional).
All indices below are predecessors of positive exponents: index n means A_(n+1).
The functors are restrictions of the published intrinsic pro-etale constructions.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteExceptional

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem finiteTransposeLeft
    {E₀ E₁ C₀ C₁ : Type*} [Category* E₀] [Category* E₁]
    [Category* C₀] [Category* C₁]
    (A : E₀ ⥤ C₀) (B : E₁ ⥤ C₁) (U : C₁ ⥤ E₁)
    (F : E₀ ⥤ E₁) (R : E₁ ⥤ E₀) (I : C₀ ⥤ C₁)
    (ad : F ⊣ R) (bd : B ⊣ U)
    {L L' : E₀} {M M' : C₀} {N : C₁}
    (a : A.obj L ≅ M) (a' : A.obj L' ≅ M')
    (v : B.obj (F.obj L) ⟶ I.obj (A.obj L))
    (v' : B.obj (F.obj L') ⟶ I.obj (A.obj L'))
    (s : M ⟶ M') (b : I.obj M' ⟶ N) (t : L ⟶ L')
    (ht : A.map t = a.hom ≫ s ≫ a'.inv)
    (hv : B.map (F.map t) ≫ v' = v ≫ I.map (A.map t)) :
    a.inv ≫ A.map (ad.homEquiv _ _
      (bd.homEquiv _ _ (v ≫ I.map a.hom ≫ I.map s ≫ b))) =
    s ≫ a'.inv ≫ A.map (ad.homEquiv _ _
      (bd.homEquiv _ _ (v' ≫ I.map a'.hom ≫ b))) := by
  have hm : A.map t ≫ a'.hom = a.hom ≫ s := by
    rw [ht]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have heq : v ≫ I.map a.hom ≫ I.map s ≫ b =
      B.map (F.map t) ≫ v' ≫ I.map a'.hom ≫ b := by
    rw [reassoc_of% hv, ← I.map_comp_assoc, ← I.map_comp_assoc, hm, I.map_comp,
      Category.assoc]
  rw [heq, bd.homEquiv_naturality_left, ad.homEquiv_naturality_left, A.map_comp]
  simp only [← Category.assoc]
  congr 1
  rw [ht]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem finiteSpecifiedHomValue
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).IsLeftAdjoint]
    (M : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (W : FixedEtaleOriginWitness X Λ M)
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (a : (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c).obj M.obj ⟶ L.obj) :
    ProEtale.specifiedExceptionalHomEquiv Λ c M W L a = W.iso.inv ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
        ((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} Λ) c)).homEquiv _ _
          ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ _
            ((ProEtale.fixedCompactSupportComparisonIso Λ c).inv.app W.complex ≫
              (ProEtale.rightDerivedLowerShriekOfCompactification
                (ModuleCat.{u + 1} Λ) c).map W.iso.hom ≫ a))) := by
  rfl

private theorem finiteSpecifiedHomLeft
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).IsLeftAdjoint]
    (M M' : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (W : FixedEtaleOriginWitness X Λ M) (W' : FixedEtaleOriginWitness X Λ M')
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (s : M.obj ⟶ M'.obj)
    (a : (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c).obj M'.obj ⟶ L.obj) :
    ProEtale.specifiedExceptionalHomEquiv Λ c M W L
      ((ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} Λ) c).map s ≫ a) =
      s ≫ ProEtale.specifiedExceptionalHomEquiv Λ c M' W' L a := by
  obtain ⟨t, ht⟩ := (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
    W.complex.obj W'.complex.obj W'.complex.property).surjective
      (W.iso.hom ≫ s ≫ W'.iso.inv)
  have hv := (ProEtale.fixedCompactSupportComparisonIso Λ c).inv.naturality
    (ObjectProperty.homMk t : W.complex ⟶ W'.complex)
  rw [finiteSpecifiedHomValue, finiteSpecifiedHomValue]
  exact finiteTransposeLeft _ _ _ _ _ _
    (Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c))
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y)
    W.iso W'.iso _ _ s a t ht hv

private theorem finiteSpecifiedHomRight
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] [CompactSpace Y]
    (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).IsLeftAdjoint]
    (M : DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (W : FixedEtaleOriginWitness X Λ M)
    (L L' : DerivedCategory.Plus (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (a : (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} Λ) c).obj M.obj ⟶ L.obj) (b : L.obj ⟶ L'.obj) :
    ProEtale.specifiedExceptionalHomEquiv Λ c M W L' (a ≫ b) =
      ProEtale.specifiedExceptionalHomEquiv Λ c M W L a ≫
        (ProEtale.sfFiniteExceptionalAt Λ c).map b := by
  rw [finiteSpecifiedHomValue, finiteSpecifiedHomValue]
  simp only [← Category.assoc]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    Functor.map_comp]
  simp only [Category.assoc]
  rfl

private theorem finiteRestrictHom
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (RX : C ⥤ C') (RY : D ⥤ D') [RX.Full] [RX.Faithful] [RY.Full] [RY.Faithful]
    (P : C' ⥤ D') (H : D' ⥤ C') (F : C ⥤ D) (G : D ⥤ C)
    (rF : F ⋙ RY ≅ RX ⋙ P) (rG : G ⋙ RX ≅ RY ⋙ H)
    (e : ∀ K L, (P.obj (RX.obj K) ⟶ RY.obj L) ≃ (RX.obj K ⟶ H.obj (RY.obj L)))
    (hleft : ∀ {K K'} (s : K ⟶ K') (L) (a : P.obj (RX.obj K') ⟶ RY.obj L),
      e K L (P.map (RX.map s) ≫ a) = RX.map s ≫ e K' L a)
    (hright : ∀ (K) {L L'} (a : P.obj (RX.obj K) ⟶ RY.obj L) (b : L ⟶ L'),
      e K L' (a ≫ RY.map b) = e K L a ≫ H.map (RY.map b)) :
    ∃ adj : F ⊣ G, ∀ K L (a : F.obj K ⟶ L),
      RX.map (adj.homEquiv K L a) ≫ rG.hom.app L =
        e K L (rF.inv.app K ≫ RY.map a) := by
  let ffX := Functor.FullyFaithful.ofFullyFaithful RX
  let ffY := Functor.FullyFaithful.ofFullyFaithful RY
  let ψ (K : C) (L : D) : (F.obj K ⟶ L) ≃ (K ⟶ G.obj L) :=
    ffY.homEquiv.trans (((rF.app K).homFromEquiv.trans (e K L)).trans
      (((rG.app L).symm.homToEquiv).trans ffX.homEquiv.symm))
  have hn (K : C) (L : D) (a : F.obj K ⟶ L) :
      RX.map (ψ K L a) ≫ rG.hom.app L =
        e K L (rF.inv.app K ≫ RY.map a) := by
    dsimp only [ψ, Equiv.trans_apply, Functor.FullyFaithful.homEquiv,
      Iso.homFromEquiv, Iso.homToEquiv, Equiv.symm, Equiv.coe_fn_mk]
    rw [ffX.map_preimage]
    simp only [Category.assoc]
    change e K L (rF.inv.app K ≫ RY.map a) ≫ rG.inv.app L ≫ rG.hom.app L = _
    rw [Iso.inv_hom_id_app]
    exact Category.comp_id _
  have hl {K K' : C} (s : K ⟶ K') (L : D) (a : F.obj K' ⟶ L) :
      ψ K L (F.map s ≫ a) = s ≫ ψ K' L a := by
    apply RX.map_injective
    apply (cancel_mono (rG.hom.app L)).1
    rw [hn, RX.map_comp, Category.assoc, hn]
    have hnat := rF.inv.naturality s
    dsimp only [Functor.comp_map] at hnat
    rw [RY.map_comp, ← Category.assoc, ← hnat, Category.assoc]
    change e K L ((RX ⋙ P).map s ≫ rF.inv.app K' ≫ RY.map a) = _
    exact hleft s L _
  have hr (K : C) {L L' : D} (a : F.obj K ⟶ L) (b : L ⟶ L') :
      ψ K L' (a ≫ b) = ψ K L a ≫ G.map b := by
    apply RX.map_injective
    apply (cancel_mono (rG.hom.app L')).1
    have hnat := rG.hom.naturality b
    dsimp only [Functor.comp_map] at hnat
    rw [hn, RX.map_comp, Category.assoc, hnat]
    change _ = RX.map (ψ K L a) ≫ rG.hom.app L ≫ H.map (RY.map b)
    rw [← Category.assoc, hn, RY.map_comp, ← Category.assoc, hright]
  let core : Adjunction.CoreHomEquiv F G :=
    { homEquiv := ψ
      homEquiv_naturality_left_symm := by
        intro K K' L s a
        apply (ψ K L).injective
        rw [Equiv.apply_symm_apply, hl, Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun {_ _ _} a b ↦ hr _ a b }
  exact ⟨Adjunction.mkOfHomEquiv core, fun K L a ↦ by
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    change RX.map (ψ K L a) ≫ rG.hom.app L = _
    exact hn K L a⟩

private theorem support_inverse
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (EX : C ≌ C') (EY : D ≌ D') (P : C ⥤ D) (S : C' ⥤ D')
    (t : EX.functor ⋙ S ≅ P ⋙ EY.functor) (M : C) (L : D)
    (v : P.obj M ⟶ L) :
    (Iso.inverseCompIso
      ((Iso.compInverseIso t).symm ≪≫ Functor.associator _ _ _)).hom.app
        (EX.functor.obj M) ≫ EY.inverse.map (t.hom.app M ≫ EY.functor.map v) =
      P.map (EX.unitIso.inv.app M) ≫ v ≫ EY.unitIso.hom.app L := by
  have ht : t.inv.app (EX.inverse.obj (EX.functor.obj M)) ≫
      S.map (EX.counitIso.hom.app (EX.functor.obj M)) ≫ t.hom.app M =
        EY.functor.map (P.map (EX.unitIso.inv.app M)) := by
    rw [EX.counit_app_functor]
    change t.inv.app (EX.inverse.obj (EX.functor.obj M)) ≫
      S.map (EX.functor.map (EX.unitIso.inv.app M)) ≫ t.hom.app M = _
    have hn := t.inv.naturality (EX.unitIso.inv.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [← Category.assoc, ← hn, Category.assoc]
    simp
  calc
    _ = EY.unitIso.hom.app (P.obj (EX.inverse.obj (EX.functor.obj M))) ≫
        EY.inverse.map (t.inv.app (EX.inverse.obj (EX.functor.obj M)) ≫
          S.map (EX.counitIso.hom.app (EX.functor.obj M)) ≫
          t.hom.app M ≫ EY.functor.map v) := by
      simp [Iso.inverseCompIso, Iso.compInverseIso, Functor.map_comp, Category.assoc]
    _ = EY.unitIso.hom.app (P.obj (EX.inverse.obj (EX.functor.obj M))) ≫
        EY.inverse.map (EY.functor.map (P.map (EX.unitIso.inv.app M) ≫ v)) := by
      have htv := reassoc_of% ht
      rw [htv, EY.functor.map_comp]
    _ = _ := by simpa only [Functor.id_map, Functor.comp_obj, Functor.comp_map,
      Functor.id_obj, Category.assoc] using
      (EY.unitIso.hom.naturality (P.map (EX.unitIso.inv.app M) ≫ v)).symm

/-- The existing positive-level finite-Tor constructible predicate.
Source: blueprint finite-Tor domain (blueprint: lem-coef-finite-exceptional). -/
abbrev domain (T : Scheme.{u}) (n : ℕ) :
    ObjectProperty (proEtaleDerivedCategory T
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T

/-- Actual quotient scalar extension, before restriction to finite Tor.
Source: blueprint Q_T (blueprint: lem-coef-finite-exceptional). -/
abbrev reduction (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (m + 1)) ⥤
      proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (n + 1)) :=
  pbcDerivedExtend ((PurCompactSupport.finiteQuotientChange l E
    (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n)
    (Nat.add_le_add_right h 1)).map T)

attribute [local irreducible] reductionDerivedChange in
/-- Finite-Tor constructibility survives the actual quotient tensor.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-finite-exceptional).
Proof: apply the arbitrary finite-ring scalar-extension theorem to the actual quotient
map. Its bounded flat model remains flat in the same interval after scalar extension.
The scalar-extension constructibility theorem supplies the constructible cohomology;
the Tor interval also bounds its cohomological support. The scalar functor is exactly
the published derived quotient tensor, including equal indices. -/
theorem reduction_preserves (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (K : (domain l E T m).FullSubcategory) :
    domain l E T n ((reduction l E T h).obj K.obj) := by
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let B := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite A := Padic.finite_coefficientExtensionRing l E _ (Nat.succ_pos m)
  have : Finite B := Padic.finite_coefficientExtensionRing l E _ (Nat.succ_pos n)
  let φ : A →+* B := compactSupportLevelQuotient l E m n h
  have hF : reduction l E T h = ProEtale.scalarExtensionFunctor φ T := by
    apply congrArg (reductionDerivedChange T)
    rfl
  rw [hF]
  obtain ⟨⟨hb, hc⟩, a, b, ht⟩ := K.property
  have ht' := ProEtale.scalarExtension_tor φ T K.obj a b ht
  have hb' := ProEtale.scalarExtension_bounded_of_tor T B _ a b ht'
  have hc' := ProEtale.scalarExtension_constructible φ T K.obj hb hc
  exact ⟨⟨hb', hc'⟩, a, b, ht'⟩

/-- Restriction of the actual quotient tensor, with unchanged morphisms.
Source: blueprint Q_T (blueprint: lem-coef-finite-exceptional). -/
def Q (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (domain l E T m).FullSubcategory ⥤ (domain l E T n).FullSubcategory :=
  (domain l E T n).lift ((domain l E T m).ι ⋙ reduction l E T h)
    (reduction_preserves l E T h)

/-- A bounded etale origin obtained directly from the arbitrary finite-ring comparison.
Source: Stacks, Tag 09AL. Finite support gives an ordered cohomological interval;
exact coefficient realization transports the resulting bounded etale origin. -/
private theorem finiteRingOrigin (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u})
    (K : (domain l E T n).FullSubcategory) :
    ∃ h : DerivedCategory.TStructure.t.plus
        ((sfIntrinsicDerivedEquivalence T
          (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj K.obj),
      Nonempty (FixedEtaleOriginWitness T
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
        ⟨(sfIntrinsicDerivedEquivalence T
          (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj K.obj, h⟩) := by
  classical
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E _ (Nat.succ_pos n)
  let : HasDerivedCategory.{u + 2}
      (proEtaleRingModules T (proEtaleConstantRing T A)) :=
    HasDerivedCategory.standard _
  let R := sfIntrinsicDerivedEquivalence T A
  let U := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  obtain ⟨a, ha⟩ := K.property.1.1.bddBelow
  obtain ⟨b, hb⟩ := K.property.1.1.bddAbove
  have horigin : ∃ L : Etale.BoundedConstructibleDerivedCategory
      (ULift.{u + 1, u} A) T,
      Nonempty ((ProEtale.finiteCoefficientIntrinsicDerivedComparison T A).obj L.obj ≅
        K.obj) := by
    apply ((finiteRing_constructibleDerived_origin T A).2.2.1 K.obj).mpr
    refine ⟨K.property.1.2, min a b, b, min_le_right _ _, ?_⟩
    intro i hi
    by_contra hz
    rcases hi with hi | hi
    · exact (not_lt_of_ge (ha hz)) (lt_of_lt_of_le hi (min_le_left _ _))
    · exact (not_lt_of_ge (hb hz)) hi
  obtain ⟨L, ⟨eL⟩⟩ := horigin
  let hL : DerivedCategory.TStructure.t.plus L.obj := by
    obtain ⟨c, d, _, hcd⟩ := L.property.2
    exact ⟨c, (DerivedCategory.isGE_iff L.obj c).2 (fun i hi ↦ hcd i (.inl hi))⟩
  let e : U.mapDerivedCategory.obj L.obj ≅ R.inverse.obj K.obj :=
    R.functor.preimageIso
      (((Functor.mapDerivedCategoryCompIso U
        (sfIntrinsicModuleEquivalence T A).functor).app L.obj).symm ≪≫
        eL ≪≫ (R.counitIso.app K.obj).symm)
  have hU : DerivedCategory.TStructure.t.plus (U.mapDerivedCategory.obj L.obj) := by
    obtain ⟨c, hc⟩ := hL
    refine ⟨c, (DerivedCategory.isGE_iff _ c).2 (fun i hi ↦ ?_)⟩
    exact U.isZero_homologyFunctor_mapDerivedCategory_obj
      ((DerivedCategory.isGE_iff L.obj c).1 hc i hi)
  have h : DerivedCategory.TStructure.t.plus (R.inverse.obj K.obj) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso e hU
  exact ⟨h, ⟨⟨⟨L.obj, hL⟩, e⟩⟩⟩

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
  [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f)

set_option linter.unusedSectionVars false in
include D hl Xbase Ybase Xft Xqc Yft Yqc Xsep Ysep fbase fsep fft fqc in
/-- The two specified finite functors preserve their constructible finite-Tor domains.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional).
Proof: bound the dimension of the proper compactification over the field and apply
exists_sfFiniteExceptionalOperations at the given field and positive level. Its literal
ambient-functor equalities give preservation for compact support and for the specified
ordinary-etale right adjoint transported to intrinsic coefficients. Right-adjoint
uniqueness identifies that adjoint with sfFiniteExceptionalFixed. Repleteness of the
finite-Tor constructible subcategory transports preservation along this canonical
isomorphism. The finite-dimension theorem includes the empty scheme. -/
theorem operations_preserve (n : ℕ) :
    (∀ K : (domain l E X n).FullSubcategory,
      domain l E Y n ((sfIntrinsicCompactSupport c
        (Padic.coefficientExtensionRing l E (n + 1))).obj K.obj)) ∧
    (∀ L : (domain l E Y n).FullSubcategory,
      domain l E X n ((ProEtale.sfFiniteExceptional
        (Padic.coefficientExtensionRing l E (n + 1)) c).obj L.obj)) := by
  let E' : ConstructibleExceptionalCoefficients.FieldStage.{u} l :=
    { carrier := E }
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (c.g ≫ (Y ↘ Spec (.of D.k)))
  obtain ⟨cMinus, cPlus, h⟩ := exists_sfFiniteExceptionalOperations D l hl f c d hd
  obtain ⟨F', G', eF, eG, _⟩ := h E' ⟨n + 1, Nat.succ_pos n⟩
  constructor
  · intro K
    have he := congrArg
      (fun H : (domain l E X n).FullSubcategory ⥤
          proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)) ↦ H.obj K) eF
    exact he ▸ (F'.obj K).property
  · intro L
    have he := congrArg
      (fun H : (domain l E Y n).FullSubcategory ⥤
          proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)) ↦ H.obj L) eG
    have hG : domain l E X n
        ((sfFiniteOperationsIntrinsicRight l E' ⟨n + 1, Nat.succ_pos n⟩ c).obj L.obj) :=
      he ▸ (G'.obj L).property
    have : (domain l E X n).IsClosedUnderIsomorphisms :=
      (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) X).1
    let : (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1)))) c).IsLeftAdjoint :=
      Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c
    let e : ProEtale.sfFiniteExceptionalFixed
        (Padic.coefficientExtensionRing l E (n + 1)) c ≅
          ProEtale.sfFiniteExceptionalAt
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c :=
      letI := c.hasCompactification
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft _
          ((Etale.rightDerivedUpperShriekAdjunctionOfCompactification
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c).rightAdjointUniq
            (Adjunction.ofIsLeftAdjoint
              (Etale.rightDerivedLowerShriekOfCompactification
                (ModuleCat.{u + 1} (ULift.{u + 1, u}
                  (Padic.coefficientExtensionRing l E (n + 1)))) c)))) _
    exact (domain l E X n).prop_of_iso
      ((Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft
          (sfIntrinsicDerivedEquivalence Y
            (Padic.coefficientExtensionRing l E (n + 1))).inverse e)
        (sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing l E (n + 1))).functor).symm.app L.obj) hG

/-- Rf_! is the restriction of the specified compactification construction.
Source: blueprint F_r (blueprint: lem-coef-finite-exceptional). -/
def F (n : ℕ) :
    (domain l E X n).FullSubcategory ⥤ (domain l E Y n).FullSubcategory :=
  (domain l E Y n).lift ((domain l E X n).ι ⋙
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
    (operations_preserve l E D hl f c n).1

/-- Rf^! is the restriction of Rnu_* followed by the etale adjoint and nu^*.
Source: blueprint G_r (blueprint: lem-coef-finite-exceptional). -/
def G (n : ℕ) :
    (domain l E Y n).FullSubcategory ⥤ (domain l E X n).FullSubcategory :=
  (domain l E X n).lift ((domain l E Y n).ι ⋙
    ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c)
    (operations_preserve l E D hl f c n).2

/-- The recorded Verdier dual into the actual structural exceptional image of the unit.
Source: blueprint omega and D (blueprint: lem-coef-finite-exceptional). -/
def dual (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))] (n : ℕ) :
    (proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (n + 1)))ᵒᵖ ⥤
      proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (n + 1)) :=
  (Functor.curry.obj (finiteIntrinsicDerivedInternalHom l E T n)).flip.obj
    (integralDualizingFiniteTerm l E D T n)

/-- The double-dual pullback formula as an actual covariant ambient functor.
Source: blueprint first display (blueprint: lem-coef-finite-exceptional). -/
def H (n : ℕ) :
    proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)) ⥤
      proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)) :=
  (dual l E D Y n).rightOp ⋙ (finiteDerivedPullback l E n f).op ⋙ dual l E D X n

/-- The canonical compact-support scalar mate, in the intrinsic realization.
Source: blueprint q_(m,n) (blueprint: lem-coef-finite-exceptional). -/
def supportMap {m n : ℕ} (h : n ≤ m) :
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1)) ⋙
        reduction l E Y h ⟶
      reduction l E X h ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) :=
  Functor.whiskerRight (PurCompactSupport.finiteImageIso l E m c).inv
      (reduction l E Y h) ≫
    PurCompactSupport.comparison (PurCompactSupport.finiteQuotientChange l E
      (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1)) c ≫
    Functor.whiskerLeft (reduction l E X h)
      (PurCompactSupport.finiteImageIso l E n c).hom

/-- Positive-index specialization of the published quotient coefficient map. -/
private theorem quotient_map (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (PurCompactSupport.finiteQuotientChange l E (m + 1) (n + 1)
      (Nat.succ_pos m) (Nat.succ_pos n) (Nat.add_le_add_right h 1)).map T =
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (compactSupportLevelQuotient l E m n h).ulift) := rfl

/-- Quotient composition as an equality of actual constant-ring maps.
Source: blueprint quotient cocycle (blueprint: lem-coef-finite-exceptional).
Proof: quotient induction sends both composites to the same residue class.
The constant-sheaf functor preserves this equality, including equal indices. -/
theorem quotient_comp (T : Scheme.{u}) {m n t : ℕ} (h : n ≤ m) (k : t ≤ n) :
    (PurCompactSupport.finiteQuotientChange l E (m + 1) (n + 1)
      (Nat.succ_pos m) (Nat.succ_pos n) (Nat.add_le_add_right h 1)).map T ≫
      (PurCompactSupport.finiteQuotientChange l E (n + 1) (t + 1)
        (Nat.succ_pos n) (Nat.succ_pos t) (Nat.add_le_add_right k 1)).map T =
    (PurCompactSupport.finiteQuotientChange l E (m + 1) (t + 1)
      (Nat.succ_pos m) (Nat.succ_pos t) (Nat.add_le_add_right (k.trans h) 1)).map T := by
  rw [quotient_map l E T h, quotient_map l E T k,
    quotient_map l E T (k.trans h), ← Functor.map_comp]
  apply congrArg ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  rintro ⟨x⟩
  apply ULift.ext
  exact Ideal.Quotient.factor_comp_apply
    (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))
    (Ideal.pow_le_pow_right (Nat.add_le_add_right k 1)) x

/-- The identical quotient induces the identity map of coefficient sheaves.
Source: blueprint equal-index clause (blueprint: lem-coef-finite-exceptional).
Proof: quotient induction gives identity on each residue class, and constant
sheafification preserves identities. -/
theorem quotient_id (T : Scheme.{u}) (n : ℕ) :
    (PurCompactSupport.finiteQuotientChange l E (n + 1) (n + 1)
      (Nat.succ_pos n) (Nat.succ_pos n) (Nat.add_le_add_right (le_refl n) 1)).map T =
      𝟙 _ := by
  rw [quotient_map l E T (le_refl n)]
  have hq : compactSupportLevelQuotient l E n n le_rfl = RingHom.id _ :=
    Ideal.Quotient.factor_eq
  rw [hq]
  exact (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_id _

/-- Actual tensor associativity restricted through the full finite-Tor inclusion.
Source: blueprint quotient cocycle (blueprint: lem-coef-finite-exceptional). -/
def reassoc (T : Scheme.{u}) {m n t : ℕ} (h : n ≤ m) (k : t ≤ n) :
    Q l E T h ⋙ Q l E T k ≅ Q l E T (k.trans h) :=
  Functor.fullyFaithfulCancelRight (domain l E T t).ι
    (Functor.isoWhiskerLeft (domain l E T m).ι
      (PurCompactSupport.tensorComposition _ _ _ (quotient_comp l E T h k)))

/-- Actual multiplication unit for self reduction, restricted to finite Tor.
Source: blueprint equal-index clause (blueprint: lem-coef-finite-exceptional). -/
def selfReduction (T : Scheme.{u}) (n : ℕ) : Q l E T (le_refl n) ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (domain l E T n).ι
    (Functor.isoWhiskerLeft (domain l E T n).ι
      (eqToIso (congrArg pbcDerivedExtend (quotient_id l E T n)) ≪≫
        PurCompactSupport.tensorIdentity _))

/-- Brown representability for the specified ordinary etale compact-support candidate.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
instance fixedSupport_isLeftAdjoint (n : ℕ) :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))) c).IsLeftAdjoint :=
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c

/-- The specified fixed-scalar exceptional realization is identified with the
right adjoint of the very same compactification by uniqueness of right adjoints.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
def fixedExceptionalIso (n : ℕ) :
    ProEtale.sfFiniteExceptionalFixed (Padic.coefficientExtensionRing l E (n + 1)) c ≅
      ProEtale.sfFiniteExceptionalAt
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c :=
  letI := c.hasCompactification
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft _
      ((Etale.rightDerivedUpperShriekAdjunctionOfCompactification
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) c).rightAdjointUniq
        (Adjunction.ofIsLeftAdjoint
          (Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u}
              (Padic.coefficientExtensionRing l E (n + 1)))) c)))) _

/-- The canonical fixed-scalar Hom bijection, with an arbitrary retained etale origin.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
def fixedHom (n : ℕ)
    (M : DerivedCategory.Plus (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))
    (W : FixedEtaleOriginWitness X _ M)
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))) :
    ((ProEtale.sfFixedCompactSupport (Padic.coefficientExtensionRing l E (n + 1)) c).obj
      M.obj ⟶ L.obj) ≃
      (M.obj ⟶ (ProEtale.sfFiniteExceptionalFixed
        (Padic.coefficientExtensionRing l E (n + 1)) c).obj L.obj) :=
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  (ProEtale.specifiedExceptionalHomEquiv _ c M W L).trans
    ((fixedExceptionalIso l E f c n).symm.app L.obj).homToEquiv

/-- The normalization on every etale-origin representative fixes the adjunction,
including its units and counits. There is no choice of adjunction in this predicate.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
def AdjunctionNormalized (n : ℕ) (a : F l E D hl f c n ⊣ G l E D hl f c n) : Prop :=
  ∀ (M : DerivedCategory.Plus (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1))))))
    (W : FixedEtaleOriginWitness X _ M)
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (n + 1))))))
    (hM : domain l E X n
      ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))).functor.obj
        M.obj))
    (hL : domain l E Y n
      ((sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (n + 1))).functor.obj
        L.obj))
    (v : (ProEtale.sfFixedCompactSupport
      (Padic.coefficientExtensionRing l E (n + 1)) c).obj M.obj ⟶ L.obj),
    (a.homEquiv ⟨_, hM⟩ ⟨_, hL⟩
      (ObjectProperty.homMk
        ((ProEtale.sfIntrinsicCompactSupportComparison _ c).hom.app M.obj ≫
          (sfIntrinsicDerivedEquivalence Y
            (Padic.coefficientExtensionRing l E (n + 1))).functor.map v))).hom =
      (sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (n + 1))).functor.map
          (fixedHom l E D f c n M W L v ≫
            (ProEtale.sfFiniteExceptionalFixed
              (Padic.coefficientExtensionRing l E (n + 1)) c).map
                ((sfIntrinsicDerivedEquivalence Y
                  (Padic.coefficientExtensionRing l E (n + 1))).unitIso.hom.app L.obj))

/-- The constructible adjunction is uniquely fixed by the recorded bounded Hom chain.
Source: blueprint proof paragraph 1 (blueprint: def-sf-finite-exceptional-constructions).
Proof: lem-sf-proetale-constructible-origin supplies a bounded etale representative
for every constructible input. Transport specifiedExceptionalHomEquiv through the
canonical coefficient realizations. Its naturality supplies Adjunction.mkOfHomEquiv.
Full faithfulness and independence of the representative give the displayed
normalization for every witness. Each Hom bijection is therefore determined, so the
adjunction is unique. Preservation and Tor domains are operations_preserve. -/
theorem adjunction_existsUnique (n : ℕ) :
    ∃! a : F l E D hl f c n ⊣ G l E D hl f c n,
      AdjunctionNormalized l E D hl f c n a := by
  classical
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let EX := sfIntrinsicDerivedEquivalence X A
  let EY := sfIntrinsicDerivedEquivalence Y A
  let RX := (domain l E X n).ι ⋙ EX.inverse
  let RY := (domain l E Y n).ι ⋙ EY.inverse
  let P := ProEtale.sfFixedCompactSupport A c
  let J := ProEtale.sfFiniteExceptionalFixed A c
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  let hX (K : (domain l E X n).FullSubcategory) :
      DerivedCategory.TStructure.t.plus (RX.obj K) :=
    (finiteRingOrigin l E n X K).choose
  let hY (L : (domain l E Y n).FullSubcategory) :
      DerivedCategory.TStructure.t.plus (RY.obj L) :=
    (finiteRingOrigin l E n Y L).choose
  let wX (K : (domain l E X n).FullSubcategory) :
      FixedEtaleOriginWitness X (ULift.{u + 1, u} A) ⟨RX.obj K, hX K⟩ :=
    Classical.choice (finiteRingOrigin l E n X K).choose_spec
  let t := ProEtale.sfIntrinsicCompactSupportComparison A c
  let sF : sfIntrinsicCompactSupport c A ⋙ EY.inverse ≅ EX.inverse ⋙ P :=
    (Iso.inverseCompIso
      ((Iso.compInverseIso t).symm ≪≫ Functor.associator _ _ _)).symm
  let rF : F l E D hl f c n ⋙ RY ≅ RX ⋙ P :=
    NatIso.ofComponents (fun K ↦ sF.app K.obj)
      (by intro K K' v; exact sF.hom.naturality v.hom)
  let rG : G l E D hl f c n ⋙ RX ≅ RY ⋙ J :=
    NatIso.ofComponents (fun L ↦ EX.unitIso.symm.app (J.obj (RY.obj L)))
      (by intro L L' v; exact EX.unitIso.inv.naturality (J.map (RY.map v)))
  let e (K : (domain l E X n).FullSubcategory)
      (L : (domain l E Y n).FullSubcategory) :
      (P.obj (RX.obj K) ⟶ RY.obj L) ≃ (RX.obj K ⟶ J.obj (RY.obj L)) :=
    fixedHom l E D f c n ⟨RX.obj K, hX K⟩ (wX K) ⟨RY.obj L, hY L⟩
  have heLeft {K K'} (s : K ⟶ K') (L) (a : P.obj (RX.obj K') ⟶ RY.obj L) :
      e K L (P.map (RX.map s) ≫ a) = RX.map s ≫ e K' L a := by
    change ProEtale.specifiedExceptionalHomEquiv _ c
      ⟨RX.obj K, hX K⟩ (wX K) ⟨RY.obj L, hY L⟩ (P.map (RX.map s) ≫ a) ≫
        (fixedExceptionalIso l E f c n).inv.app (RY.obj L) =
      RX.map s ≫ ProEtale.specifiedExceptionalHomEquiv _ c
        ⟨RX.obj K', hX K'⟩ (wX K') ⟨RY.obj L, hY L⟩ a ≫ _
    have hh := finiteSpecifiedHomLeft (ULift.{u + 1, u} A) c
      ⟨RX.obj K, hX K⟩ ⟨RX.obj K', hX K'⟩ (wX K) (wX K')
      ⟨RY.obj L, hY L⟩ (RX.map s) a
    exact (congrArg (· ≫ (fixedExceptionalIso l E f c n).inv.app (RY.obj L)) hh).trans
      (Category.assoc _ _ _)
  have heRight (K) {L L'} (a : P.obj (RX.obj K) ⟶ RY.obj L) (b : L ⟶ L') :
      e K L' (a ≫ RY.map b) = e K L a ≫ J.map (RY.map b) := by
    change ProEtale.specifiedExceptionalHomEquiv _ c
      ⟨RX.obj K, hX K⟩ (wX K) ⟨RY.obj L', hY L'⟩ (a ≫ RY.map b) ≫
        (fixedExceptionalIso l E f c n).inv.app (RY.obj L') =
      (ProEtale.specifiedExceptionalHomEquiv _ c
        ⟨RX.obj K, hX K⟩ (wX K) ⟨RY.obj L, hY L⟩ a ≫ _) ≫ J.map (RY.map b)
    have hh := finiteSpecifiedHomRight (ULift.{u + 1, u} A) c
      ⟨RX.obj K, hX K⟩ (wX K) ⟨RY.obj L, hY L⟩ ⟨RY.obj L', hY L'⟩ a (RY.map b)
    have hn := (fixedExceptionalIso l E f c n).inv.naturality (RY.map b)
    calc
      _ = (ProEtale.specifiedExceptionalHomEquiv _ c
          ⟨RX.obj K, hX K⟩ (wX K) ⟨RY.obj L, hY L⟩ a ≫
          (ProEtale.sfFiniteExceptionalAt (ULift.{u + 1, u} A) c).map (RY.map b)) ≫
            (fixedExceptionalIso l E f c n).inv.app (RY.obj L') :=
        congrArg (· ≫ (fixedExceptionalIso l E f c n).inv.app (RY.obj L')) hh
      _ = _ := by
        rw [Category.assoc]
        exact (congrArg (ProEtale.specifiedExceptionalHomEquiv _ c
          ⟨RX.obj K, hX K⟩ (wX K) ⟨RY.obj L, hY L⟩ a ≫ ·) hn).trans
            (Category.assoc _ _ _).symm
  obtain ⟨a, ha⟩ := finiteRestrictHom RX RY P J (F l E D hl f c n)
    (G l E D hl f c n) rF rG e heLeft heRight
  have hnorm : AdjunctionNormalized l E D hl f c n a := by
    intro M W L hM hL v
    let K0 : (domain l E X n).FullSubcategory := ⟨EX.functor.obj M.obj, hM⟩
    let L0 : (domain l E Y n).FullSubcategory := ⟨EY.functor.obj L.obj, hL⟩
    let x : (F l E D hl f c n).obj K0 ⟶ L0 :=
      ObjectProperty.homMk (t.hom.app M.obj ≫ EY.functor.map v)
    apply EX.inverse.map_injective
    apply (cancel_mono (EX.unitIso.inv.app (J.obj (RY.obj L0)))).1
    change RX.map (a.homEquiv K0 L0 x) ≫ rG.hom.app L0 =
      EX.inverse.map (EX.functor.map
        (fixedHom l E D f c n M W L v ≫ J.map (EY.unitIso.hom.app L.obj))) ≫ _
    rw [ha]
    have hs : rF.inv.app K0 ≫ RY.map x =
        P.map (EX.unitIso.inv.app M.obj) ≫ v ≫ EY.unitIso.hom.app L.obj := by
      exact support_inverse EX EY P _ t M.obj L.obj v
    rw [hs]
    have hu := EX.unitIso.inv.naturality
      (fixedHom l E D f c n M W L v ≫ J.map (EY.unitIso.hom.app L.obj))
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map,
      Functor.id_obj] at hu
    change EX.inverse.map (EX.functor.map _) ≫
      EX.unitIso.inv.app (J.obj (RY.obj L0)) = _ at hu
    apply Eq.trans ?_ hu.symm
    change ProEtale.specifiedExceptionalHomEquiv _ c
      ⟨RX.obj K0, hX K0⟩ (wX K0) ⟨RY.obj L0, hY L0⟩
        (P.map (EX.unitIso.inv.app M.obj) ≫ v ≫ EY.unitIso.hom.app L.obj) ≫
          (fixedExceptionalIso l E f c n).inv.app (RY.obj L0) =
      EX.unitIso.inv.app M.obj ≫
        (ProEtale.specifiedExceptionalHomEquiv _ c M W L v ≫
          (fixedExceptionalIso l E f c n).inv.app L.obj) ≫
            J.map (EY.unitIso.hom.app L.obj)
    erw [finiteSpecifiedHomLeft (ULift.{u + 1, u} A) c
      ⟨RX.obj K0, hX K0⟩ M (wX K0) W ⟨RY.obj L0, hY L0⟩
      (EX.unitIso.inv.app M.obj) (v ≫ EY.unitIso.hom.app L.obj)]
    erw [finiteSpecifiedHomRight (ULift.{u + 1, u} A) c M W L
      ⟨RY.obj L0, hY L0⟩ v (EY.unitIso.hom.app L.obj)]
    simp only [Category.assoc]
    exact congrArg
      (fun z ↦ EX.unitIso.inv.app M.obj ≫
        ProEtale.specifiedExceptionalHomEquiv _ c M W L v ≫ z)
      ((fixedExceptionalIso l E f c n).inv.naturality (EY.unitIso.hom.app L.obj))
  refine ⟨a, hnorm, ?_⟩
  intro a' ha'
  have hHom
      (M : DerivedCategory.Plus (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
      (W : FixedEtaleOriginWitness X _ M)
      (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
      (hM : domain l E X n (EX.functor.obj M.obj))
      (hL : domain l E Y n (EY.functor.obj L.obj))
      (x : (F l E D hl f c n).obj ⟨_, hM⟩ ⟶ ⟨_, hL⟩) :
      a'.homEquiv _ _ x = a.homEquiv _ _ x := by
    let v : P.obj M.obj ⟶ L.obj := EY.functor.preimage (t.inv.app M.obj ≫ x.hom)
    have hx : ObjectProperty.homMk (t.hom.app M.obj ≫ EY.functor.map v) = x := by
      apply ObjectProperty.hom_ext
      dsimp only [v]
      rw [Functor.map_preimage]
      simp only [Iso.hom_inv_id_app_assoc]
      rfl
    rw [← hx]
    apply ObjectProperty.hom_ext
    exact (ha' M W L hM hL v).trans (hnorm M W L hM hL v).symm
  have : (domain l E X n).IsClosedUnderIsomorphisms :=
    (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) X).1
  have : (domain l E Y n).IsClosedUnderIsomorphisms :=
    (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) Y).1
  apply Adjunction.ext
  apply NatTrans.ext
  funext K
  let hM := (domain l E X n).prop_of_iso (EX.counitIso.app K.obj).symm K.property
  let K0 : (domain l E X n).FullSubcategory := ⟨EX.functor.obj (RX.obj K), hM⟩
  let eK : K0 ≅ K := (domain l E X n).fullyFaithfulι.preimageIso (EX.counitIso.app K.obj)
  let FK := (F l E D hl f c n).obj K0
  let hL := (domain l E Y n).prop_of_iso (EY.counitIso.app FK.obj).symm FK.property
  let L0 : (domain l E Y n).FullSubcategory := ⟨EY.functor.obj (RY.obj FK), hL⟩
  let eL : L0 ≅ FK := (domain l E Y n).fullyFaithfulι.preimageIso
    (EY.counitIso.app FK.obj)
  have hu0 : a'.unit.app K0 = a.unit.app K0 := by
    have hh := hHom ⟨RX.obj K, hX K⟩ (wX K) ⟨RY.obj FK, hY FK⟩ hM hL eL.inv
    change a'.unit.app K0 ≫ (G l E D hl f c n).map eL.inv =
      a.unit.app K0 ≫ (G l E D hl f c n).map eL.inv at hh
    have hh' := congrArg (· ≫ (G l E D hl f c n).map eL.hom) hh
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id] at hh'
    have hg := (G l E D hl f c n).map_id FK
    rw [hg] at hh'
    exact (Category.comp_id _).symm.trans (hh'.trans (Category.comp_id _))
  apply (cancel_epi eK.hom).1
  calc
    eK.hom ≫ a'.unit.app K = a'.unit.app K0 ≫
        (F l E D hl f c n ⋙ G l E D hl f c n).map eK.hom :=
      by simpa only [Functor.id_map] using a'.unit.naturality eK.hom
    _ = a.unit.app K0 ≫ (F l E D hl f c n ⋙ G l E D hl f c n).map eK.hom := by rw [hu0]
    _ = eK.hom ≫ a.unit.app K := by
      simpa only [Functor.id_map] using (a.unit.naturality eK.hom).symm

/-- The specified constructible adjunction, selected only by its unique Hom normalization.
Source: blueprint proof paragraph 1 (blueprint: lem-coef-finite-exceptional). -/
def adjunction (n : ℕ) : F l E D hl f c n ⊣ G l E D hl f c n :=
  (adjunction_existsUnique l E D hl f c n).choose

set_option linter.unusedSectionVars false in
/-- The finite constant-ring pull identifications respect compactification composition.
Source: blueprint proof step 3, projection construction
(blueprint: lem-coef-finite-exceptional).
Proof: the canonical inverse-image comparison sends every constant section to itself.
The inverse-image composition comparison has the same action. The constant-sheaf
universal property identifies the two ring maps, hence their isomorphisms. -/
theorem finitePull_comp (n : ℕ) :
    (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (c.i ≫ c.g) =
      proEtaleRingCompositeCoefficients c.i c.g
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring c.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull c.g)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull c.i) := by
  exact (proEtaleConstantRingCompositeCoefficients_eq c.i c.g
    (Padic.coefficientExtensionRing l E (n + 1))).symm

/-- The ordinary pullback presentation comparison, descended termwise. It is fixed
by the constant-section adjunction, before any exceptional formula is considered.
Source: blueprint proof step 3, ordinary pullback
(blueprint: lem-coef-finite-exceptional). -/
def formulaPullIso (n : ℕ) :
    PurCompactSupport.pull (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) f ≅
      finiteDerivedPullback l E n f := by
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  letI : (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f).Additive :=
    sfIntrinsicPullback_additive _ f
  letI : HasDerivedCategory (proEtaleRingModules Y
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory (proEtaleRingModules X
      (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1)))) :=
    HasDerivedCategory.standard _
  exact Functor.mapDerivedCategoryNatIso.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (C := proEtaleRingModules Y
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1))))
    (D := proEtaleRingModules X
      (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1))))
    (PurCompactSupport.finitePullbackIso.{u} l E n f)

/-- Evaluation and absolute-trace normalization of the finite dual-formula comparison.
All tensor presentations have their existing K-flat/evaluation normalization, and
sX is the descended Koszul symmetry. The trace is the existing structural-counit
transpose through compact-support composition, transported by the canonical site
comparisons. Thus this equation excludes rescaling the dual-formula isomorphism.
Source: blueprint proof steps 3--5; finite analogue of FormulaNormalized in
CoefDualFormulaScalarTranspose (blueprint: lem-coef-finite-exceptional). -/
def FormulaNormalized (n : ℕ)
    (k : G l E D hl f c n ⋙ (domain l E X n).ι ≅
      (domain l E Y n).ι ⋙ H l E D f n) : Prop :=
  ∀ (aX : IntegralHom.TensorPresentation.{u, u} X
      (integralCoefficientCommRingSheaf l E X n))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (integralCoefficientCommRingSheaf l E c.Z n))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (integralCoefficientCommRingSheaf l E Y n))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (L : (domain l E Y n).FullSubcategory),
    ((PurCompactSupport.projectionMap
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c
      (IntegralFiniteExtension.tensorModel X aX)
      (IntegralFiniteExtension.tensorModel c.Z aZ)
      (IntegralFiniteExtension.tensorModel Y aY)
      (finitePull_comp l E f c n)).app ((G l E D hl f c n).obj L).obj).app
        ((dual l E D Y n).obj (op L.obj)) ≫
      (PurCompactSupport.image
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c).map
        (aX.tensor.map (Prod.mkHom (𝟙 _)
          ((formulaPullIso l E f n).hom.app ((dual l E D Y n).obj (op L.obj)))) ≫
          (sX.swap ((G l E D hl f c n).obj L).obj
            ((finiteDerivedPullback l E n f).obj
              ((dual l E D Y n).obj (op L.obj)))).hom ≫
          aX.tensor.map (Prod.mkHom (𝟙 _) (k.hom.app L)) ≫
          (aX.adjunction ((finiteDerivedPullback l E n f).obj
            ((dual l E D Y n).obj (op L.obj)))).counit.app
              (integralDualizingFiniteTerm l E D X n)) ≫
      (PurCompactSupport.finiteImageIso l E n c).hom.app
        (integralDualizingFiniteTerm l E D X n) ≫
      CoefDualFormulaScalarTranspose.finiteTrace D l E f c n =
    aY.tensor.map (Prod.mkHom
      ((PurCompactSupport.finiteImageIso l E n c).hom.app
        ((G l E D hl f c n).obj L).obj ≫
        ((adjunction l E D hl f c n).counit.app L).hom) (𝟙 _)) ≫
      (aY.tensor.map (Prod.mkHom (𝟙 L.obj) (𝟙 _))) ≫
      (aY.adjunction L.obj).counit.app (integralDualizingFiniteTerm l E D Y n)

/-- The finite dual formula has a unique evaluation/trace-normalized natural isomorphism.
Source: blueprint proof steps 2--5 (blueprint: lem-coef-finite-exceptional).
Proof: finite Verdier biduality and pullback Tor preservation put H in the domain.
Form the structural relative trace by transposing the absolute counit through support
composition. Projection, the ordinary counit and evaluation define the exchange
pairing. The absolute-trace-exchange lemma identifies its Hom action and proves it
invertible. Biduality, the ordinary adjunction, this exchange and biduality give the
four natural Hom bijections displayed in the blueprint. They make H a right adjoint
to F. Uniqueness of right adjoints compares it with the specified adjunction F ⊣ G.
Uncurrying the image of its counit gives exactly the displayed normalization, for
every normalized tensor presentation. Conversely, tensor-Hom injectivity, projection
invertibility on the finite-Tor domain and Verdier duality force each component from
this equation. Naturality then gives uniqueness of the natural isomorphism. -/
theorem dualFormula_existsUnique (n : ℕ) :
    ∃! k : G l E D hl f c n ⋙ (domain l E X n).ι ≅
      (domain l E Y n).ι ⋙ H l E D f n,
      FormulaNormalized l E D hl f c n k := by
  sorry

/-- The canonical finite dual formula, chosen only from its unique evaluation/trace
normalization. Source: blueprint proof step 5
(blueprint: lem-coef-finite-exceptional). -/
def dualFormulaIso (n : ℕ) :
    G l E D hl f c n ⋙ (domain l E X n).ι ≅
      (domain l E Y n).ι ⋙ H l E D f n :=
  (dualFormula_existsUnique l E D hl f c n).exists.choose

/-- The compact-support comparison restricted through the full inclusion.
Its orientation is Q_Y F_m to F_n Q_X, as in the displayed unit/counit identities.
Source: blueprint second paragraph (blueprint: lem-coef-finite-exceptional). -/
def qMap {m n : ℕ} (h : n ≤ m) :
    F l E D hl f c m ⋙ Q l E Y h ⟶ Q l E X h ⋙ F l E D hl f c n :=
  ((domain l E Y n).fullyFaithfulι.whiskeringRight
    (domain l E X m).FullSubcategory).preimage
    (Functor.whiskerLeft (domain l E X m).ι (supportMap l E f c h))

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  PurCompactSupport.image

omit Xsep Ysep in
/-- The normalized coefficient comparison is invertible before choosing finite coordinates. -/
private theorem coefficientComparison_isIso
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (R : ConstructibleExceptionalCoefficients.RingSystem l Ω D hl (f := f))
    {s t : ConstructibleExceptionalCoefficients.RingStage.{u} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (ha : ConstructibleExceptionalCoefficients.Allowed l a)
    (K : ConstructibleExceptionalCoefficients.C l Ω X (s.stage l)) :
    IsIso ((PurCompactSupport.comparison a c).app
      ((ConstructibleExceptionalCoefficients.RingStage.inclusion l Ω X s).obj K)) := by
  let := (R.scalar (s := s) (t := t) a ha true).commShift
  let := (R.scalar (s := s) (t := t) a ha false).commShift
  let i :=
    (ConstructibleExceptionalCoefficients.RingStage.inclusion l Ω Y t).mapIso
        ((R.comparison c (s := s) (t := t) a ha).q.app K) ≪≫
      (R.left c t).app ((R.scalar (s := s) (t := t) a ha true).functor.obj K) ≪≫
      (PurCompactSupport.image (t.coefficients l) c).mapIso
        ((R.scalar (s := s) (t := t) a ha true).realization.app K)
  let j :=
    (R.scalar (s := s) (t := t) a ha false).realization.app ((R.operation c (s.stage l)).F.obj K) ≪≫
      (pbcDerivedExtend (a.map Y)).mapIso ((R.left c s).app K)
  have he : j.hom ≫ (PurCompactSupport.comparison a c).app
      ((ConstructibleExceptionalCoefficients.RingStage.inclusion l Ω X s).obj K) = i.hom := by
    simpa only [j, i, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Category.assoc] using (R.comparison_normalized c (s := s) (t := t) a ha K).symm
  have hi : IsIso (j.hom ≫ (PurCompactSupport.comparison a c).app
      ((ConstructibleExceptionalCoefficients.RingStage.inclusion l Ω X s).obj K)) :=
    he.symm ▸ i.isIso_hom
  exact IsIso.of_isIso_comp_left j.hom _

attribute [local irreducible] reductionDerivedChange PurCompactSupport.comparison
  PurCompactSupport.finiteImageIso in
/-- The actual compact-support comparison is invertible on the stated domain.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-finite-exceptional).
Proof: lem-fix-compact-support-coefficient-change gives invertibility on the etale
origin of every bounded constructible finite-Tor input. The canonical intrinsic
realization preserves this comparison. The full inclusion reflects isomorphisms. -/
theorem qMap_isIso {m n : ℕ} (h : n ≤ m) : IsIso (qMap l E D hl f c h) := by
  let Ω := AlgebraicClosure (ULift.{u} (Padic l))
  obtain ⟨S⟩ := ConstructibleExceptionalCoefficients.exists_system l Ω D hl f
  let R := S.ring
  let E' : ConstructibleExceptionalCoefficients.FieldStage.{u} l := { carrier := E }
  let s : ConstructibleExceptionalCoefficients.RingStage.{u} l :=
    .finite E' ⟨m + 1, Nat.succ_pos m⟩
  let t : ConstructibleExceptionalCoefficients.RingStage.{u} l :=
    .finite E' ⟨n + 1, Nat.succ_pos n⟩
  let a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l) :=
    PurCompactSupport.finiteQuotientChange l E
    (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) (Nat.add_le_add_right h 1)
  let ha : ConstructibleExceptionalCoefficients.Allowed l
      (s := .finite E' ⟨m + 1, Nat.succ_pos m⟩)
      (t := .finite E' ⟨n + 1, Nat.succ_pos n⟩) a :=
    .quotient E' ⟨m + 1, Nat.succ_pos m⟩ ⟨n + 1, Nat.succ_pos n⟩
      (Nat.add_le_add_right h 1)
  have hcomp (K : (domain l E X m).FullSubcategory) :
      IsIso ((PurCompactSupport.comparison a c).app K.obj) :=
    coefficientComparison_isIso l D hl f c Ω R (s := s) (t := t) a ha K
  let e : ((F l E D hl f c m ⋙ Q l E Y h) ⋙ (domain l E Y n).ι) ≅
      ((Q l E X h ⋙ F l E D hl f c n) ⋙ (domain l E Y n).ι) :=
    NatIso.ofComponents (fun K ↦
      (reduction l E Y h).mapIso ((PurCompactSupport.finiteImageIso l E m c).symm.app K.obj) ≪≫
        @asIso _ _ _ _ ((PurCompactSupport.comparison a c).app K.obj) (hcomp K) ≪≫
        (PurCompactSupport.finiteImageIso l E n c).app ((reduction l E X h).obj K.obj))
      (by
        intro K K' v
        exact (supportMap l E f c h).naturality v.hom)
  let ff := (domain l E Y n).fullyFaithfulι.whiskeringRight
    (domain l E X m).FullSubcategory
  exact (ff.preimageIso e).isIso_hom

/-- The canonical compact-support coefficient isomorphism.
Source: blueprint q_(m,n) (blueprint: lem-coef-finite-exceptional). -/
def q {m n : ℕ} (h : n ≤ m) :
    F l E D hl f c m ⋙ Q l E Y h ≅ Q l E X h ⋙ F l E D hl f c n :=
  @asIso _ _ _ _ (qMap l E D hl f c h) (qMap_isIso l E D hl f c h)

/-- The exceptional coefficient map is the counit transpose of inverse q. This
formula fixes the map itself before its invertibility, rather than choosing an
isomorphism. Source: blueprint proof paragraphs 2 and 3
(blueprint: lem-coef-finite-exceptional). -/
def b {m n : ℕ} (h : n ≤ m) :
    G l E D hl f c m ⋙ Q l E X h ⟶ Q l E Y h ⋙ G l E D hl f c n :=
  mateEquiv (adjunction l E D hl f c m) (adjunction l E D hl f c n)
    (q l E D hl f c h).inv

end WeilConjectures.FiniteExceptional
