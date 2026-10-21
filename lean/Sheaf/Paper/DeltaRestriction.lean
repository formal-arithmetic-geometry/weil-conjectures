/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP, SHEAF group Q145
-/
module

public import Sheaf.Paper.DualityPairing
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedRestrictionClosed
import WeilConjectures.SixFunctors.Etale.Derived.DoubleDualCompat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarInternalHom
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-! # Restriction of the evaluation-transpose double-dual morphism

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
order 2124; Stacks Project, Tags 08J9 and 08JB
(blueprint: lem-weil-delta-restriction).

The comparisons below are normalized by evaluation and by the compact-support counit.
All categories are ordinary unbounded categories of constant-ring module sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true

universe u v w z z'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

/-- Evaluation with the factors in the order DK tensor K.
Source: blueprint order 2124, evaluation of lem-weil-duality-pairing; Stacks 08J9
(blueprint: lem-weil-delta-restriction). -/
def restrictionDualEvaluation {C : Type z} [Category.{v} C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (adj : ∀ K : C, T.obj K ⊣ H.obj (op K))
    (b : ∀ K L : C, (T.obj K).obj L ≅ (T.obj L).obj K) (Ω K : C) :
    (T.obj ((H.obj (op K)).obj Ω)).obj K ⟶ Ω :=
  (b _ _).hom ≫ (adj K).counit.app Ω

/-- The double-dual arrow is the actual transpose of evaluation.
Source: blueprint order 2124, lem-weil-duality-pairing; Stacks 08J9
(blueprint: lem-weil-delta-restriction). -/
def restrictionDualDelta {C : Type z} [Category.{v} C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (adj : ∀ K : C, T.obj K ⊣ H.obj (op K))
    (b : ∀ K L : C, (T.obj K).obj L ≅ (T.obj L).obj K) (Ω K : C) :
    K ⟶ (dualityDoubleFunctor H Ω).obj K :=
  (adj ((H.obj (op K)).obj Ω)).homEquiv K Ω
    (restrictionDualEvaluation T H adj b Ω K)

/-- The canonical natural restriction isomorphism, its evaluation normalization, the
contravariant double-dual identity, and its transported form.
Source: blueprint order 2124, displayed identity and following sentence; Stacks 08JB
(blueprint: lem-weil-delta-restriction). -/
def DualDeltaRestriction {C : Type z} [Category.{v} C]
    {D : Type z'} [Category.{w} D] (r : C ⥤ D)
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (T' : D ⥤ D ⥤ D) (H' : Dᵒᵖ ⥤ D ⥤ D)
    (adj : ∀ K : C, T.obj K ⊣ H.obj (op K))
    (adj' : ∀ K : D, T'.obj K ⊣ H'.obj (op K))
    (b : ∀ K L : C, (T.obj K).obj L ≅ (T.obj L).obj K)
    (b' : ∀ K L : D, (T'.obj K).obj L ≅ (T'.obj L).obj K)
    (μ : ∀ K L : C, (T'.obj (r.obj K)).obj (r.obj L) ≅ r.obj ((T.obj K).obj L))
    (Ω : C) (Ω' : D) (θ : r.obj Ω ≅ Ω') : Prop :=
  ∃ α : H.flip.obj Ω ⋙ r ≅ r.op ⋙ H'.flip.obj Ω',
    (∀ K : C, α.hom.app (op K) =
      (adj' (r.obj K)).homEquiv (r.obj ((H.obj (op K)).obj Ω)) Ω'
        ((μ K ((H.obj (op K)).obj Ω)).hom ≫ r.map ((adj K).counit.app Ω) ≫ θ.hom)) ∧
    (∀ K : C,
      r.map (restrictionDualDelta T H adj b Ω K) ≫
          α.hom.app (op ((H.obj (op K)).obj Ω)) =
        restrictionDualDelta T' H' adj' b' Ω' (r.obj K) ≫
          (H'.map (α.hom.app (op K)).op).app Ω') ∧
    (∀ K : C,
      r.map (restrictionDualDelta T H adj b Ω K) ≫
          (α.app (op ((H.obj (op K)).obj Ω)) ≪≫
            ((H'.mapIso (α.app (op K)).op).app Ω').symm).hom =
        restrictionDualDelta T' H' adj' b' Ω' (r.obj K))

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionDualDelta_isIso_iff {C : Type z} [Category.{v} C]
    {D : Type z'} [Category.{w} D] (r : C ⥤ D)
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (T' : D ⥤ D ⥤ D) (H' : Dᵒᵖ ⥤ D ⥤ D)
    (adj : ∀ K : C, T.obj K ⊣ H.obj (op K))
    (adj' : ∀ K : D, T'.obj K ⊣ H'.obj (op K))
    (b : ∀ K L : C, (T.obj K).obj L ≅ (T.obj L).obj K)
    (b' : ∀ K L : D, (T'.obj K).obj L ≅ (T'.obj L).obj K)
    (μ : ∀ K L : C, (T'.obj (r.obj K)).obj (r.obj L) ≅ r.obj ((T.obj K).obj L))
    (Ω : C) (Ω' : D) (θ : r.obj Ω ≅ Ω')
    (h : DualDeltaRestriction r T H T' H' adj adj' b b' μ Ω Ω' θ) (K : C) :
    IsIso (r.map (restrictionDualDelta T H adj b Ω K)) ↔
      IsIso (restrictionDualDelta T' H' adj' b' Ω' (r.obj K)) := by
  obtain ⟨α, _, _, hδ⟩ := h
  rw [← hδ K, isIso_comp_right_iff]

set_option backward.isDefEq.respectTransparency false in
private def restrictionTensorRepackage {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (T : D ⥤ D ⥤ D) (S : C ⥤ C ⥤ C)
    (e : (((Functor.whiskeringLeft₂ D).obj F).obj F).obj T ≅
      (Functor.postcompose₂.obj F).obj S) :
    Functor.curry.obj (F.prod F ⋙ Functor.uncurry.obj T) ≅
      Functor.curry.obj (Functor.uncurry.obj S ⋙ F) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ (e.app X).app Y)
    (fun g ↦ by simpa using (e.hom.app X).naturality g))
    (fun f ↦ by
      ext Y
      have h := congr_app (e.hom.naturality f) Y
      dsimp at h ⊢
      rw [F.map_id, (T.obj _).map_id, Category.comp_id,
        (S.obj _).map_id, Category.comp_id]
      exact h)

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionTensorNormalized
    {C D : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] :
    ∃ e : Functor.curry.obj (F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
        Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D))) ≅
        Functor.curry.obj (Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙
          F.mapDerivedCategory),
    ∀ P Q : HomotopyCategory C (.up ℤ),
      F.mapDerivedCategory.map (Functor.LaxMonoidal.μ _root_.DerivedCategory.Qh P Q) ≫
        F.mapDerivedCategoryFactorsh.hom.app (P ⊗ Q) ≫
        _root_.DerivedCategory.Qh.map
          (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app P).app Q) =
      (e.inv.app (_root_.DerivedCategory.Qh.obj P)).app (_root_.DerivedCategory.Qh.obj Q) ≫
        (F.mapDerivedCategoryFactorsh.hom.app P ⊗ₘ F.mapDerivedCategoryFactorsh.hom.app Q) ≫
        Functor.LaxMonoidal.μ _root_.DerivedCategory.Qh
          ((F.mapHomotopyCategory (.up ℤ)).obj P) ((F.mapHomotopyCategory (.up ℤ)).obj Q) := by
  let a := F.leftDerivedFunctorIsoMapDerivedCategory
  let t := curriedTensor (_root_.DerivedCategory D)
  let b := (((Functor.whiskeringLeft₂ _).mapIso a).app F.leftDerivedFunctor).app t
  let c := (((Functor.whiskeringLeft₂ _).obj F.mapDerivedCategory).mapIso a).app t
  let d := (Functor.postcompose₂.mapIso a).app (curriedTensor (_root_.DerivedCategory C))
  let e := c.symm ≪≫ b.symm ≪≫ (asIso F.leftDerivedTensorComparison).symm ≪≫ d
  refine ⟨restrictionTensorRepackage F.mapDerivedCategory t
    (curriedTensor (_root_.DerivedCategory C)) e, ?_⟩
  intro P Q
  have he : ((restrictionTensorRepackage F.mapDerivedCategory t
      (curriedTensor (_root_.DerivedCategory C)) e).inv.app
      (_root_.DerivedCategory.Qh.obj P)).app (_root_.DerivedCategory.Qh.obj Q) =
      a.inv.app (_root_.DerivedCategory.Qh.obj P ⊗ _root_.DerivedCategory.Qh.obj Q) ≫
      (F.leftDerivedTensorComparison.app (_root_.DerivedCategory.Qh.obj P)).app
        (_root_.DerivedCategory.Qh.obj Q) ≫
      (a.hom.app (_root_.DerivedCategory.Qh.obj P) ⊗ₘ
        a.hom.app (_root_.DerivedCategory.Qh.obj Q)) := by
    dsimp [restrictionTensorRepackage, e, b, c, d, t]
    rw [MonoidalCategory.tensorHom_def]
    simp only [Category.assoc]
  rw [he]
  have h := F.leftDerivedTensorComparison_app_app_comp_tensorHom P Q
  have ha (X : HomotopyCategory C (.up ℤ)) :
      a.hom.app (_root_.DerivedCategory.Qh.obj X) ≫
        F.mapDerivedCategoryFactorsh.hom.app X = F.leftDerivedFunctorCounit.app X :=
    congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac X
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, ha P, ha Q, h]
  rw [← cancel_epi (a.hom.app (_root_.DerivedCategory.Qh.obj P ⊗
    _root_.DerivedCategory.Qh.obj Q))]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← a.hom.naturality_assoc, reassoc_of% (ha (P ⊗ Q))]

end CategoryTheory

open CategoryTheory.MonoidalClosed

namespace CategoryTheory
set_option backward.isDefEq.respectTransparency false
private theorem canonicalRestriction {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
    [BraidedCategory C] [BraidedCategory D] (G : C ⥤ D) [G.LaxBraided]
    [∀ X Y, IsIso (Functor.LaxMonoidal.μ G X Y)]
    (h : ∀ X : C, IsIso (Functor.LaxMonoidal.ihomComparison G X).natTrans)
    (Ω : C) (Ω' : D) (θ : G.obj Ω ≅ Ω') :
    DualDeltaRestriction G (curriedTensor C) internalHom (curriedTensor D) internalHom
      internalHomAdjunction₂.adj internalHomAdjunction₂.adj
      (fun X Y ↦ β_ X Y) (fun X Y ↦ β_ X Y)
      (fun X Y ↦ asIso (Functor.LaxMonoidal.μ G X Y)) Ω Ω' θ := by
  let a : internalHom.flip.obj Ω ⋙ G ⟶ G.op ⋙ internalHom.flip.obj Ω' :=
    { app := fun X ↦ dualComparison G θ.hom X.unop
      naturality := fun X Y f ↦ by
        dsimp [dualComparison]
        simp only [internalHom_map]
        rw [Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app_assoc, Category.assoc]
        exact congrArg ((Functor.LaxMonoidal.ihomComparison G X.unop).natTrans.app Ω ≫ ·)
          ((pre (G.map f.unop)).naturality θ.hom).symm }
  have ha (X : Cᵒᵖ) : IsIso (a.app X) := by
    have := h X.unop
    dsimp [a, dualComparison]
    infer_instance
  have : IsIso a := (NatTrans.isIso_iff_isIso_app a).2 ha
  let α : internalHom.flip.obj Ω ⋙ G ≅ G.op ⋙ internalHom.flip.obj Ω' :=
    asIso a
  refine ⟨α, ?_, ?_, ?_⟩
  · intro K
    change dualComparison G θ.hom K = _
    rw [dualComparison, Functor.LaxMonoidal.ihomComparison_app_eq_curry,
      ← curry_natural_right]
    simp only [internalHomAdjunction₂_adj, curry,
      ihom.ihom_adjunction_counit, asIso_hom, Category.assoc]
    rfl
  · intro K
    simpa [restrictionDualDelta, restrictionDualEvaluation, toIhomIhom, α, a, curry, internalHom]
      using map_toIhomIhom_comp_dualComparison G θ.hom K
  · intro K
    apply (cancel_mono ((internalHom.mapIso (α.app (op K)).op).app Ω').hom).1
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    simpa [restrictionDualDelta, restrictionDualEvaluation, toIhomIhom, α, a,
      curry, internalHom]
      using map_toIhomIhom_comp_dualComparison G θ.hom K
end CategoryTheory

namespace CategoryTheory
set_option backward.isDefEq.respectTransparency false
private theorem transportedBraiding {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    {F G : C ⥤ D} [F.Monoidal]
    (h : ∀ X Y, Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
      (β_ (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F Y X)
    (e : F ≅ G) :
    letI := Functor.Monoidal.transport e
    ∀ X Y, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
      (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X := by
  let := Functor.Monoidal.transport e
  have : e.hom.IsMonoidal := Functor.Monoidal.natTransIsMonoidal_of_transport e
  intro X Y
  rw [← cancel_epi (e.hom.app X ⊗ₘ e.hom.app Y),
    ← NatTrans.IsMonoidal.tensor_assoc, ← e.hom.naturality, ← Category.assoc, h,
    Category.assoc, NatTrans.IsMonoidal.tensor,
    ← BraidedCategory.braiding_naturality_assoc]
end CategoryTheory

namespace CategoryTheory
set_option backward.isDefEq.respectTransparency false
private theorem canonicalRestrictionTransport {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
    [BraidedCategory C] [BraidedCategory D] {F G : C ⥤ D} [F.Monoidal]
    (hb : ∀ X Y, Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
      (β_ (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F Y X)
    (h : ∀ X : C, IsIso (Functor.LaxMonoidal.ihomComparison F X).natTrans)
    (e : F ≅ G) (Ω : C) (Ω' : D) (θ : G.obj Ω ≅ Ω') :
    letI := Functor.Monoidal.transport e
    DualDeltaRestriction G (curriedTensor C) internalHom (curriedTensor D) internalHom
      internalHomAdjunction₂.adj internalHomAdjunction₂.adj
      (fun X Y ↦ β_ X Y) (fun X Y ↦ β_ X Y)
      (fun X Y ↦ asIso (Functor.LaxMonoidal.μ G X Y)) Ω Ω' θ := by
  let := Functor.Monoidal.transport e
  let : G.LaxBraided := { braided := transportedBraiding hb e }
  have : e.hom.IsMonoidal := Functor.Monoidal.natTransIsMonoidal_of_transport e
  have : e.symm.hom.IsMonoidal := inferInstanceAs (NatTrans.IsMonoidal e.inv)
  apply canonicalRestriction G _ Ω Ω' θ
  intro X
  have := h X
  exact Functor.LaxMonoidal.isIso_ihomComparison_of_iso e.symm X
end CategoryTheory

namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency false
attribute [local instance] derivedBraidedCategory
private theorem genericEtaleRestriction
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A] {W Y : Scheme.{u}} (j : W ⟶ Y)
    (h : ∀ X : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A),
      letI := leftDerivedUpperStarMonoidal A j
      IsIso (Functor.LaxMonoidal.ihomComparison (upperStar A j).leftDerivedFunctor X).natTrans)
    (Ω : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (Ω' : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A))
    (θ : (upperStar A j).mapDerivedCategory.obj Ω ≅ Ω') :
    DualDeltaRestriction (upperStar A j).mapDerivedCategory
      (derivedTensor A Y) (derivedHom A Y) (derivedTensor A W) (derivedHom A W)
      (derivedTensorHomAdjunction A) (derivedTensorHomAdjunction A)
      (fun K L ↦ β_ K L) (fun K L ↦ β_ K L)
      (fun K L ↦
        ((derivedTensor A W).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory A j).app K).symm).app
            ((upperStar A j).mapDerivedCategory.obj L) ≪≫
        ((derivedTensor A W).obj _).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory A j).app L).symm ≪≫
        (leftDerivedUpperStarTensorIso A j K L).symm ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory A j).app _) Ω Ω' θ := by
  let := leftDerivedUpperStarMonoidal A j
  have hr := CategoryTheory.canonicalRestrictionTransport
    (leftDerivedUpperStar_μ_map_braiding_hom A j) h
    (leftDerivedUpperStarIsoMapDerivedCategory A j) Ω Ω' θ
  dsimp only [derivedTensor, derivedHom, derivedTensorHomAdjunction,
    derivedTensorHomAdjunction₂]
  convert hr using 1
  · funext K
    rfl
  · funext K
    rfl
  · funext K L
    apply Iso.ext
    dsimp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [asIso_hom]
    rw [Functor.Monoidal.transport_μ]
    rw [MonoidalCategory.tensorHom_def]
    have hμ : Functor.LaxMonoidal.μ (upperStar A j).leftDerivedFunctor K L =
        (leftDerivedUpperStarTensorIso A j K L).inv := by
      apply (cancel_mono (leftDerivedUpperStarTensorIso A j K L).hom).1
      rw [Iso.inv_hom_id, leftDerivedUpperStarTensorIso_hom,
        ← leftDerivedUpperStar_δ_eq A j K L, Functor.Monoidal.μ_δ]
    rw [hμ]
    simp only [Category.assoc]
    rfl
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry

namespace Etale

/-- Construct the descended Koszul braiding prescribed by the pairing assertion.
Its prescribed components determine the natural isomorphism, so the construction is
independent of the proof of the assertion.
Source: blueprint order 2124, evaluation restriction; Stacks 08J9
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionPairingBraiding
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u})
    (Ω : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (h : AmbientDualityPairing A Y Ω) :
    derivedTensor A Y ≅ (derivedTensor A Y).flip :=
  letI := derivedBraidedCategory A Y
  let _ := h
  BraidedCategory.curriedBraidingNatIso _

section
attribute [local instance] derivedBraidedCategory
set_option backward.isDefEq.respectTransparency false in
private theorem pairedEtaleRestriction
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A] {W Y : Scheme.{u}} (j : W ⟶ Y)
    (h : ∀ X : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A),
      letI := leftDerivedUpperStarMonoidal A j
      IsIso (Functor.LaxMonoidal.ihomComparison (upperStar A j).leftDerivedFunctor X).natTrans)
    (Ω : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (Ω' : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A))
    (θ : (upperStar A j).mapDerivedCategory.obj Ω ≅ Ω')
    (hΩ : AmbientDualityPairing A Y Ω) (hΩ' : AmbientDualityPairing A W Ω') :
    DualDeltaRestriction (upperStar A j).mapDerivedCategory
      (derivedTensor A Y) (derivedHom A Y) (derivedTensor A W) (derivedHom A W)
      (derivedTensorHomAdjunction A) (derivedTensorHomAdjunction A)
      (fun K L ↦ ((deltaRestrictionPairingBraiding A Y Ω hΩ).app K).app L)
      (fun K L ↦ ((deltaRestrictionPairingBraiding A W Ω' hΩ').app K).app L)
      (fun K L ↦
        ((derivedTensor A W).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory A j).app K).symm).app
            ((upperStar A j).mapDerivedCategory.obj L) ≪≫
        ((derivedTensor A W).obj _).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory A j).app L).symm ≪≫
        (leftDerivedUpperStarTensorIso A j K L).symm ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory A j).app _) Ω Ω' θ := by
  simpa only [deltaRestrictionPairingBraiding, BraidedCategory.curriedBraidingNatIso,
    NatIso.ofComponents.app] using genericEtaleRestriction A j h Ω Ω' θ

end

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The unique Koszul braiding specified componentwise by the pairing theorem.
The witness is determined by its equality with the descended braiding, so this selection
contains no arbitrary monoidal structure or pairing.
Source: blueprint order 2124, lem-weil-duality-pairing; Stacks 06YU and 0FPT
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionBraiding {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    derivedTensor (ModuleCat.{u + 1} Λ) Y ≅ (derivedTensor (ModuleCat.{u + 1} Λ) Y).flip :=
  deltaRestrictionPairingBraiding (ModuleCat.{u + 1} Λ) Y
    (dualizingComplex (ModuleCat.{u + 1} Λ) aY) ((ambient_duality_pairing Λ aY).1)

/-- The canonical tensor comparison for exact restriction; it transports the existing
K-flat-derived pullback comparison through L j* = D j*.
Source: blueprint order 2124, proof step 4; Stacks 08JB
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionTensorIso {W Y : Scheme.{u}} (j : W ⟶ Y)
    (K L : DerivedCategoryModule Λ Y) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
        ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj K)).obj
          ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj L) ≅
      (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj K).obj L) :=
  ((derivedTensor (ModuleCat.{u + 1} Λ) W).mapIso
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app K).symm).app
      ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj L) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) W).obj _).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app L).symm ≪≫
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) j K L).symm ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app _

/-- The canonical evaluation-transpose map into the double dual for any ambient object.
Source: blueprint order 2124, lem-weil-duality-pairing; Stacks 08J9
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionMap {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (Ω K : DerivedCategoryModule Λ Y) :
    K ⟶ (dualityDoubleFunctor (derivedHom (ModuleCat.{u + 1} Λ) Y) Ω).obj K :=
  restrictionDualDelta (derivedTensor (ModuleCat.{u + 1} Λ) Y)
    (derivedHom (ModuleCat.{u + 1} Λ) Y)
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ))
    (fun K L ↦ ((deltaRestrictionBraiding Λ aY).app K).app L) Ω K

/-- The dualizing comparison is the unique, counit-normalized adjoint-locality isomorphism
at the constant coefficient object. The Noetherian and compactification conditions are
consequences of the stated finite-type hypotheses, rather than additional assumptions.
Source: blueprint order 2124, proof step 1, lem-amb-etale-adjoint-locality
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionDualizingIso {k : Type u} [Field k]
    {W Y : Scheme.{u}} (j : W ⟶ Y) (aY : Y ⟶ Spec (.of k)) [Etale j]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated (j ≫ aY)] [LocallyOfFiniteType (j ≫ aY)] [QuasiCompact (j ≫ aY)] :
    (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (dualizingComplex (ModuleCat.{u + 1} Λ) aY) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (j ≫ aY) :=
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  letI : IsNoetherian Y := ⟨⟩
  letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (j ≫ aY)
  letI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (j ≫ aY)
  letI : IsNoetherian W := ⟨⟩
  letI : IsSeparated j := IsSeparated.of_comp j aY
  (Classical.choose (existsUnique_etaleAmbientAdjointLocalityIso Λ j aY
    (HasCompactification.compactification aY)
    (HasCompactification.compactification (j ≫ aY))
    (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) aY)
    (rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) (j ≫ aY))
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) aY)
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (j ≫ aY)))).app
      (constantComplex Λ (Spec (.of k)))

set_option backward.isDefEq.respectTransparency false in
/-- Etale restriction commutes with the evaluation-transpose double-dual morphism,
including the canonical natural comparison and its variance.
Source: blueprint order 2124; Stacks 08J9 and 08JB
(blueprint: lem-weil-delta-restriction).

Proof:
1. The existing adjoint-locality comparison identifies the dualizing objects; its
   Noetherian and compactification hypotheses follow from the stated finite-type data.
2. The source-library derived inverse image is braided strong monoidal, and its closed
   comparison is invertible for etale j. Transport both properties along its natural
   isomorphism to the exact derived restriction.
3. Postcompose the closed comparison with theta. Naturality gives alpha, and the
   defining closed-comparison equation gives its evaluation compatibility.
4. Apply the categorical double-dual compatibility for braided monoidal functors.
   The canonical Koszul braiding is the one prescribed by the ambient pairing assertion.
   Cancelling the inverse contravariant comparison gives the transported form.
-/
theorem delta_restriction {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {W Y : Scheme.{u}} (j : W ⟶ Y) (aY : Y ⟶ Spec (.of k)) [Etale j]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated (j ≫ aY)] [LocallyOfFiniteType (j ≫ aY)] [QuasiCompact (j ≫ aY)] :
    DualDeltaRestriction (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory
      (derivedTensor (ModuleCat.{u + 1} Λ) Y) (derivedHom (ModuleCat.{u + 1} Λ) Y)
      (derivedTensor (ModuleCat.{u + 1} Λ) W) (derivedHom (ModuleCat.{u + 1} Λ) W)
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ))
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ))
      (fun K L ↦ ((deltaRestrictionBraiding Λ aY).app K).app L)
      (fun K L ↦ ((deltaRestrictionBraiding Λ (j ≫ aY)).app K).app L)
      (deltaRestrictionTensorIso Λ j)
      (dualizingComplex (ModuleCat.{u + 1} Λ) aY)
      (dualizingComplex (ModuleCat.{u + 1} Λ) (j ≫ aY))
      (deltaRestrictionDualizingIso Λ j aY) := by
  exact pairedEtaleRestriction (ModuleCat.{u + 1} Λ) j
    (fun X ↦ isIso_ihomComparison_leftDerivedUpperStar_of_etale Λ j X) _ _
    (deltaRestrictionDualizingIso Λ j aY)
    ((ambient_duality_pairing Λ aY).1) ((ambient_duality_pairing Λ (j ≫ aY)).1)

/-- The double-dual map is an isomorphism precisely when the corresponding double-dual
maps on a jointly surjective etale covering are isomorphisms, including an empty covering.
Source: blueprint order 2124, locality assertion
(blueprint: lem-weil-delta-restriction).

Proof:
1. Exact restriction commutes with cohomology sheaves in every integer degree.
2. Use lem-weil-pbc-etale-cover-detects-iso on the underlying abelian sheaves. The inverse
   of an invertible A-linear map is A-linear, so forgetting coefficients reflects isomorphisms.
3. The unbounded criterion lem-weil-pbc-unbounded-derived-iso-cohomology detects derived
   isomorphisms. Apply it to delta and use delta_restriction to identify its restrictions.
4. For an empty covering joint surjectivity forces Y to be empty; its module category is
   zero, so the criterion still holds. No boundedness hypothesis occurs.
-/
theorem isIso_delta_iff_etale_cover {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    {I : Type w} (W : I → Scheme.{u}) (j : ∀ i : I, W i ⟶ Y) [∀ i : I, Etale (j i)]
    [∀ i : I, IsSeparated (j i ≫ aY)] [∀ i : I, LocallyOfFiniteType (j i ≫ aY)]
    [∀ i : I, QuasiCompact (j i ≫ aY)]
    (hj : ∀ y : Y, ∃ (i : I) (x : W i), (j i).base x = y)
    (K : DerivedCategoryModule Λ Y) :
    IsIso (deltaRestrictionMap Λ aY (dualizingComplex (ModuleCat.{u + 1} Λ) aY) K) ↔
      ∀ i : I, IsIso (deltaRestrictionMap Λ (j i ≫ aY)
        (dualizingComplex (ModuleCat.{u + 1} Λ) (j i ≫ aY))
        ((upperStar (ModuleCat.{u + 1} Λ) (j i)).mapDerivedCategory.obj K)) := by
  classical
  let d := deltaRestrictionMap Λ aY (dualizingComplex (ModuleCat.{u + 1} Λ) aY) K
  have local_iff (i : I) :
      IsIso ((upperStar (ModuleCat.{u + 1} Λ) (j i)).mapDerivedCategory.map d) ↔
      IsIso (deltaRestrictionMap Λ (j i ≫ aY)
        (dualizingComplex (ModuleCat.{u + 1} Λ) (j i ≫ aY))
        ((upperStar (ModuleCat.{u + 1} Λ) (j i)).mapDerivedCategory.obj K)) := by
    exact restrictionDualDelta_isIso_iff _ _ _ _ _ _ _ _ _ _ _ _ _
      (delta_restriction Λ (j i) aY) K
  constructor
  · intro h i
    exact (local_iff i).1 (by infer_instance)
  · intro h
    have hl (i : I) := (local_iff i).2 (h i)
    let index : Y → I := fun y ↦ (hj y).choose
    let point (y : Y) : W (index y) := (hj y).choose_spec.choose
    have hp (y : Y) : (j (index y)).base (point y) = y :=
      (hj y).choose_spec.choose_spec
    apply isIso_of_forall_isIso_leftDerivedUpperStar_map Λ (fun y : Y ↦ j (index y))
      (fun y ↦ ⟨y, point y, hp y⟩) d
    intro y
    exact (NatIso.isIso_map_iff
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) (j (index y))) d).2
      (hl (index y))

end Etale

namespace ProEtale


/-- The existing native derived internal Hom, with its plain bifunctor signature exposed.
Source: blueprint order 2124, proof step 4 (blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionNativeHom
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u}) :
    (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))ᵒᵖ ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ⥤
        _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  MonoidalClosed.internalHom

/-- The adjunction of the native tensor and internal Hom, without changing its unit or counit.
Source: blueprint order 2124, proof step 4 (blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionNativeAdjunction
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u}) (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (deltaRestrictionNativeTensor A Y).obj K ⊣
      (deltaRestrictionNativeHom A Y).obj (op K) :=
  MonoidalClosed.internalHomAdjunction₂.adj K


/-- Construct the descended Koszul braiding prescribed by the pairing assertion.
Its prescribed components determine the natural isomorphism, so the construction is
independent of the proof of the assertion.
Source: blueprint order 2124, evaluation restriction; Stacks 08J9
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionPairingBraiding
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u})
    (Ω : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (h : AmbientDualityPairing A Y Ω) :
    deltaRestrictionNativeTensor A Y ≅
      (deltaRestrictionNativeTensor A Y).flip :=
  letI := _root_.DerivedCategory.braidedCategory' (Sheaf (Scheme.ProEt.topology Y) A)
  let _ := h
  BraidedCategory.curriedBraidingNatIso _

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The unique descended Koszul braiding specified by the pro-etale pairing theorem.
Its componentwise normalization determines the selected natural isomorphism, independently
of Omega; it is not a choice of an arbitrary braiding.
Source: blueprint order 2124, lem-weil-duality-pairing; Stacks 06YU and 0FPT
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionBraiding {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (Ω : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    deltaRestrictionNativeTensor (ModuleCat.{u + 1} Λ) Y ≅
      (deltaRestrictionNativeTensor (ModuleCat.{u + 1} Λ) Y).flip :=
  deltaRestrictionPairingBraiding (ModuleCat.{u + 1} Λ) Y Ω
    ((Etale.ambient_duality_pairing Λ aY).2 Ω)

set_option backward.isDefEq.respectTransparency false in
private theorem proEtaleNormalizedTensor
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {W Y : Scheme.{u}} (j : W ⟶ Y) :
    ∃ e : DeltaRestrictionTensorComparison A j,
      IsNormalizedDeltaRestrictionTensor A j e := by
  exact restrictionTensorNormalized (upperStar A j)

set_option backward.isDefEq.respectTransparency false in
private theorem proEtaleRestrictionFromClosed
    (A : Type z) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A] {W Y : Scheme.{u}} (j : W ⟶ Y) [WeaklyEtale j]
    (e : DeltaRestrictionTensorComparison A j) (he : IsNormalizedDeltaRestrictionTensor A j e)
    (Ω : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (Ω' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology W) A))
    (θ : (upperStar A j).mapDerivedCategory.obj Ω ≅ Ω')
    (hΩ : AmbientDualityPairing A Y Ω) (hΩ' : AmbientDualityPairing A W Ω') :
    letI := _root_.DerivedCategory.braidedCategory' (Sheaf (Scheme.ProEt.topology Y) A)
    letI := _root_.DerivedCategory.braidedCategory' (Sheaf (Scheme.ProEt.topology W) A)
    DualDeltaRestriction (upperStar A j).mapDerivedCategory
      (deltaRestrictionNativeTensor A Y) (deltaRestrictionNativeHom A Y)
      (deltaRestrictionNativeTensor A W) (deltaRestrictionNativeHom A W)
      (deltaRestrictionNativeAdjunction A Y) (deltaRestrictionNativeAdjunction A W)
      (fun K L ↦ ((deltaRestrictionPairingBraiding A Y Ω hΩ).app K).app L)
      (fun K L ↦ ((deltaRestrictionPairingBraiding A W Ω' hΩ').app K).app L)
      (fun K L ↦ (e.app K).app L) Ω Ω' θ := by
  let := _root_.DerivedCategory.braidedCategory' (Sheaf (Scheme.ProEt.topology Y) A)
  let := _root_.DerivedCategory.braidedCategory' (Sheaf (Scheme.ProEt.topology W) A)
  obtain ⟨m, hμ, hb, hh⟩ := exists_normalizedRestrictionMonoidalClosed A j e he
  let := m
  let : (upperStar A j).mapDerivedCategory.LaxBraided := { braided := hb }
  have hc := CategoryTheory.canonicalRestriction (upperStar A j).mapDerivedCategory
    hh Ω Ω' θ
  have hμiso (K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
      (e.app K).app L = asIso (Functor.LaxMonoidal.μ (upperStar A j).mapDerivedCategory K L) := by
    apply Iso.ext
    exact (hμ K L).symm
  have hAY : deltaRestrictionNativeAdjunction A Y =
      (fun K ↦ MonoidalClosed.internalHomAdjunction₂.adj K) := rfl
  have hAW : deltaRestrictionNativeAdjunction A W =
      (fun K ↦ MonoidalClosed.internalHomAdjunction₂.adj K) := rfl
  simpa only [deltaRestrictionPairingBraiding, BraidedCategory.curriedBraidingNatIso,
    NatIso.ofComponents.app, deltaRestrictionNativeTensor, deltaRestrictionNativeHom,
    hAY, hAW, hμiso] using hc

/-- The derived tensor comparison is fixed by the ordinary oplax tensor comparison
on every homotopy complex. This normalization determines the natural isomorphism uniquely.
Source: blueprint order 2124, final clause, proof step 4; Stacks 08JB
(blueprint: lem-weil-delta-restriction).

Proof: The exact inverse image is strong monoidal and preserves flat sheaves and
coproducts. Apply it to K-flat resolutions in both variables. The ordinary tensor
comparison is an isomorphism there and descends through the quasi-isomorphism
localizations. The ordinary comparison first descends to homotopy categories.
Its square with the localization lax tensor maps is the displayed
identity. Naturality and the essential surjectivity of K-flat localization determine
all its components, so the chosen data are uniquely normalized.
-/
theorem deltaRestrictionTensorComparison_normalized {W Y : Scheme.{u}} (j : W ⟶ Y) :
    ∃ e : DeltaRestrictionTensorComparison (ModuleCat.{u + 1} Λ) j,
      IsNormalizedDeltaRestrictionTensor (ModuleCat.{u + 1} Λ) j e := by
  exact proEtaleNormalizedTensor (ModuleCat.{u + 1} Λ) j

/-- Canonical derived tensor comparison for ordinary constant-coefficient pro-etale sheaves.
The representative normalization above determines the selected data.
Source: blueprint order 2124, final clause; Stacks 08JB
(blueprint: lem-weil-delta-restriction). -/
def deltaRestrictionTensorIso {W Y : Scheme.{u}} (j : W ⟶ Y)
    (K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    ((deltaRestrictionNativeTensor (ModuleCat.{u + 1} Λ) W).obj
        ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj K)).obj
          ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj L) ≅
      (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (((deltaRestrictionNativeTensor (ModuleCat.{u + 1} Λ) Y).obj K).obj L) :=
  ((deltaRestrictionTensorComparison_normalized Λ j).choose.app K).app L

set_option backward.isDefEq.respectTransparency false in
/-- The same restriction identity on the small pro-etale sites, for an arbitrary specified
ambient object Omega and its inverse image. This concerns ordinary module sheaves, with no
pro-etale exceptional-adjoint or condensed-coefficient assertion.
Source: blueprint order 2124, final clause; Stacks 08J9 and 08JB
(blueprint: lem-weil-delta-restriction).

Proof:
1. Etale j is weakly etale. Apply the separate normalized native closed monoidal
   restriction theorem to the specified tensor comparison and its homotopy square.
2. Use its tensor-map equality, braided identity and invertible closed comparison
   in the generic categorical restriction argument. Postcomposition is the identity
   because Omega_W is the restriction of Omega_Y.
3. Evaluation compatibility follows from the defining closed comparison. Categorical
   double-dual compatibility and inverse cancellation give both required identities.
   No pro-etale exceptional adjoint is used.
-/
theorem delta_restriction {k : Type u} [Field k]
    [HasInvertibleExponent Λ (Spec (.of k))]
    {W Y : Scheme.{u}} (j : W ⟶ Y) (aY : Y ⟶ Spec (.of k)) [Etale j]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated (j ≫ aY)] [LocallyOfFiniteType (j ≫ aY)] [QuasiCompact (j ≫ aY)]
    (Ω : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    DualDeltaRestriction (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory
      (deltaRestrictionNativeTensor (ModuleCat.{u + 1} Λ) Y)
      (deltaRestrictionNativeHom (ModuleCat.{u + 1} Λ) Y)
      (deltaRestrictionNativeTensor (ModuleCat.{u + 1} Λ) W)
      (deltaRestrictionNativeHom (ModuleCat.{u + 1} Λ) W)
      (deltaRestrictionNativeAdjunction (ModuleCat.{u + 1} Λ) Y)
      (deltaRestrictionNativeAdjunction (ModuleCat.{u + 1} Λ) W)
      (fun K L ↦ ((deltaRestrictionBraiding Λ aY Ω).app K).app L)
      (fun K L ↦ ((deltaRestrictionBraiding Λ (j ≫ aY)
        ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj Ω)).app K).app L)
      (deltaRestrictionTensorIso Λ j) Ω
      ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj Ω) (Iso.refl _) := by
  exact proEtaleRestrictionFromClosed (ModuleCat.{u + 1} Λ) j
    (deltaRestrictionTensorComparison_normalized Λ j).choose
    (deltaRestrictionTensorComparison_normalized Λ j).choose_spec Ω _ (Iso.refl _)
    ((Etale.ambient_duality_pairing Λ aY).2 Ω)
    ((Etale.ambient_duality_pairing Λ (j ≫ aY)).2 _)

end ProEtale

end AlgebraicGeometry
