/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Algebra.Homology.ScalarInternalHomData
import all Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Coherence of normalized scalar tensor comparisons

Source: Stacks 07A4 and 0D6D. The pure-generator equations determine the chain
comparisons before their coherence descends to unbounded derived categories.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r w u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures SheafOfModules CategoryTheory.Functor
namespace CategoryTheory.ScalarHomTensor
section ExactRestrictionComposition
attribute [local instance] Limits.comp_preservesFiniteLimits Limits.comp_preservesFiniteColimits
private theorem exact_comp_fac
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    [F.Additive] [G.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) (X : CochainComplex A ℤ) :
    ((Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj X) ≫
      (Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj X)) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app X) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj X) =
      H.mapDerivedCategoryFactors.hom.app X ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).symm).hom.app X) := by
  let k := Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)
  apply (cancel_mono (DerivedCategory.Q.map (k.hom.app X))).mp
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_fac, Functor.mapDerivedCategoryNatIso_fac]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, k,
    ← DerivedCategory.Q.map_comp, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  rfl

end ExactRestrictionComposition

private theorem composition_of_normalized_adjunctions
    {K₁ K₂ K₃ D₁ D₂ D₃ : Type*}
    [Category* K₁] [Category* K₂] [Category* K₃]
    [Category* D₁] [Category* D₂] [Category* D₃]
    {L : K₁ ⥤ K₂} {N : K₂ ⥤ K₃} {H : K₁ ⥤ K₃}
    {U : K₂ ⥤ K₁} {V : K₃ ⥤ K₂} {W : K₃ ⥤ K₁}
    (al : L ⊣ U) (an : N ⊣ V) (ah : H ⊣ W)
    {F : D₁ ⥤ D₂} {G : D₂ ⥤ D₃} {I : D₁ ⥤ D₃}
    {Ur : D₂ ⥤ D₁} {Vr : D₃ ⥤ D₂} {Wr : D₃ ⥤ D₁}
    (af : F ⊣ Ur) (ag : G ⊣ Vr) (ai : I ⊣ Wr)
    (q₁ : K₁ ⥤ D₁) (q₂ : K₂ ⥤ D₂) (q₃ : K₃ ⥤ D₃)
    (el : q₁ ⋙ F ⟶ L ⋙ q₂) (en : q₂ ⋙ G ⟶ N ⋙ q₃)
    (eh : q₁ ⋙ I ⟶ H ⋙ q₃)
    (ru : q₂ ⋙ Ur ≅ U ⋙ q₁) (rv : q₃ ⋙ Vr ≅ V ⋙ q₂)
    (rw : q₃ ⋙ Wr ≅ W ⋙ q₁) (d : Wr ≅ Vr ⋙ Ur) (c : L ⋙ N ≅ H)
    (s : W ≅ V ⋙ U)
    (hl : ∀ (X : K₁) (Y : K₂) (f : L.obj X ⟶ Y),
      af.homEquiv _ _ (el.app X ≫ q₂.map f) =
        q₁.map (al.homEquiv _ _ f) ≫ ru.inv.app Y)
    (hn : ∀ (X : K₂) (Y : K₃) (f : N.obj X ⟶ Y),
      ag.homEquiv _ _ (en.app X ≫ q₃.map f) =
        q₂.map (an.homEquiv _ _ f) ≫ rv.inv.app Y)
    (hh : ∀ X : K₁, ai.homEquiv _ _ (eh.app X) =
      q₁.map (ah.unit.app X) ≫ rw.inv.app (H.obj X))
    (hc : ∀ X : K₁, (al.comp an).homEquiv _ _ (c.hom.app X) =
      ah.unit.app X ≫ s.hom.app (H.obj X))
    (hr : ∀ Y : K₃, d.hom.app (q₃.obj Y) ≫
      Ur.map (rv.hom.app Y) ≫ ru.hom.app (V.obj Y) = rw.hom.app Y ≫ q₁.map (s.hom.app Y))
    (X : K₁) :
    (Adjunction.leftAdjointUniq (af.comp ag) (ai.ofNatIsoRight d)).hom.app (q₁.obj X) ≫
        eh.app X = G.map (el.app X) ≫ en.app (L.obj X) ≫ q₃.map (c.hom.app X) := by
  have hd (Y : D₃) (f : I.obj (q₁.obj X) ⟶ Y) :
      (af.comp ag).homEquiv _ _
        ((Adjunction.leftAdjointUniq (af.comp ag) (ai.ofNatIsoRight d)).hom.app
          (q₁.obj X) ≫ f) = ai.homEquiv _ _ f ≫ d.hom.app Y := by
    rw [(af.comp ag).homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit]
    exact Adjunction.homEquiv_ofNatIsoRight_apply ai d f
  have hri (Y : K₃) : rw.inv.app Y ≫ d.hom.app (q₃.obj Y) =
      q₁.map (s.hom.app Y) ≫ ru.inv.app (V.obj Y) ≫ Ur.map (rv.inv.app Y) := by
    apply (cancel_mono (Ur.map (rv.hom.app Y) ≫ ru.hom.app (V.obj Y))).mp
    simp only [Category.assoc, ← Ur.map_comp_assoc, Iso.inv_hom_id_app]
    rw [hr]
    dsimp only [Functor.comp_obj]
    simp only [Ur.map_id, Category.id_comp,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm
  apply ((af.comp ag).homEquiv _ _).injective
  rw [hd, hh]
  simp only [Category.assoc, Functor.comp_obj]
  rw [hri]
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply, ag.homEquiv_naturality_left, hn]
  rw [← Category.assoc (el.app X), af.homEquiv_naturality_right, hl]
  have hchain : al.homEquiv _ _ (an.homEquiv _ _ (c.hom.app X)) =
      ah.unit.app X ≫ s.hom.app (H.obj X) := by
    have h := hc X
    rw [Adjunction.comp_homEquiv] at h
    change al.homEquiv _ _ (an.homEquiv _ _ (c.hom.app X)) =
      ah.unit.app X ≫ s.hom.app (H.obj X) at h
    exact h
  rw [hchain, q₁.map_comp]
  simp only [Category.assoc]

private theorem composition_of_normalized_tensor_maps
    {K₁ K₂ K₃ D₁ D₂ D₃ : Type*}
    [Category* K₁] [Category* K₂] [Category* K₃]
    [Category* D₁] [Category* D₂] [Category* D₃]
    (q₁ : K₁ ⥤ D₁) (q₂ : K₂ ⥤ D₂) (q₃ : K₃ ⥤ D₃)
    (L : K₁ ⥤ K₂) (N : K₂ ⥤ K₃) (H : K₁ ⥤ K₃)
    (F : D₁ ⥤ D₂) (G : D₂ ⥤ D₃) (I : D₁ ⥤ D₃)
    (t₁ : K₁ × K₁ ⥤ K₁) (t₂ : K₂ × K₂ ⥤ K₂) (t₃ : K₃ × K₃ ⥤ K₃)
    (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂) (T₃ : D₃ × D₃ ⥤ D₃)
    (el : q₁ ⋙ F ⟶ L ⋙ q₂) (en : q₂ ⋙ G ⟶ N ⋙ q₃)
    (eh : q₁ ⋙ I ⟶ H ⋙ q₃) (c : L ⋙ N ≅ H) (d : F ⋙ G ≅ I)
    (bl : ∀ X Y, L.obj (t₁.obj (X, Y)) ⟶ t₂.obj (L.obj X, L.obj Y))
    (bn : ∀ X Y, N.obj (t₂.obj (X, Y)) ⟶ t₃.obj (N.obj X, N.obj Y))
    (bh : ∀ X Y, H.obj (t₁.obj (X, Y)) ⟶ t₃.obj (H.obj X, H.obj Y))
    (mf : T₁ ⋙ F ≅ F.prod F ⋙ T₂) (mg : T₂ ⋙ G ≅ G.prod G ⋙ T₃)
    (mi : T₁ ⋙ I ≅ I.prod I ⋙ T₃)
    (X Y : K₁)
    (r₁ : q₁.obj (t₁.obj (X, Y)) ≅ T₁.obj (q₁.obj X, q₁.obj Y))
    (r₂ : q₂.obj (t₂.obj (L.obj X, L.obj Y)) ≅ T₂.obj (q₂.obj (L.obj X), q₂.obj (L.obj Y)))
    (r₃ : q₃.obj (t₃.obj (N.obj (L.obj X), N.obj (L.obj Y))) ≅
      T₃.obj (q₃.obj (N.obj (L.obj X)), q₃.obj (N.obj (L.obj Y))))
    (r₄ : q₃.obj (t₃.obj (H.obj X, H.obj Y)) ≅ T₃.obj (q₃.obj (H.obj X), q₃.obj (H.obj Y)))
    [IsIso (eh.app X)] [IsIso (eh.app Y)]
    (hf : F.map r₁.hom ≫ mf.hom.app (q₁.obj X, q₁.obj Y) ≫
      T₂.map (Prod.mkHom (el.app X) (el.app Y)) =
      el.app (t₁.obj (X, Y)) ≫ q₂.map (bl X Y) ≫ r₂.hom)
    (hg : G.map r₂.hom ≫ mg.hom.app (q₂.obj (L.obj X), q₂.obj (L.obj Y)) ≫
      T₃.map (Prod.mkHom (en.app (L.obj X)) (en.app (L.obj Y))) =
      en.app (t₂.obj (L.obj X, L.obj Y)) ≫ q₃.map (bn (L.obj X) (L.obj Y)) ≫ r₃.hom)
    (hh : I.map r₁.hom ≫ mi.hom.app (q₁.obj X, q₁.obj Y) ≫
      T₃.map (Prod.mkHom (eh.app X) (eh.app Y)) =
      eh.app (t₁.obj (X, Y)) ≫ q₃.map (bh X Y) ≫ r₄.hom)
    (hc : N.map (bl X Y) ≫ bn (L.obj X) (L.obj Y) ≫
      t₃.map (Prod.mkHom (c.hom.app X) (c.hom.app Y)) =
      c.hom.app (t₁.obj (X, Y)) ≫ bh X Y)
    (he : ∀ Z, d.hom.app (q₁.obj Z) ≫ eh.app Z =
      G.map (el.app Z) ≫ en.app (L.obj Z) ≫ q₃.map (c.hom.app Z))
    (hr : q₃.map (t₃.map (Prod.mkHom (c.hom.app X) (c.hom.app Y))) ≫ r₄.hom =
      r₃.hom ≫ T₃.map (Prod.mkHom (q₃.map (c.hom.app X)) (q₃.map (c.hom.app Y)))) :
    G.map (mf.hom.app (q₁.obj X, q₁.obj Y)) ≫
        mg.hom.app (F.obj (q₁.obj X), F.obj (q₁.obj Y)) ≫
          T₃.map (Prod.mkHom (d.hom.app (q₁.obj X)) (d.hom.app (q₁.obj Y))) =
      d.hom.app (T₁.obj (q₁.obj X, q₁.obj Y)) ≫ mi.hom.app (q₁.obj X, q₁.obj Y) := by
  have : IsIso (Prod.mkHom (eh.app X) (eh.app Y)) :=
    inferInstanceAs (IsIso ((asIso (eh.app X)).prod (asIso (eh.app Y))).hom)
  apply (cancel_epi (G.map (F.map r₁.hom))).mp
  apply (cancel_mono (T₃.map (Prod.mkHom (eh.app X) (eh.app Y)))).mp
  have ht : T₃.map (Prod.mkHom (d.hom.app (q₁.obj X)) (d.hom.app (q₁.obj Y))) ≫
      T₃.map (Prod.mkHom (eh.app X) (eh.app Y)) =
    T₃.map (Prod.mkHom (G.map (el.app X)) (G.map (el.app Y))) ≫
      T₃.map (Prod.mkHom (en.app (L.obj X)) (en.app (L.obj Y))) ≫
        T₃.map (Prod.mkHom (q₃.map (c.hom.app X)) (q₃.map (c.hom.app Y))) := by
    simp only [← T₃.map_comp]
    congr 1
    apply Prod.ext <;> exact he _
  simp only [Category.assoc]
  rw [ht]
  have hm := mg.hom.naturality (Prod.mkHom (el.app X) (el.app Y))
  dsimp only [Functor.comp_map, Functor.prod_map] at hm
  rw [← reassoc_of% hm]
  rw [← G.map_comp_assoc, ← G.map_comp_assoc, Category.assoc, hf, G.map_comp, G.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hg]
  have he' := en.naturality (bl X Y)
  dsimp only [Functor.comp_map] at he'
  rw [reassoc_of% he', ← hr]
  rw [← q₃.map_comp_assoc, ← q₃.map_comp_assoc, Category.assoc, hc, q₃.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% (he (t₁.obj (X, Y)))]
  have hd := d.hom.naturality r₁.hom
  dsimp only [Functor.comp_map] at hd
  rw [reassoc_of% hd, hh]

private theorem identity_of_normalized_adjunctions
    {K D : Type*} [Category* K] [Category* D]
    {L U₀ : K ⥤ K} (al : L ⊣ U₀) {F U : D ⥤ D} (af : F ⊣ U)
    (q : K ⥤ D) (e : q ⋙ F ⟶ L ⋙ q) (r : q ⋙ U ≅ U₀ ⋙ q)
    (d : U ≅ 𝟭 D) (c : L ≅ 𝟭 K) (s : U₀ ≅ 𝟭 K)
    (hn : ∀ X, af.homEquiv _ _ (e.app X) = q.map (al.unit.app X) ≫ r.inv.app (L.obj X))
    (hc : ∀ X, al.unit.app X ≫ U₀.map (c.hom.app X) ≫ s.hom.app X = 𝟙 X)
    (hr : ∀ X, d.hom.app (q.obj X) = r.hom.app X ≫ q.map (s.hom.app X)) (X : K) :
    e.app X ≫ q.map (c.hom.app X) =
      (Adjunction.leftAdjointUniq (af.ofNatIsoRight d) Adjunction.id).hom.app (q.obj X) := by
  apply ((af.ofNatIsoRight d).homEquiv _ _).injective
  dsimp only [Functor.id_obj]
  have hu : (af.ofNatIsoRight d).homEquiv (q.obj X) (q.obj X)
      ((Adjunction.leftAdjointUniq (af.ofNatIsoRight d) Adjunction.id).hom.app
        (q.obj X)) = 𝟙 _ :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app (af.ofNatIsoRight d)
      (Adjunction.id : 𝟭 D ⊣ 𝟭 D) (q.obj X)
  rw [hu]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, af.homEquiv_naturality_right, hn]
  have hnat := r.inv.naturality (c.hom.app X)
  dsimp only [Functor.comp_map, Functor.id_map] at hnat
  simp only [Category.assoc]
  rw [← reassoc_of% hnat, hr X]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← q.map_comp, ← q.map_comp, hc]
  exact q.map_id X

private theorem identity_of_normalized_tensor_maps
    {K D : Type*} [Category* K] [Category* D]
    (q : K ⥤ D) (L : K ⥤ K) (F : D ⥤ D)
    (t : K × K ⥤ K) (T : D × D ⥤ D)
    (e : q ⋙ F ⟶ L ⋙ q) (c : L ≅ 𝟭 K) (d : F ≅ 𝟭 D)
    (b : ∀ X Y, L.obj (t.obj (X, Y)) ⟶ t.obj (L.obj X, L.obj Y))
    (m : T ⋙ F ≅ F.prod F ⋙ T) (X Y : K)
    (r : q.obj (t.obj (X, Y)) ≅ T.obj (q.obj X, q.obj Y))
    (r' : q.obj (t.obj (L.obj X, L.obj Y)) ≅ T.obj (q.obj (L.obj X), q.obj (L.obj Y)))
    (hm : F.map r.hom ≫ m.hom.app (q.obj X, q.obj Y) ≫
        T.map (Prod.mkHom (e.app X) (e.app Y)) =
      e.app (t.obj (X, Y)) ≫ q.map (b X Y) ≫ r'.hom)
    (hc : b X Y ≫ t.map (Prod.mkHom (c.hom.app X) (c.hom.app Y)) =
      c.hom.app (t.obj (X, Y)))
    (he : ∀ Z, e.app Z ≫ q.map (c.hom.app Z) = d.hom.app (q.obj Z))
    (hr : q.map (t.map (Prod.mkHom (c.hom.app X) (c.hom.app Y))) ≫ r.hom =
      r'.hom ≫ T.map (Prod.mkHom (q.map (c.hom.app X)) (q.map (c.hom.app Y)))) :
    m.hom.app (q.obj X, q.obj Y) ≫
      T.map (Prod.mkHom (d.hom.app (q.obj X)) (d.hom.app (q.obj Y))) =
        d.hom.app (T.obj (q.obj X, q.obj Y)) := by
  apply (cancel_epi (F.map r.hom)).mp
  rw [← he X, ← he Y]
  have ht : T.map (Prod.mkHom (e.app X ≫ q.map (c.hom.app X))
      (e.app Y ≫ q.map (c.hom.app Y))) =
    T.map (Prod.mkHom (e.app X) (e.app Y)) ≫
      T.map (Prod.mkHom (q.map (c.hom.app X)) (q.map (c.hom.app Y))) := by
    rw [← T.map_comp]
    congr 1
  rw [ht, reassoc_of% hm]
  rw [← hr, ← q.map_comp_assoc, hc, ← Category.assoc, he]
  exact (d.hom.naturality r.hom).symm

private noncomputable def tensorCompRoute
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (T₁ : A × A ⥤ A) (T₂ : B × B ⥤ B) (T₃ : D × D ⥤ D)
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    (u : T₁ ⋙ F ≅ F.prod F ⋙ T₂) (v : T₂ ⋙ G ≅ G.prod G ⋙ T₃)
    (d : F ⋙ G ≅ H) : T₁ ⋙ (F ⋙ G) ≅ H.prod H ⋙ T₃ :=
  (Functor.associator T₁ F G).symm ≪≫ isoWhiskerRight u G ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft (F.prod F) v ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (NatIso.prod d d) T₃

private theorem tensor_comp_app
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (T₁ : A × A ⥤ A) (T₂ : B × B ⥤ B) (T₃ : D × D ⥤ D)
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    (u : T₁ ⋙ F ≅ F.prod F ⋙ T₂) (v : T₂ ⋙ G ≅ G.prod G ⋙ T₃)
    (d : F ⋙ G ≅ H) (X Y : A) :
    (tensorCompRoute T₁ T₂ T₃ F G H u v d).hom.app (X, Y) =
    G.map (u.hom.app (X, Y)) ≫ v.hom.app (F.obj X, F.obj Y) ≫
      T₃.map (Prod.mkHom (d.hom.app X) (d.hom.app Y)) := by
  dsimp only [tensorCompRoute]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp,
    NatIso.prod, NatTrans.prod, Functor.prod_obj]

attribute [local irreducible] tensorCompRoute

private noncomputable def tensorIdRoute
    {A : Type*} [Category* A] (T : A × A ⥤ A) (F : A ⥤ A)
    (u : T ⋙ F ≅ F.prod F ⋙ T) (d : F ≅ 𝟭 A) : T ⋙ F ≅ T :=
  u ≪≫ isoWhiskerRight (NatIso.prod d d) T ≪≫ Functor.leftUnitor T

private theorem tensor_id_app
    {A : Type*} [Category* A] (T : A × A ⥤ A) (F : A ⥤ A)
    (u : T ⋙ F ≅ F.prod F ⋙ T) (d : F ≅ 𝟭 A) (X Y : A) :
    (tensorIdRoute T F u d).hom.app (X, Y) =
      u.hom.app (X, Y) ≫ T.map (Prod.mkHom (d.hom.app X) (d.hom.app Y)) := by
  dsimp only [tensorIdRoute]
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, NatIso.prod, NatTrans.prod,
    Functor.prod_obj, Functor.id_obj]
  exact congrArg (fun f ↦ u.hom.app (X, Y) ≫ f)
    (Category.comp_id (T.map (Prod.mkHom (d.hom.app X) (d.hom.app Y))))

attribute [local irreducible] tensorIdRoute

private noncomputable def tensorIdRightRoute
    {A : Type*} [Category* A] (T : A × A ⥤ A) (F : A ⥤ A)
    (d : F ≅ 𝟭 A) : T ⋙ F ≅ T :=
  isoWhiskerLeft T d ≪≫ Functor.rightUnitor T

private theorem tensor_id_right_app
    {A : Type*} [Category* A] (T : A × A ⥤ A) (F : A ⥤ A)
    (d : F ≅ 𝟭 A) (X Y : A) :
    (tensorIdRightRoute T F d).hom.app (X, Y) =
      d.hom.app (T.obj (X, Y)) := by
  dsimp only [tensorIdRightRoute]
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  exact Category.comp_id _

attribute [local irreducible] tensorIdRightRoute

private theorem naturality_from_components
    {A B : Type*} [Category* A] [Category* B] {F G : A ⥤ B}
    (e : F ⟶ G) (f : ∀ X, F.obj X ⟶ G.obj X) (h : ∀ X, e.app X = f X)
    {X Y : A} (u : X ⟶ Y) : F.map u ≫ f Y = f X ≫ G.map u := by
  rw [← h X, ← h Y]
  exact e.naturality u

private theorem app_eq_of_iso
    {A B : Type*} [Category* A] [Category* B] {F G : A ⥤ B}
    (α β : F ⟶ G) {X Y : A} (i : X ≅ Y) (h : α.app X = β.app X) :
    α.app Y = β.app Y := by
  apply (cancel_epi (F.map i.hom)).mp
  rw [α.naturality, β.naturality, h]

private theorem tensor_comp_transport
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (T₁ : A × A ⥤ A) (T₂ : B × B ⥤ B) (T₃ : D × D ⥤ D)
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    (u : T₁ ⋙ F ≅ F.prod F ⋙ T₂) (v : T₂ ⋙ G ≅ G.prod G ⋙ T₃)
    (z : T₁ ⋙ H ≅ H.prod H ⋙ T₃) (c : F ⋙ G ≅ H)
    {X' Y' X Y : A} (i : X' ≅ X) (j : Y' ≅ Y)
    (hrep : G.map (u.hom.app (X', Y')) ≫ v.hom.app (F.obj X', F.obj Y') ≫
      T₃.map (Prod.mkHom (c.hom.app X') (c.hom.app Y')) =
        c.hom.app (T₁.obj (X', Y')) ≫ z.hom.app (X', Y')) :
    G.map (u.hom.app (X, Y)) ≫ v.hom.app (F.obj X, F.obj Y) ≫
      T₃.map (Prod.mkHom (c.hom.app X) (c.hom.app Y)) =
        c.hom.app (T₁.obj (X, Y)) ≫ z.hom.app (X, Y) := by
  let l : T₁ ⋙ (F ⋙ G) ≅
      H.prod H ⋙ T₃ :=
    tensorCompRoute T₁ T₂ T₃
      F G H u v c
  let r := isoWhiskerLeft T₁ c ≪≫ z
  have hl (X Y : A) :
      l.hom.app (X, Y) =
        G.map (u.hom.app (X, Y)) ≫
          v.hom.app (F.obj X, F.obj Y) ≫
            T₃.map (Prod.mkHom (c.hom.app X) (c.hom.app Y)) :=
    tensor_comp_app T₁ T₂ T₃
      F G H u v c X Y
  have hr (X Y : A) :
      r.hom.app (X, Y) = c.hom.app (T₁.obj (X, Y)) ≫
        z.hom.app (X, Y) := by
    rfl
  have h₀ : l.hom.app (X', Y') = r.hom.app (X', Y') :=
    (hl _ _).trans (hrep.trans (hr _ _).symm)
  have h := app_eq_of_iso l.hom r.hom (Iso.prod i j) h₀
  exact (hl X Y).symm.trans
    (h.trans (hr X Y))

private theorem tensor_id_transport
    {A : Type*} [Category* A] (T : A × A ⥤ A) (F : A ⥤ A)
    (u : T ⋙ F ≅ F.prod F ⋙ T) (d : F ≅ 𝟭 A)
    {X' Y' X Y : A} (i : X' ≅ X) (j : Y' ≅ Y)
    (hrep : u.hom.app (X', Y') ≫
      T.map (Prod.mkHom (d.hom.app X') (d.hom.app Y')) = d.hom.app (T.obj (X', Y'))) :
    T.map (Prod.mkHom (d.inv.app X) (d.inv.app Y)) =
      d.inv.app (T.obj (X, Y)) ≫ u.hom.app (X, Y) := by
  let l := tensorIdRoute T F u d
  let r := tensorIdRightRoute T F d
  have hl (X Y : A) :
      l.hom.app (X, Y) = u.hom.app (X, Y) ≫
        T.map (Prod.mkHom (d.hom.app X) (d.hom.app Y)) :=
    tensor_id_app T F u d X Y
  have hr (X Y : A) :
      r.hom.app (X, Y) = d.hom.app (T.obj (X, Y)) :=
    tensor_id_right_app T F d X Y
  have h₀ : l.hom.app (X', Y') = r.hom.app (X', Y') :=
    (hl _ _).trans (hrep.trans (hr _ _).symm)
  have h := app_eq_of_iso l.hom r.hom (Iso.prod i j) h₀
  have hh : u.hom.app (X, Y) ≫
      T.map (Prod.mkHom (d.hom.app X) (d.hom.app Y)) = d.hom.app (T.obj (X, Y)) :=
    (hl X Y).symm.trans (h.trans (hr X Y))
  apply (cancel_epi (d.hom.app (T.obj (X, Y)))).mp
  change d.hom.app (T.obj (X, Y)) ≫ T.map (Prod.mkHom (d.inv.app X) (d.inv.app Y)) = _
  have hc : Prod.mkHom (d.hom.app X) (d.hom.app Y) ≫
      Prod.mkHom (d.inv.app X) (d.inv.app Y) = 𝟙 _ := by
    apply Prod.ext <;> exact Iso.hom_inv_id_app d _
  have ht : T.map (Prod.mkHom (d.hom.app X) (d.hom.app Y)) ≫
      T.map (Prod.mkHom (d.inv.app X) (d.inv.app Y)) = 𝟙 _ :=
    ((T.map_comp _ _).symm.trans (congrArg T.map hc)).trans (T.map_id _)
  have hz := congrArg (fun f ↦ f ≫ u.hom.app (X, Y))
    (Iso.hom_inv_id_app d (T.obj (X, Y)))
  calc
    d.hom.app (T.obj (X, Y)) ≫
        T.map (Prod.mkHom (d.inv.app X) (d.inv.app Y)) =
      (u.hom.app (X, Y) ≫ T.map (Prod.mkHom (d.hom.app X) (d.hom.app Y))) ≫
        T.map (Prod.mkHom (d.inv.app X) (d.inv.app Y)) :=
      congrArg (fun f ↦ f ≫ T.map (Prod.mkHom (d.inv.app X) (d.inv.app Y))) hh.symm
    _ = u.hom.app (X, Y) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f ↦ u.hom.app (X, Y) ≫ f) ht).trans (Category.comp_id _))
    _ = d.hom.app (T.obj (X, Y)) ≫
        (d.inv.app (T.obj (X, Y)) ≫ u.hom.app (X, Y)) :=
      (Category.id_comp _).symm.trans (hz.symm.trans (Category.assoc _ _ _))

private theorem unit_square_of_epi
    {K₁ K₂ D₁ D₂ : Type*}
    [Category* K₁] [Category* K₂] [Category* D₁] [Category* D₂]
    {L : K₁ ⥤ K₂} {U : K₂ ⥤ K₁} (al : L ⊣ U)
    {F : D₁ ⥤ D₂} {V : D₂ ⥤ D₁} (af : F ⊣ V)
    (q₁ : K₁ ⥤ D₁) (q₂ : K₂ ⥤ D₂)
    (e : q₁ ⋙ F ⟶ L ⋙ q₂) (r : q₂ ⋙ V ≅ U ⋙ q₁)
    {P' P : K₁} (f : P' ⟶ P) [Epi (q₁.map f)]
    (h : af.unit.app (q₁.obj P') ≫ V.map (e.app P') ≫ r.hom.app (L.obj P') =
      q₁.map (al.unit.app P')) :
    af.unit.app (q₁.obj P) ≫ V.map (e.app P) ≫ r.hom.app (L.obj P) =
      q₁.map (al.unit.app P) := by
  apply (cancel_epi (q₁.map f)).mp
  erw [af.unit.naturality_assoc]
  change af.unit.app (q₁.obj P') ≫ V.map (F.map (q₁.map f)) ≫
    V.map (e.app P) ≫ r.hom.app (L.obj P) = _
  rw [← V.map_comp_assoc]
  erw [e.naturality f]
  rw [V.map_comp, Category.assoc]
  erw [r.hom.naturality (L.map f)]
  rw [← Category.assoc, ← Category.assoc]
  rw [Category.assoc _ _ (r.hom.app (L.obj P')), h]
  dsimp only [Functor.comp_map]
  rw [← q₁.map_comp, ← q₁.map_comp]
  exact congrArg q₁.map (al.unit.naturality f).symm

private theorem unit_square_of_transpose
    {K₁ K₂ D₁ D₂ : Type*}
    [Category* K₁] [Category* K₂] [Category* D₁] [Category* D₂]
    {L : K₁ ⥤ K₂} {U : K₂ ⥤ K₁} (al : L ⊣ U)
    {F : D₁ ⥤ D₂} {V : D₂ ⥤ D₁} (af : F ⊣ V)
    (q₁ : K₁ ⥤ D₁) (q₂ : K₂ ⥤ D₂)
    (e : q₁ ⋙ F ⟶ L ⋙ q₂) (r : q₂ ⋙ V ≅ U ⋙ q₁) (P : K₁)
    (h : (af.homEquiv _ _).symm
      (q₁.map (al.unit.app P) ≫ r.inv.app (L.obj P)) = e.app P) :
    af.unit.app (q₁.obj P) ≫ V.map (e.app P) ≫ r.hom.app (L.obj P) =
      q₁.map (al.unit.app P) := by
  have hu := congrArg (af.homEquiv _ _) h
  rw [Equiv.apply_symm_apply] at hu
  erw [Adjunction.homEquiv_unit] at hu
  dsimp only [Functor.id_obj] at hu
  rw [← Category.assoc, ← hu]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R : Sheaf J CommRingCat.{max c v r}}
attribute [local irreducible] monoidalCategory derivedInternalHomOfUniverses
attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
private theorem tensor_hasMap
    {D : Type c} [Category.{v} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (A : Sheaf K CommRingCat.{u}) (P Q : CochainComplex (scalarModules K A) ℤ) :
    letI := monoidalCategory A
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor (scalarModules K A)) (.up ℤ) := by
  let := monoidalCategory A
  infer_instance

attribute [local instance 2000] tensor_hasMap

private theorem bifunctor_map_factor
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [Preadditive D]
    (F : A ⥤ B ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    [∀ (P : CochainComplex A ℤ) (Q : CochainComplex B ℤ),
      HomologicalComplex.HasMapBifunctor P Q F (.up ℤ)]
    {P P' : CochainComplex A ℤ} {Q Q' : CochainComplex B ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap f (𝟙 Q) F (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') g F (.up ℤ) =
      HomologicalComplex.mapBifunctorMap f g F (.up ℤ) := by
  simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

private theorem generator_eq
    (P Q : CochainComplex (scalarModules J R) ℤ) (p q n : ℤ) (h : p + q = n)
    (V : Cᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y =
      letI := monoidalCategory R
      (CochainComplex.ιMapBifunctor P Q (curriedTensor (scalarModules J R))
        p q n h).val.app V
          (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y) := by
  rfl

attribute [local irreducible] coefficientTensorGenerator

private theorem total_pure_hom_ext
    (P Q : CochainComplex (scalarModules J R) ℤ) (n : ℤ)
    (H : scalarModules J R)
    {f g : ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X n ⟶ H}
    (hh : ∀ (p q : ℤ) (h : p + q = n) (V : Cᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      f.val.app V (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y) =
        g.val.app V (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y)) :
    f = g := by
  let := monoidalCategory R
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  apply SheafOfModules.ScalarHomOrdinary.pure_hom_ext R (P.X p) (Q.X q) H
  intro V x y
  have hx := hh p q h V x y
  rw [generator_eq.{c, v, r}] at hx
  exact hx

variable [∀ A : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J A)]
  (M : ScalarHomModels.{c, v, r, w} J) {S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private noncomputable def ordinaryComp
    {T : Sheaf J CommRingCat.{max c v r}} (b : S ⟶ T) :
    (M.scalar a).extension ⋙ (M.scalar b).extension ≅ (M.scalar (a ≫ b)).extension :=
  Adjunction.leftAdjointUniq
    ((M.scalar a).ordinaryAdjunction.comp (M.scalar b).ordinaryAdjunction)
    ((M.scalar (a ≫ b)).ordinaryAdjunction.ofNatIsoRight
      (scalarHomOrdinaryRestrictionComp.{c, v, r} a b))

private theorem ordinaryComp_unit
    {T : Sheaf J CommRingCat.{max c v r}} (b : S ⟶ T)
    (P : scalarModules J R) (V : Cᵒᵖ) (x : P.val.obj V) :
    ((ordinaryComp M a b).hom.app P).val.app V
      (scalarHomUnitSection M b _ V (scalarHomUnitSection M a P V x)) =
        scalarHomUnitSection M (a ≫ b) P V x := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((M.scalar a).ordinaryAdjunction.comp (M.scalar b).ordinaryAdjunction)
    ((M.scalar (a ≫ b)).ordinaryAdjunction.ofNatIsoRight
      (scalarHomOrdinaryRestrictionComp.{c, v, r} a b)) P
  exact congrArg (fun f ↦ f.val.app V x) h

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ A : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J A)] in
private theorem restrictionComp_section
    {T : Sheaf J CommRingCat.{max c v r}} (b : S ⟶ T)
    (H : scalarModules J T) (V : Cᵒᵖ) (x : H.val.obj V) :
    ((scalarHomOrdinaryRestrictionComp.{c, v, r} a b).hom.app H).val.app V x = x := by
  rfl

attribute [local irreducible] ordinaryComp scalarHomOrdinaryRestrictionComp

private noncomputable def complexCompIso
    {T : Sheaf J CommRingCat.{max c v r}} (b : S ⟶ T) :
    scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
      scalarComplex (M.scalar b).extension (M.scalar b).extension_additive ≅
        scalarComplex (M.scalar (a ≫ b)).extension (M.scalar (a ≫ b)).extension_additive := by
  let := (M.scalar a).extension_additive
  let := (M.scalar b).extension_additive
  let := (M.scalar (a ≫ b)).extension_additive
  exact Functor.mapHomologicalComplexCompIso (ordinaryComp M a b) (.up ℤ)

private noncomputable def complexComp
    {T : Sheaf J CommRingCat.{max c v r}} (b : S ⟶ T)
    (P : CochainComplex (scalarModules J R) ℤ) :
    (scalarComplex (M.scalar b).extension (M.scalar b).extension_additive).obj
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P) ≅
      (scalarComplex (M.scalar (a ≫ b)).extension
        (M.scalar (a ≫ b)).extension_additive).obj P :=
  (complexCompIso M a b).app P

private theorem complexComp_f
    {T : Sheaf J CommRingCat.{max c v r}} (b : S ⟶ T)
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℤ) :
    (complexComp M a b P).hom.f n = (ordinaryComp M a b).hom.app (P.X n) := by
  rfl

private theorem complexCompIso_f
    {T : Sheaf J CommRingCat.{max c v r}} (b : S ⟶ T)
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℤ) :
    ((complexCompIso M a b).hom.app P).f n =
      (ordinaryComp M a b).hom.app (P.X n) := by
  rfl

attribute [local irreducible] complexCompIso

omit [∀ A : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J A)] in
private theorem generator_map
    {A : Sheaf J CommRingCat.{max c v r}}
    {P P' Q Q' : CochainComplex (scalarModules J A) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (p q n : ℤ) (h : p + q = n)
    (V : Cᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    (((coefficientTotalTensor.{r, c, v} J A).map (Prod.mkHom f g)).f n).val.app V
        (coefficientTensorGenerator.{r, c, v} J A P Q p q n h V x y) =
      coefficientTensorGenerator.{r, c, v} J A P' Q' p q n h V
        ((f.f p).val.app V x) ((g.f q).val.app V y) := by
  let := monoidalCategory A
  have hi := HomologicalComplex.ι_mapBifunctorMap f g (curriedTensor (scalarModules J A))
    (.up ℤ) p q n h
  have hh := congrArg (fun k ↦ k.val.app V
    (SheafOfModules.ScalarHomOrdinary.pure A (P.X p) (Q.X q) V x y)) hi
  simp only [curriedTensor_map_app, curriedTensor_obj_map,
    ← tensorHom_def_assoc] at hh
  change (((HomologicalComplex.mapBifunctorMap f g
      (curriedTensor (scalarModules J A)) (.up ℤ)).f n).val.app V)
      ((CochainComplex.ιMapBifunctor P Q (curriedTensor (scalarModules J A))
        p q n h).val.app V (SheafOfModules.ScalarHomOrdinary.pure A _ _ V x y)) =
    (CochainComplex.ιMapBifunctor P' Q' (curriedTensor (scalarModules J A))
        p q n h).val.app V
      (((monoidalCategory A).tensorHom (f.f p) (g.f q)).val.app V
        (SheafOfModules.ScalarHomOrdinary.pure A _ _ V x y)) at hh
  rw [SheafOfModules.ScalarHomOrdinary.pure_map] at hh
  have hm : (coefficientTotalTensor.{r, c, v} J A).map (Prod.mkHom f g) =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor (scalarModules J A)) (.up ℤ) := by
    simpa only [coefficientTotalTensor, Functor.uncurry_obj_map,
      Functor.map₂HomologicalComplex] using
        bifunctor_map_factor (curriedTensor (scalarModules J A)) f g
  rw [hm, generator_eq.{c, v, r}, generator_eq.{c, v, r}]
  exact hh

private theorem unitSection_map {A B : Sheaf J CommRingCat.{max c v r}}
    (b : A ⟶ B) {P Q : scalarModules J A} (f : P ⟶ Q)
    (V : Cᵒᵖ) (x : P.val.obj V) :
    ((M.scalar b).extension.map f).val.app V (scalarHomUnitSection M b P V x) =
      scalarHomUnitSection M b Q V (f.val.app V x) :=
  (congrArg (fun k ↦ k.val.app V x) ((M.scalar b).ordinaryAdjunction.unit.naturality f)).symm

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] coefficientTotalTensor

-- Three scalar functors require conversions between termwise and ordinary extension.
set_option maxHeartbeats 800000 in
-- Termwise adjunctions and total tensor generators require dependent conversions.
private theorem complex_comp
    (μ : ∀ {A B : Sheaf J CommRingCat.{max c v r}} (f : A ⟶ B),
      ScalarHomTensorComparison M f)
    {T : Sheaf J CommRingCat.{max c v r}} (b : S ⟶ T)
    (P Q : CochainComplex (scalarModules J R) ℤ) :
    (scalarComplex (M.scalar b).extension (M.scalar b).extension_additive).map
        ((μ a).complexIso P Q).hom ≫
      ((μ b).complexIso
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P)
        ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q)).hom ≫
      (coefficientTotalTensor.{r, c, v} J T).map
        (Prod.mkHom (complexComp M a b P).hom (complexComp M a b Q).hom) =
      (complexComp M a b _).hom ≫ ((μ (a ≫ b)).complexIso P Q).hom := by
  let := (M.scalar a).extension_additive
  let := (M.scalar b).extension_additive
  apply HomologicalComplex.Hom.ext
  funext n
  apply (((M.scalar a).ordinaryAdjunction.comp
    (M.scalar b).ordinaryAdjunction).homEquiv
      (((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X n) _).injective
  apply total_pure_hom_ext.{c, v, r}
  intro p q h V x y
  change
    (((coefficientTotalTensor.{r, c, v} J T).map
      (Prod.mkHom (complexComp M a b P).hom (complexComp M a b Q).hom)).f n).val.app V
      ((((μ b).complexIso _ _).hom.f n).val.app V
        (((M.scalar b).extension.map (((μ a).complexIso P Q).hom.f n)).val.app V
          (scalarHomUnitSection M b _ V
            (scalarHomUnitSection M a _ V
              (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y))))) =
      (((μ (a ≫ b)).complexIso P Q).hom.f n).val.app V
        ((((complexComp M a b
          ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q))).hom.f n)).val.app V
          (scalarHomUnitSection M b _ V
            (scalarHomUnitSection M a _ V
              (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y))))
  let t := fun z ↦
    (((coefficientTotalTensor.{r, c, v} J T).map
      (Prod.mkHom (complexComp M a b P).hom (complexComp M a b Q).hom)).f n).val.app V z
  let u := (((μ b).complexIso
      ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P)
      ((scalarComplex (M.scalar a).extension
        (M.scalar a).extension_additive).obj Q)).hom.f n).val.app V
  have h₀ := congrArg (fun z ↦ t (u z))
    (unitSection_map M b (((μ a).complexIso P Q).hom.f n) V
      (scalarHomUnitSection M a _ V
        (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y)))
  have h₁ := congrArg (fun z ↦ t (u (scalarHomUnitSection M b _ V z)))
    ((μ a).generators P Q p q n h V x y)
  have h₂ := congrArg t ((μ b).generators
    ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P)
    ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj Q) p q n h V
      (scalarHomUnitSection M a (P.X p) V x)
      (scalarHomUnitSection M a (Q.X q) V y))
  have h₃ := generator_map.{c, v, r}
    (complexComp M a b P).hom (complexComp M a b Q).hom p q n h V
    (scalarHomUnitSection M b _ V (scalarHomUnitSection M a (P.X p) V x))
    (scalarHomUnitSection M b _ V (scalarHomUnitSection M a (Q.X q) V y))
  have hx := congrArg
    (fun f ↦ f.val.app V
      (scalarHomUnitSection M b _ V (scalarHomUnitSection M a (P.X p) V x)))
    (complexComp_f M a b P p)
  have hy := congrArg
    (fun f ↦ f.val.app V
      (scalarHomUnitSection M b _ V (scalarHomUnitSection M a (Q.X q) V y)))
    (complexComp_f M a b Q q)
  have h₄ := congrArg₂
    (fun x y ↦ coefficientTensorGenerator.{r, c, v} J T
      ((scalarComplex (M.scalar (a ≫ b)).extension
        (M.scalar (a ≫ b)).extension_additive).obj P)
      ((scalarComplex (M.scalar (a ≫ b)).extension
        (M.scalar (a ≫ b)).extension_additive).obj Q) p q n h V x y)
    (hx.trans (ordinaryComp_unit M a b (P.X p) V x))
    (hy.trans (ordinaryComp_unit M a b (Q.X q) V y))
  have h₅ := ((μ (a ≫ b)).generators P Q p q n h V x y).symm
  have h₆ := congrArg (fun z ↦ (((μ (a ≫ b)).complexIso P Q).hom.f n).val.app V z)
    (ordinaryComp_unit M a b (((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X n) V
      (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y))
  have h₇ := congrArg
    (fun f ↦ (((μ (a ≫ b)).complexIso P Q).hom.f n).val.app V
      (f.val.app V (scalarHomUnitSection M b _ V
        (scalarHomUnitSection M a _ V
          (coefficientTensorGenerator.{r, c, v} J R P Q p q n h V x y)))))
    (complexComp_f M a b ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) n)
  exact h₀.trans
    (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.symm.trans h₇.symm))))))

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] tensor_hasMap

private noncomputable def epsRaw :
    DerivedCategory.Q ⋙ (M.scalar a).derived ⟶
      scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        DerivedCategory.Q :=
  let s := M.scalar a
  letI := s.extension_additive
  let F := scalarComplex s.extension s.extension_additive
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv s.derived ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ)) s.counit ≫
    Functor.whiskerRight (s.extension.mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft F (DerivedCategory.quotientCompQhIso _).hom

private theorem epsRaw_app (P : CochainComplex (scalarModules J R) ℤ) :
    (epsRaw M a).app P = scalarPairComplexComparison (M.scalar a).extension
      (M.scalar a).extension_additive (M.scalar a).derived (M.scalar a).counit P := by
  change (M.scalar a).derived.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (M.scalar a).counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map (𝟙 _) ≫ (DerivedCategory.quotientCompQhIso _).hom.app _ = _
  erw [DerivedCategory.Qh.map_id, Category.id_comp]
  rfl



private theorem eps_naturality
    {P Q : CochainComplex (scalarModules J R) ℤ} (f : P ⟶ Q) :
    (M.scalar a).derived.map (DerivedCategory.Q.map f) ≫
        scalarPairComplexComparison (M.scalar a).extension
          (M.scalar a).extension_additive (M.scalar a).derived (M.scalar a).counit Q =
      scalarPairComplexComparison (M.scalar a).extension
          (M.scalar a).extension_additive (M.scalar a).derived (M.scalar a).counit P ≫
        DerivedCategory.Q.map
          ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).map f) := by
  exact naturality_from_components (epsRaw M a)
    (fun P ↦ scalarPairComplexComparison (M.scalar a).extension
      (M.scalar a).extension_additive (M.scalar a).derived (M.scalar a).counit P)
    (epsRaw_app M a) f

private noncomputable def eps :
    DerivedCategory.Q ⋙ (M.scalar a).derived ⟶
      scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        DerivedCategory.Q where
  app P := scalarPairComplexComparison (M.scalar a).extension
    (M.scalar a).extension_additive (M.scalar a).derived (M.scalar a).counit P
  naturality _ _ f := eps_naturality M a f

private theorem eps_app (P : CochainComplex (scalarModules J R) ℤ) :
    (eps M a).app P = scalarPairComplexComparison (M.scalar a).extension
      (M.scalar a).extension_additive (M.scalar a).derived (M.scalar a).counit P := by
  rfl

attribute [local irreducible] eps epsRaw scalarPairComplexComparison

private noncomputable def chainAdj :
    scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⊣
      (scalarRestriction a).mapHomologicalComplex (.up ℤ) :=
  letI := (M.scalar a).extension_additive
  (M.scalar a).ordinaryAdjunction.mapHomologicalComplex (.up ℤ)

private theorem chainAdj_unit_f
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℤ) :
    ((chainAdj M a).unit.app P).f n =
      (M.scalar a).ordinaryAdjunction.unit.app (P.X n) := by
  rfl

private noncomputable def chainUnit :
    𝟭 (CochainComplex (scalarModules J R) ℤ) ⟶
      scalarComplex (M.scalar a).extension (M.scalar a).extension_additive ⋙
        (scalarRestriction a).mapHomologicalComplex (.up ℤ) :=
  (chainAdj M a).unit

private theorem unit_normalization_flat
    (P : CochainComplex (scalarModules J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hf : ∀ n, IsFlatOnSite (J := J) (R := R) (P.X n)) :
    (M.scalar a).adjunction.unit.app (DerivedCategory.Q.obj P) ≫
        (scalarDerivedRestriction a).map ((eps M a).app P) ≫
          (scalarRestrictionComparison a).hom.app
            ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P) =
      DerivedCategory.Q.map ((chainUnit M a).app P) := by
  let s := M.scalar a
  let := s.extension_additive
  let adj := chainAdj M a
  have hn := s.normalization P hp hf _ (adj.unit.app P)
  have ht : scalarChainTranspose a s.extension s.extension_additive
      s.ordinaryAdjunction P _ (adj.unit.app P) = 𝟙 _ := by
    change (adj.homEquiv _ _).symm (adj.unit.app P) = 𝟙 _
    exact adj.homEquiv_symm_unit P
  erw [ht, DerivedCategory.Q.map_id, Category.comp_id] at hn
  exact unit_square_of_transpose adj s.adjunction
    (DerivedCategory.Q (C := scalarModules J R))
    (DerivedCategory.Q (C := scalarModules J S)) (eps M a) (scalarRestrictionComparison a) P
    (hn.trans (eps_app M a P).symm)

private theorem unit_normalization
    (P : CochainComplex (scalarModules J R) ℤ) :
    (M.scalar a).adjunction.unit.app (DerivedCategory.Q.obj P) ≫
        (scalarDerivedRestriction a).map ((eps M a).app P) ≫
          (scalarRestrictionComparison a).hom.app
            ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P) =
      DerivedCategory.Q.map ((chainUnit M a).app P) := by
  let s := M.scalar a
  obtain ⟨P', f, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  have hflat : ∀ n, IsFlatOnSite (J := J) (R := R) (P'.X n) := fun n ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P'.X n)).symm (hf n)
  have hn := unit_normalization_flat M a P' hp hflat
  have : QuasiIso f := hq
  have : IsIso (DerivedCategory.Q.map f) := inferInstance
  exact unit_square_of_epi (chainAdj M a) s.adjunction
    (DerivedCategory.Q (C := scalarModules J R))
    (DerivedCategory.Q (C := scalarModules J S))
    (eps M a) (scalarRestrictionComparison a) f hn

private noncomputable def chainRestrictionComp
    {T : Sheaf J CommRingCat.{max c v r}} (b : S ⟶ T) :
    (scalarRestriction (a ≫ b)).mapHomologicalComplex (.up ℤ) ≅
      (scalarRestriction b).mapHomologicalComplex (.up ℤ) ⋙
        (scalarRestriction a).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (scalarHomOrdinaryRestrictionComp.{c, v, r} a b) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (scalarRestriction b ⋙ scalarRestriction a)) (.up ℤ)).symm

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ A : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J A)] in
private theorem chainRestrictionComp_f
    {T : Sheaf J CommRingCat.{max c v r}} (b : S ⟶ T)
    (H : CochainComplex (scalarModules J T) ℤ) (n : ℤ) :
    ((chainRestrictionComp.{c, v, r} a b).hom.app H).f n =
      (scalarHomOrdinaryRestrictionComp.{c, v, r} a b).hom.app (H.X n) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

private theorem homEquiv_eps (P : CochainComplex (scalarModules J R) ℤ) :
    (M.scalar a).adjunction.homEquiv _ _ ((eps M a).app P) =
      DerivedCategory.Q.map ((chainUnit M a).app P) ≫
        (scalarRestrictionComparison a).inv.app
          ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P) := by
  rw [Adjunction.homEquiv_unit]
  apply (cancel_mono ((scalarRestrictionComparison a).hom.app _)).mp
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  exact unit_normalization M a P

private theorem homEquiv_eps_map
    (P : CochainComplex (scalarModules J R) ℤ)
    (H : CochainComplex (scalarModules J S) ℤ)
    (f : (scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P ⟶ H) :
    (M.scalar a).adjunction.homEquiv _ _ ((eps M a).app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
          (((chainAdj M a).homEquiv P H) f) ≫
        (scalarRestrictionComparison a).inv.app H := by
  let := (M.scalar a).extension_additive
  rw [(M.scalar a).adjunction.homEquiv_naturality_right, homEquiv_eps]
  erw [Category.assoc, ← (scalarRestrictionComparison a).inv.naturality f]
  dsimp only [Functor.comp_map]
  rw [← Category.assoc, ← DerivedCategory.Q.map_comp]
  rfl

attribute [local irreducible] chainAdj

-- The diagram lemma retains the canonical restriction comparison explicitly.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem eps_comp
    {T : Sheaf J CommRingCat.{max c v r}} (b : S ⟶ T)
    (P : CochainComplex (scalarModules J R) ℤ) :
    (scalarHomExtensionComp M a b).hom.app (DerivedCategory.Q.obj P) ≫
        (eps M (a ≫ b)).app P =
      (M.scalar b).derived.map ((eps M a).app P) ≫
        (eps M b).app
          ((scalarComplex (M.scalar a).extension (M.scalar a).extension_additive).obj P) ≫
          DerivedCategory.Q.map (complexComp M a b P).hom := by
  apply composition_of_normalized_adjunctions.{max c v r, max c v r + 1,
    max c v r, max c v r + 1, max c v r, max c v r + 1,
    w, max c v r + 1, w, max c v r + 1, w, max c v r + 1} (chainAdj M a) (chainAdj M b)
    (chainAdj M (a ≫ b)) (M.scalar a).adjunction (M.scalar b).adjunction
    (M.scalar (a ≫ b)).adjunction
    (DerivedCategory.Q (C := scalarModules J R))
    (DerivedCategory.Q (C := scalarModules J S))
    (DerivedCategory.Q (C := scalarModules J T))
    (eps M a) (eps M b) (eps M (a ≫ b)) (scalarRestrictionComparison a)
    (scalarRestrictionComparison b) (scalarRestrictionComparison (a ≫ b))
    (scalarHomRestrictionComp.{c, v, r, w} a b) (complexCompIso M a b)
    (chainRestrictionComp.{c, v, r} a b) (homEquiv_eps_map M a) (homEquiv_eps_map M b)
    (homEquiv_eps M (a ≫ b)) ?_
    (exact_comp_fac (scalarRestriction b) (scalarRestriction a) (scalarRestriction (a ≫ b))
      (scalarHomOrdinaryRestrictionComp.{c, v, r} a b)) P
  intro X
  rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
  simp only [Functor.comp_map, Category.assoc]
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  simp only [chainAdj_unit_f, chainRestrictionComp_f]
  rw [complexCompIso_f]
  ext V x
  change ((ordinaryComp M a b).hom.app (X.X n)).val.app V
      (scalarHomUnitSection M b _ V (scalarHomUnitSection M a (X.X n) V x)) =
    ((scalarHomOrdinaryRestrictionComp.{c, v, r} a b).hom.app
      ((M.scalar (a ≫ b)).extension.obj (X.X n))).val.app V
        (scalarHomUnitSection M (a ≫ b) (X.X n) V x)
  rw [restrictionComp_section.{c, v, r}]
  exact ordinaryComp_unit M a b (X.X n) V x

attribute [local irreducible] scalarHomExtensionComp

private noncomputable def modelIso {A : Sheaf J CommRingCat.{max c v r}}
    (P Q : CochainComplex (scalarModules J A) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q) :=
  CoefficientTensorModels.iso.{r, c, v, w} J A (M.closed A) (M.model A) P Q hp hq

private theorem model_natural
    {A : Sheaf J CommRingCat.{max c v r}}
    {P P' Q Q' : CochainComplex (scalarModules J A) ℤ}
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (hp' : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P')
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q)
    (hq' : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    DerivedCategory.Q.map ((coefficientTotalTensor.{r, c, v} J A).map (Prod.mkHom f g)) ≫
        (modelIso M P' Q' hp' hq').hom =
      (modelIso M P Q hp hq).hom ≫
        (M.closed A).tensor.map
          (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) := by
  let K : ObjectProperty (CochainComplex (scalarModules J A) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A)
  let f' : (⟨P, hp⟩ : K.FullSubcategory) ⟶ ⟨P', hp'⟩ := ObjectProperty.homMk f
  let g' : (⟨Q, hq⟩ : K.FullSubcategory) ⟶ ⟨Q', hq'⟩ := ObjectProperty.homMk g
  exact (M.model A).comparison.hom.naturality (Prod.mkHom f' g')

private noncomputable def ordinaryId (A : Sheaf J CommRingCat.{max c v r}) :
    (M.scalar (𝟙 A)).extension ≅ 𝟭 (scalarModules J A) :=
  Adjunction.leftAdjointUniq
    ((M.scalar (𝟙 A)).ordinaryAdjunction.ofNatIsoRight
      (scalarHomOrdinaryRestrictionId.{c, v, r} A)) Adjunction.id

private theorem ordinaryId_unit (A : Sheaf J CommRingCat.{max c v r})
    (P : scalarModules J A) (V : Cᵒᵖ) (x : P.val.obj V) :
    ((ordinaryId M A).hom.app P).val.app V (scalarHomUnitSection M (𝟙 A) P V x) = x := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((M.scalar (𝟙 A)).ordinaryAdjunction.ofNatIsoRight
      (scalarHomOrdinaryRestrictionId.{c, v, r} A)) Adjunction.id P
  exact congrArg (fun f ↦ f.val.app V x) h

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ A : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J A)] in
private theorem restrictionId_section (A : Sheaf J CommRingCat.{max c v r})
    (H : scalarModules J A) (V : Cᵒᵖ) (x : H.val.obj V) :
    ((scalarHomOrdinaryRestrictionId.{c, v, r} A).hom.app H).val.app V x = x := by
  rfl

attribute [local irreducible] ordinaryId scalarHomOrdinaryRestrictionId

private noncomputable def complexId (A : Sheaf J CommRingCat.{max c v r}) :
    scalarComplex (M.scalar (𝟙 A)).extension (M.scalar (𝟙 A)).extension_additive ≅
      𝟭 (CochainComplex (scalarModules J A) ℤ) := by
  let := (M.scalar (𝟙 A)).extension_additive
  exact NatIso.mapHomologicalComplex (ordinaryId M A) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)

private theorem complexId_f (A : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (scalarModules J A) ℤ) (n : ℤ) :
    ((complexId M A).hom.app P).f n = (ordinaryId M A).hom.app (P.X n) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

attribute [local irreducible] complexId

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem complex_id
    (A : Sheaf J CommRingCat.{max c v r}) (μ : ScalarHomTensorComparison M (𝟙 A))
    (P Q : CochainComplex (scalarModules J A) ℤ) :
    (μ.complexIso P Q).hom ≫ (coefficientTotalTensor.{r, c, v} J A).map
        (Prod.mkHom ((complexId M A).hom.app P) ((complexId M A).hom.app Q)) =
      (complexId M A).hom.app ((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)) := by
  let := (M.scalar (𝟙 A)).extension_additive
  apply HomologicalComplex.Hom.ext
  funext n
  apply ((M.scalar (𝟙 A)).ordinaryAdjunction.homEquiv _ _).injective
  apply total_pure_hom_ext.{c, v, r}
  intro p q h V x y
  change
    (((coefficientTotalTensor.{r, c, v} J A).map
      (Prod.mkHom ((complexId M A).hom.app P) ((complexId M A).hom.app Q))).f n).val.app V
      (((μ.complexIso P Q).hom.f n).val.app V
        (scalarHomUnitSection M (𝟙 A) _ V
          (coefficientTensorGenerator.{r, c, v} J A P Q p q n h V x y))) =
    (((complexId M A).hom.app
      ((coefficientTotalTensor.{r, c, v} J A).obj (P, Q))).f n).val.app V
      (scalarHomUnitSection M (𝟙 A) _ V
        (coefficientTensorGenerator.{r, c, v} J A P Q p q n h V x y))
  have h₀ := congrArg
    (fun z ↦ (((coefficientTotalTensor.{r, c, v} J A).map
      (Prod.mkHom ((complexId M A).hom.app P) ((complexId M A).hom.app Q))).f n).val.app V z)
    (μ.generators P Q p q n h V x y)
  have h₁ := generator_map.{c, v, r}
    ((complexId M A).hom.app P) ((complexId M A).hom.app Q) p q n h V
    (scalarHomUnitSection M (𝟙 A) (P.X p) V x)
    (scalarHomUnitSection M (𝟙 A) (Q.X q) V y)
  have hx := congrArg (fun f ↦ f.val.app V
    (scalarHomUnitSection M (𝟙 A) (P.X p) V x)) (complexId_f M A P p)
  have hy := congrArg (fun f ↦ f.val.app V
    (scalarHomUnitSection M (𝟙 A) (Q.X q) V y)) (complexId_f M A Q q)
  have h₂ := congrArg₂
    (coefficientTensorGenerator.{r, c, v} J A P Q p q n h V)
    (hx.trans (ordinaryId_unit M A (P.X p) V x))
    (hy.trans (ordinaryId_unit M A (Q.X q) V y))
  have hz := congrArg (fun f ↦ f.val.app V
    (scalarHomUnitSection M (𝟙 A) _ V
      (coefficientTensorGenerator.{r, c, v} J A P Q p q n h V x y)))
    (complexId_f M A ((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)) n)
  exact h₀.trans
    (h₁.trans (h₂.trans ((ordinaryId_unit M A _ V _).symm.trans hz.symm)))

private theorem derivedId_hom_Q {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 A).mapDerivedCategoryFactors.hom.app K := by
  have hf := congr_app (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh A))
    ((HomotopyCategory.quotient A (.up ℤ)).obj K)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.mapDerivedCategoryFactorsh_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app] at hf
  have h₁ : ((𝟭 A).mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  have h₂ : (Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app K = 𝟙 _ := rfl
  rw [h₁, h₂] at hf
  erw [Functor.map_id, Functor.map_id, Category.comp_id, Category.comp_id] at hf
  have he : (DerivedCategory.quotientCompQhIso A).inv.app
      (((𝟭 A).mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  rw [he] at hf
  erw [Category.id_comp, Category.comp_id, Category.comp_id] at hf
  exact hf

private noncomputable def chainRestrictionId (A : Sheaf J CommRingCat.{max c v r}) :
    (scalarRestriction (𝟙 A)).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex (scalarModules J A) ℤ) :=
  NatIso.mapHomologicalComplex (scalarHomOrdinaryRestrictionId.{c, v, r} A) (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ A : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J A)] in
private theorem chainRestrictionId_f (A : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (scalarModules J A) ℤ) (n : ℤ) :
    ((chainRestrictionId.{c, v, r} A).hom.app P).f n =
      (scalarHomOrdinaryRestrictionId.{c, v, r} A).hom.app (P.X n) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

private theorem exact_id_fac
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (U : A ⥤ A) [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (e : U ≅ 𝟭 A) (P : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso A).hom.app
        (DerivedCategory.Q.obj P) =
      U.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app P) := by
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  rw [derivedId_hom_Q]
  have h := Functor.mapDerivedCategoryNatIso_fac e P
  have hid : (Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app P = 𝟙 P := rfl
  erw [hid, Category.comp_id]
  exact h

private theorem eps_id (A : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (scalarModules J A) ℤ) :
    (eps M (𝟙 A)).app P ≫ DerivedCategory.Q.map ((complexId M A).hom.app P) =
      (scalarHomExtensionId M A).hom.app (DerivedCategory.Q.obj P) := by
  apply identity_of_normalized_adjunctions.{max c v r, max c v r + 1, w, max c v r + 1}
    (chainAdj M (𝟙 A))
    (M.scalar (𝟙 A)).adjunction (DerivedCategory.Q (C := scalarModules J A)) (eps M (𝟙 A))
    (scalarRestrictionComparison (𝟙 A)) (scalarHomRestrictionId.{c, v, r, w} A)
    (complexId M A) (chainRestrictionId.{c, v, r} A) (homEquiv_eps M (𝟙 A)) ?_
    (exact_id_fac (scalarRestriction (𝟙 A)) (scalarHomOrdinaryRestrictionId A)) P
  intro X
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    chainAdj_unit_f, chainRestrictionId_f]
  rw [complexId_f]
  ext V x
  change ((scalarHomOrdinaryRestrictionId.{c, v, r} A).hom.app (X.X n)).val.app V
    (((ordinaryId M A).hom.app (X.X n)).val.app V
      (scalarHomUnitSection M (𝟙 A) (X.X n) V x)) = x
  rw [restrictionId_section.{c, v, r}]
  exact ordinaryId_unit M A (X.X n) V x

attribute [local irreducible] scalarHomExtensionId

private theorem normalization {A B : Sheaf J CommRingCat.{max c v r}} (f : A ⟶ B)
    (μ : ScalarHomTensorComparison M f) (P Q : CochainComplex (scalarModules J A) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q) :
    (M.scalar f).derived.map (modelIso M P Q hp hq).hom ≫
      μ.iso.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (M.closed B).tensor.map (Prod.mkHom ((eps M f).app P) ((eps M f).app Q)) =
    (eps M f).app ((coefficientTotalTensor.{r, c, v} J A).obj (P, Q)) ≫
      DerivedCategory.Q.map (μ.complexIso P Q).hom ≫
      (modelIso M _ _ (μ.preservesKFlat P hp) (μ.preservesKFlat Q hq)).hom := by
  rw [eps_app M f P, eps_app M f Q, eps_app M f _]
  dsimp only [modelIso]
  exact μ.normalization P Q hp hq

attribute [local irreducible] modelIso

private theorem comp_representatives
    (μ : ∀ {A B : Sheaf J CommRingCat.{max c v r}} (f : A ⟶ B),
      ScalarHomTensorComparison M f)
    {T : Sheaf J CommRingCat.{max c v r}} (b : S ⟶ T)
    (P Q : CochainComplex (scalarModules J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q) :
    (M.scalar b).derived.map ((μ a).iso.hom.app (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj Q)) ≫
      (μ b).iso.hom.app ((M.scalar a).derived.obj (DerivedCategory.Q.obj P),
        (M.scalar a).derived.obj (DerivedCategory.Q.obj Q)) ≫
      (M.closed T).tensor.map (Prod.mkHom
        ((scalarHomExtensionComp M a b).hom.app (DerivedCategory.Q.obj P))
        ((scalarHomExtensionComp M a b).hom.app (DerivedCategory.Q.obj Q))) =
    (scalarHomExtensionComp M a b).hom.app
      ((M.closed R).tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (μ (a ≫ b)).iso.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
  let L := scalarComplex (M.scalar a).extension (M.scalar a).extension_additive
  let N := scalarComplex (M.scalar b).extension (M.scalar b).extension_additive
  let H := scalarComplex (M.scalar (a ≫ b)).extension
    (M.scalar (a ≫ b)).extension_additive
  have hlp := (μ a).preservesKFlat P hp
  have hlq := (μ a).preservesKFlat Q hq
  have hnp := (μ b).preservesKFlat (L.obj P) hlp
  have hnq := (μ b).preservesKFlat (L.obj Q) hlq
  have hhp := (μ (a ≫ b)).preservesKFlat P hp
  have hhq := (μ (a ≫ b)).preservesKFlat Q hq
  have : IsIso ((eps M (a ≫ b)).app P) := by
    rw [eps_app]
    exact (M.scalar (a ≫ b)).computes P hp
  have : IsIso ((eps M (a ≫ b)).app Q) := by
    rw [eps_app]
    exact (M.scalar (a ≫ b)).computes Q hq
  exact composition_of_normalized_tensor_maps.{max c v r, max c v r + 1,
    max c v r, max c v r + 1, max c v r, max c v r + 1,
    w, max c v r + 1, w, max c v r + 1, w, max c v r + 1}
    (DerivedCategory.Q (C := scalarModules J R))
    (DerivedCategory.Q (C := scalarModules J S))
    (DerivedCategory.Q (C := scalarModules J T)) L N H
    (M.scalar a).derived (M.scalar b).derived (M.scalar (a ≫ b)).derived
    (coefficientTotalTensor.{r, c, v} J R) (coefficientTotalTensor.{r, c, v} J S)
    (coefficientTotalTensor.{r, c, v} J T) (M.closed R).tensor (M.closed S).tensor
    (M.closed T).tensor (eps M a) (eps M b) (eps M (a ≫ b))
    (complexCompIso M a b) (scalarHomExtensionComp M a b)
    (fun X Y ↦ ((μ a).complexIso X Y).hom)
    (fun X Y ↦ ((μ b).complexIso X Y).hom)
    (fun X Y ↦ ((μ (a ≫ b)).complexIso X Y).hom)
    (μ a).iso (μ b).iso (μ (a ≫ b)).iso P Q
    (modelIso M P Q hp hq) (modelIso M _ _ hlp hlq)
    (modelIso M _ _ hnp hnq) (modelIso M _ _ hhp hhq)
    (normalization M a (μ a) P Q hp hq)
    (normalization M b (μ b) _ _ hlp hlq)
    (normalization M (a ≫ b) (μ (a ≫ b)) P Q hp hq)
    (complex_comp M a μ b P Q) (eps_comp M a b)
    (model_natural M hnp hhp hnq hhq (complexComp M a b P).hom
      (complexComp M a b Q).hom)

private theorem id_representatives
    (A : Sheaf J CommRingCat.{max c v r}) (μ : ScalarHomTensorComparison M (𝟙 A))
    (P Q : CochainComplex (scalarModules J A) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q) :
    μ.iso.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (M.closed A).tensor.map (Prod.mkHom
        ((scalarHomExtensionId M A).hom.app (DerivedCategory.Q.obj P))
        ((scalarHomExtensionId M A).hom.app (DerivedCategory.Q.obj Q))) =
    (scalarHomExtensionId M A).hom.app
      ((M.closed A).tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  exact identity_of_normalized_tensor_maps.{max c v r, max c v r + 1, w, max c v r + 1}
    (DerivedCategory.Q (C := scalarModules J A))
    (scalarComplex (M.scalar (𝟙 A)).extension (M.scalar (𝟙 A)).extension_additive)
    (M.scalar (𝟙 A)).derived (coefficientTotalTensor.{r, c, v} J A) (M.closed A).tensor
    (eps M (𝟙 A)) (complexId M A) (scalarHomExtensionId M A)
    (fun X Y ↦ (μ.complexIso X Y).hom) μ.iso P Q
    (modelIso M P Q hp hq)
    (modelIso M _ _ (μ.preservesKFlat P hp) (μ.preservesKFlat Q hq))
    (normalization M (𝟙 A) μ P Q hp hq) (complex_id M A μ P Q) (eps_id M A)
    (model_natural M (μ.preservesKFlat P hp) hp (μ.preservesKFlat Q hq) hq
      ((complexId M A).hom.app P) ((complexId M A).hom.app Q))

private theorem exists_kflat_rep (X : DerivedCategory (scalarModules J R)) :
    ∃ (P : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ X) := by
  let q : CochainComplex (scalarModules J R) ℤ ⥤ DerivedCategory (scalarModules J R) :=
    DerivedCategory.Q
  obtain ⟨P, f, hp, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (q.objPreimage X)
  have : QuasiIso f := hq
  have : IsIso (q.map f) := inferInstance
  exact ⟨P, hp, ⟨asIso (q.map f) ≪≫ q.objObjPreimageIso X⟩⟩

private theorem comp_all
    (μ : ∀ {A B : Sheaf J CommRingCat.{max c v r}} (f : A ⟶ B),
      ScalarHomTensorComparison M f)
    {T : Sheaf J CommRingCat.{max c v r}} (b : S ⟶ T)
    (X Y : DerivedCategory (scalarModules J R)) :
    (M.scalar b).derived.map ((μ a).iso.hom.app (X, Y)) ≫
      (μ b).iso.hom.app ((M.scalar a).derived.obj X, (M.scalar a).derived.obj Y) ≫
      (M.closed T).tensor.map (Prod.mkHom ((scalarHomExtensionComp M a b).hom.app X)
        ((scalarHomExtensionComp M a b).hom.app Y)) =
    (scalarHomExtensionComp M a b).hom.app ((M.closed R).tensor.obj (X, Y)) ≫
      (μ (a ≫ b)).iso.hom.app (X, Y)  := by
  obtain ⟨P, hp, ⟨i⟩⟩ := exists_kflat_rep.{c, v, r, w} (J := J) (R := R) X
  obtain ⟨Q, hq, ⟨j⟩⟩ := exists_kflat_rep.{c, v, r, w} (J := J) (R := R) Y
  exact tensor_comp_transport (M.closed R).tensor (M.closed S).tensor (M.closed T).tensor
    (M.scalar a).derived (M.scalar b).derived (M.scalar (a ≫ b)).derived
    (μ a).iso (μ b).iso (μ (a ≫ b)).iso (scalarHomExtensionComp M a b) i j
    (comp_representatives M a μ b P Q hp hq)

private theorem id_all
    (A : Sheaf J CommRingCat.{max c v r}) (μ : ScalarHomTensorComparison M (𝟙 A))
    (X Y : DerivedCategory (scalarModules J A)) :
    (M.closed A).tensor.map (Prod.mkHom
        ((scalarHomExtensionId M A).inv.app X) ((scalarHomExtensionId M A).inv.app Y)) =
      (scalarHomExtensionId M A).inv.app ((M.closed A).tensor.obj (X, Y)) ≫
        μ.iso.hom.app (X, Y)  := by
  obtain ⟨P, hp, ⟨i⟩⟩ := exists_kflat_rep.{c, v, r, w} (J := J) (R := A) X
  obtain ⟨Q, hq, ⟨j⟩⟩ := exists_kflat_rep.{c, v, r, w} (J := J) (R := A) Y
  exact tensor_id_transport (M.closed A).tensor (M.scalar (𝟙 A)).derived μ.iso
    (scalarHomExtensionId M A) i j (id_representatives M A μ P Q hp hq)

end CategoryTheory.ScalarHomTensor

namespace CategoryTheory
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]
  (M : ScalarHomModels.{c, v, r, w} J) {R S : Sheaf J CommRingCat.{max c v r}}

/-- The normalized derived scalar tensor comparisons respect the unit-normalized
left-adjoint composition and identity comparisons.
Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0D6D.
(blueprint: lem-sfb-scalar-hom-tensor-coherence).

Proof: the proved total_pure_hom_ext and complexIso_unique helpers show that
chain maps and the specified chain comparisons are determined by their pure generators.
The proved tensorIso_unique helper then cancels the representative comparison
isomorphisms and uses fully faithful K-flat restriction to prove derived uniqueness.
Proof irrelevance then gives comparison_unique for the entire normalized comparison.
Identify the unit-normalized extension comparison on a K-flat representative
with t tensor (s tensor x) mapped to t b(s) tensor x. The inverse inserts 1. Choose the
representatives with flat terms. Ordinary tensor
cancellation and exact conservative restriction preserve flat terms under scalar
extension, and the given comparison preserves K-flatness. Thus every intermediate
representative computes its derived scalar pair. The
unit identity identifies this with leftAdjointUniq. Evaluate the two tensor routes
on each total pure generator: each sends t tensor (s tensor (x tensor y)) to
(t b(s) tensor x) tensor (1 tensor y). The specified generator equations for the
three chain tensor comparisons give this equality. Equivalently the existing
cochainPullbackTensorCoherence supplies this chain square for identity geometric
inverse images, after identifying its normalized maps by complexIso_unique.
Tensor balancing, sheafification and coproduct generation extend it to the total
complexes. The normalization squares
and fully faithful restriction to K-flat representatives descend it to the stated
derived equation. For the identity map, scalar multiplication identifies extension
with the identity; the same generator argument gives the identity equation.
No coefficient map is assumed flat; scalar extension preserves K-flat complexes. -/
theorem scalarHomTensorCoherence
    (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
      ScalarHomTensorComparison M a) :
    (∀ {R S T : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (b : S ⟶ T)
      (X Y : DerivedCategory (scalarModules J R)),
      (M.scalar b).derived.map ((μ a).iso.hom.app (X, Y)) ≫
          (μ b).iso.hom.app ((M.scalar a).derived.obj X, (M.scalar a).derived.obj Y) ≫
            (M.closed T).tensor.map (Prod.mkHom
              ((scalarHomExtensionComp M a b).hom.app X)
              ((scalarHomExtensionComp M a b).hom.app Y)) =
        (scalarHomExtensionComp M a b).hom.app ((M.closed R).tensor.obj (X, Y)) ≫
          (μ (a ≫ b)).iso.hom.app (X, Y)) ∧
    (∀ (R : Sheaf J CommRingCat.{max c v r})
      (X Y : DerivedCategory (scalarModules J R)),
      (M.closed R).tensor.map (Prod.mkHom
          ((scalarHomExtensionId M R).inv.app X) ((scalarHomExtensionId M R).inv.app Y)) =
        (scalarHomExtensionId M R).inv.app ((M.closed R).tensor.obj (X, Y)) ≫
          (μ (𝟙 R)).iso.hom.app (X, Y)) := by
  constructor
  · intro R S T a b X Y
    exact ScalarHomTensor.comp_all M a μ b X Y
  · intro R X Y
    exact ScalarHomTensor.id_all M R (μ (𝟙 R)) X Y

end CategoryTheory
