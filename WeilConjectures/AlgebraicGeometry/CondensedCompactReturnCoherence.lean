/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusOperatorsBase
import WeilConjectures.AlgebraicGeometry.CompactReturnComposition
import WeilConjectures.AlgebraicGeometry.CondensedPointTrivializationComposition
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionSuccessive
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste

/-! Coherence of the specified compact-return comparisons. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

private theorem exactTrivialization_comp
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F G H : C ⥤ C) [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (c : H ≅ F ⋙ G) (a : F ≅ 𝟭 C) (b : G ≅ 𝟭 C)
    (d : H ≅ 𝟭 C)
    (hd : c ≪≫ Functor.isoWhiskerRight a G ≪≫ Functor.leftUnitor G ≪≫ b = d)
    (K : DerivedCategory C) :
    (Functor.mapDerivedCategoryNatIso c).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso F G).hom.app K ≫
        G.mapDerivedCategory.map ((Functor.mapDerivedCategoryNatIso a).hom.app K ≫
          (Functor.mapDerivedCategoryIdIso C).hom.app K) ≫
        (Functor.mapDerivedCategoryNatIso b).hom.app K ≫
        (Functor.mapDerivedCategoryIdIso C).hom.app K =
      (Functor.mapDerivedCategoryNatIso d).hom.app K ≫
        (Functor.mapDerivedCategoryIdIso C).hom.app K := by
  have hn := NatTrans.congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight a G) K
  have hu := NatTrans.congr_app (Functor.mapDerivedCategoryCompIso_id_comp G) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hn hu
  have ht := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom.app K) hd
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at ht
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  rw [reassoc_of% hu]
  have hi : (Functor.mapDerivedCategoryNatIso (Functor.leftUnitor G)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  rw [hi] at ht
  simp only [NatTrans.id_app] at ht
  erw [Category.id_comp] at ht
  erw [Category.id_comp]
  simpa only [Category.assoc] using
    congrArg (· ≫ (Functor.mapDerivedCategoryIdIso C).hom.app K) ht

private theorem derived_eqToIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (h : F = G) :
    (Functor.mapDerivedCategoryNatIso (eqToIso h)).hom =
      eqToHom (by cases h; rfl) := by
  subst h
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem exchange_slide
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (P : C ⥤ C) (Q : D ⥤ D) (e : F ⋙ Q ⟶ P ⋙ F)
    {A B T U : C} {V : D} (c : T ≅ P.obj A)
    (b : A ⟶ B) (d : P.obj B ⟶ U) (a : V ⟶ Q.obj (F.obj A)) :
    (a ≫ e.app A ≫ F.map c.inv) ≫ F.map (c.hom ≫ P.map b ≫ d) =
      a ≫ Q.map (F.map b) ≫ e.app B ≫ F.map d := by
  have hn := e.naturality b
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc, c.inv_hom_id, F.map_id, Category.id_comp]
  rw [← reassoc_of% hn]

private theorem cancel_inverse_image
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    {A B : C} {V : D} (c : A ≅ B) (a : V ⟶ T.obj A) (b : V ⟶ T.obj B)
    (h : a = b ≫ T.map c.inv) : b = a ≫ T.map c.hom := by
  rw [h, Category.assoc, ← T.map_comp, c.inv_hom_id, T.map_id, Category.comp_id]

private def joinedExchange
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : C ⥤ D) (R : D ⥤ E) (A : C ⥤ C) (B : D ⥤ D) (Q : E ⥤ E)
    (e : R ⋙ Q ⟶ B ⋙ R) (b : J ⋙ B ⟶ A ⋙ J) :
    (J ⋙ R) ⋙ Q ⟶ A ⋙ (J ⋙ R) :=
  (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft J e ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight b R ≫
    (Functor.associator _ _ _).hom

private theorem joinedExchange_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : C ⥤ D) (R : D ⥤ E)
    (A₁ A₂ A₁₂ : C ⥤ C) (B₁ B₂ B₁₂ : D ⥤ D) (Q₁ Q₂ Q₁₂ : E ⥤ E)
    (cA : A₁₂ ≅ A₁ ⋙ A₂) (cB : B₁₂ ≅ B₁ ⋙ B₂) (cQ : Q₁₂ ≅ Q₁ ⋙ Q₂)
    (e₁ : R ⋙ Q₁ ⟶ B₁ ⋙ R) (e₂ : R ⋙ Q₂ ⟶ B₂ ⋙ R)
    (e₁₂ : R ⋙ Q₁₂ ⟶ B₁₂ ⋙ R)
    (b₁ : J ⋙ B₁ ⟶ A₁ ⋙ J) (b₂ : J ⋙ B₂ ⟶ A₂ ⋙ J)
    (b₁₂ : J ⋙ B₁₂ ⟶ A₁₂ ⋙ J)
    (he : ∀ L, e₁₂.app L = cQ.hom.app (R.obj L) ≫ Q₂.map (e₁.app L) ≫
      e₂.app (B₁.obj L) ≫ R.map (cB.inv.app L))
    (hb : ∀ K, b₁₂.app K = cB.hom.app (J.obj K) ≫ B₂.map (b₁.app K) ≫
      b₂.app (A₁.obj K) ≫ J.map (cA.inv.app K)) (K : C) :
    (joinedExchange J R A₁₂ B₁₂ Q₁₂ e₁₂ b₁₂).app K =
      cQ.hom.app ((J ⋙ R).obj K) ≫
        Q₂.map ((joinedExchange J R A₁ B₁ Q₁ e₁ b₁).app K) ≫
        (joinedExchange J R A₂ B₂ Q₂ e₂ b₂).app (A₁.obj K) ≫
        (J ⋙ R).map (cA.inv.app K) := by
  simp only [joinedExchange, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id]
  rw [he, hb]
  have h := exchange_slide R B₂ Q₂ e₂ (cB.app (J.obj K)) (b₁.app K)
    (b₂.app (A₁.obj K) ≫ J.map (cA.inv.app K))
    (cQ.hom.app ((J ⋙ R).obj K) ≫ Q₂.map (e₁.app (J.obj K)))
  simpa only [Functor.comp_obj, Functor.comp_map, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc] using h

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
open CondensedOpenProper

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem exactSquareComparison
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : CommSq i f' f j) :
    (derivedOpenCoherencePullbackSquare Λ sq).hom =
      ((pComp Λ f' j).symm ≪≫ eqToIso (congrArg (P Λ) sq.w.symm) ≪≫
        pComp Λ i f).hom := by
  simp only [derivedOpenCoherencePullbackSquare, openCoherencePullbackSquare,
    pComp, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, derived_eqToIso, eqToIso.hom, Category.assoc]

private theorem properExchange_eq
    {Z S : Scheme.{u}} (p : Z ⟶ S) (gZ : Z ⟶ Z) (gS : S ⟶ S)
    (w : gZ ≫ p = p ≫ gS) :
    properExchange Λ p gZ gS w =
      derivedDirectImageOpenRestriction Λ (CommSq.mk w) := by
  let adj := (upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction
  let c := (pComp Λ p gS).symm ≪≫
    eqToIso (congrArg (P Λ) w.symm) ≪≫ pComp Λ gZ p
  exact (Adjunction.exchangeRight_eq_mateEquiv adj adj c).trans
    (congrArg (fun τ : P Λ gS ⋙ P Λ p ⟶ P Λ p ⋙ P Λ gZ ↦
      (mateEquiv adj adj (TwoSquare.mk _ _ _ _ τ)).natTrans)
      (exactSquareComparison Λ (CommSq.mk w)).symm)

private theorem properExchange_comp
    {Z S : Scheme.{u}} (p : Z ⟶ S)
    (gZ hZ : Z ⟶ Z) (gS hS : S ⟶ S)
    [IsIso gZ] [IsIso hZ] [IsIso gS] [IsIso hS]
    (w : gZ ≫ p = p ≫ gS) (v : hZ ≫ p = p ≫ hS)
    (wv : (hZ ≫ gZ) ≫ p = p ≫ (hS ≫ gS)) (K : D Λ Z) :
    (properExchange Λ p (hZ ≫ gZ) (hS ≫ gS) wv).app K =
      (pComp Λ hS gS).hom.app ((R Λ p).obj K) ≫
        (P Λ hS).map ((properExchange Λ p gZ gS w).app K) ≫
        (properExchange Λ p hZ hS v).app ((P Λ gZ).obj K) ≫
        (R Λ p).map ((pComp Λ hZ gZ).inv.app K) := by
  have q := IsPullback.of_horiz_isIso (CommSq.mk w)
  have q' := IsPullback.of_horiz_isIso (CommSq.mk v)
  have h := derivedOpenRestrictionSuccessive Λ q q' K
  simp only [properExchange_eq]
  exact h.symm

private theorem pointReparametrization_comp {k : Type u} [Field k] [IsSepClosed k]
    (f g : Spec (.of k) ⟶ Spec (.of k)) (K : D Λ (Spec (.of k))) :
    (pComp Λ f g).hom.app K ≫
        (P Λ f).map ((pointReparametrization Λ g).hom.app K) ≫
        (pointReparametrization Λ f).hom.app K =
      (pointReparametrization Λ (f ≫ g)).hom.app K := by
  have hd : upperStarComp Λ f g ≪≫
      Functor.isoWhiskerRight (upperStarIsoIdOfIsSepClosed Λ g) (upperStar Λ f) ≪≫
      Functor.leftUnitor (upperStar Λ f) ≪≫ upperStarIsoIdOfIsSepClosed Λ f =
        upperStarIsoIdOfIsSepClosed Λ (f ≫ g) := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
    erw [Category.id_comp]
    exact sepClosedPointTrivialization_comp Λ f g N
  have h := exactTrivialization_comp (upperStar Λ g) (upperStar Λ f)
    (upperStar Λ (f ≫ g)) (upperStarComp Λ f g)
    (upperStarIsoIdOfIsSepClosed Λ g) (upperStarIsoIdOfIsSepClosed Λ f)
    (upperStarIsoIdOfIsSepClosed Λ (f ≫ g)) hd K
  simpa only [pComp, P, pointReparametrization, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc] using h

-- Quantify over the zero structure so this normalization also applies to the
-- instance chosen when compactExchange was defined in another module.
private theorem comparisonInverse_eq_B (pst : Pasting Λ)
    {U' U W' W : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ W'}
    {j : U ⟶ W} {b : W' ⟶ W} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback a j' j b) {zero : HasZeroMorphisms (D Λ U ⥤ D Λ W')} :
    @comparisonInverse _ _ zero _ _ (openMap Λ sq.toCommSq) = (pst.B sq).hom := by
  classical
  have hi : IsIso (openMap Λ sq.toCommSq) := by
    rw [← pst.B_normalized sq]
    infer_instance
  rw [comparisonInverse, dif_pos hi]
  apply @IsIso.inv_eq_of_hom_inv_id _ _ _ _ _ hi
  rw [← pst.B_normalized sq]
  exact (pst.B sq).inv_hom_id

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor moduleObjectDerivedPushforward
  Scheme.instCategory

private theorem compactExchange_eq_joined (pst : Pasting Λ)
    {X Z S : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ S)
    (gX : X ⟶ X) (gZ : Z ⟶ Z) (gS : S ⟶ S) [IsIso gX] [IsIso gZ]
    (wj : gX ≫ j = j ≫ gZ) (wp : gZ ≫ p = p ≫ gS) :
    compactExchange Λ j p gX gZ gS wj wp =
      joinedExchange (J Λ j) (R Λ p) (P Λ gX) (P Λ gZ) (P Λ gS)
        (properExchange Λ p gZ gS wp)
        (pst.B (IsPullback.of_horiz_isIso (CommSq.mk wj))).hom := by
  unfold compactExchange joinedExchange
  rw [comparisonInverse_eq_B Λ pst (IsPullback.of_horiz_isIso (CommSq.mk wj))]

private theorem compactExchange_comp (pst : Pasting Λ)
    {X Z S : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ S)
    (gX hX : X ⟶ X) (gZ hZ : Z ⟶ Z) (gS hS : S ⟶ S)
    [IsIso gX] [IsIso hX] [IsIso gZ] [IsIso hZ] [IsIso gS] [IsIso hS]
    (wj : gX ≫ j = j ≫ gZ) (vj : hX ≫ j = j ≫ hZ)
    (wp : gZ ≫ p = p ≫ gS) (vp : hZ ≫ p = p ≫ hS)
    (wjo : (hX ≫ gX) ≫ j = j ≫ (hZ ≫ gZ))
    (wpo : (hZ ≫ gZ) ≫ p = p ≫ (hS ≫ gS)) (K : D Λ X) :
    (compactExchange Λ j p (hX ≫ gX) (hZ ≫ gZ) (hS ≫ gS) wjo wpo).app K =
      (pComp Λ hS gS).hom.app ((J Λ j ⋙ R Λ p).obj K) ≫
        (P Λ hS).map ((compactExchange Λ j p gX gZ gS wj wp).app K) ≫
        (compactExchange Λ j p hX hZ hS vj vp).app ((P Λ gX).obj K) ≫
        (J Λ j ⋙ R Λ p).map ((pComp Λ hX gX).inv.app K) := by
  let q := IsPullback.of_horiz_isIso (CommSq.mk wj)
  let q' := IsPullback.of_horiz_isIso (CommSq.mk vj)
  let qo := IsPullback.of_horiz_isIso (CommSq.mk wjo)
  have h := joinedExchange_comp (J Λ j) (R Λ p)
    (P Λ gX) (P Λ hX) (P Λ (hX ≫ gX))
    (P Λ gZ) (P Λ hZ) (P Λ (hZ ≫ gZ))
    (P Λ gS) (P Λ hS) (P Λ (hS ≫ gS))
    (pComp Λ hX gX) (pComp Λ hZ gZ) (pComp Λ hS gS)
    (properExchange Λ p gZ gS wp) (properExchange Λ p hZ hS vp)
    (properExchange Λ p (hZ ≫ gZ) (hS ≫ gS) wpo)
    (pst.B q).hom (pst.B q').hom (pst.B qo).hom
    (properExchange_comp Λ p gZ hZ gS hS wp vp wpo)
    (pst.B_vertical q q' qo) K
  simpa only [compactExchange_eq_joined Λ pst] using h

private theorem pointReparametrization_inv_comp
    {k : Type u} [Field k] [IsSepClosed k]
    (f g : Spec (.of k) ⟶ Spec (.of k)) (K : D Λ (Spec (.of k))) :
    (pointReparametrization Λ (f ≫ g)).inv.app K ≫ (pComp Λ f g).hom.app K =
      (pointReparametrization Λ f).inv.app K ≫
        (P Λ f).map ((pointReparametrization Λ g).inv.app K) := by
  apply (cancel_epi ((pointReparametrization Λ (f ≫ g)).hom.app K)).mp
  rw [Iso.hom_inv_id_app_assoc, ← pointReparametrization_comp Λ f g K]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

/-- Compact return respects successive semilinear structures on automorphism squares.
Source: latest blueprint, `lem-fd-realness-pushforward.proof.md`, Step 1, the compact
exchange cocycle and its naturality calculation.
(blueprint: lem-fd-condensed-compact-return-composition).

Proof: normalize the proper mate as derived open restriction and apply successive
restriction pasting. Normalize the inverse open mate as the Cartesian open exchange
from the open/proper pasting package and apply its vertical pasting law. Their middle
pullback compositors cancel; naturality of the proper exchange interchanges the two
remaining maps. The canonical trivialization at the separably closed point has the
same composition law, obtained by applying exact derivation to its ordinary law.
Naturality of exchange and of point trivialization now gives the return equation. -/
theorem compactReturn_comp (hΛ : IsAdmissibleCoefficient Λ)
    {X Z : Scheme.{u}} {k : Type u} [Field k] [IsSepClosed k]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Spec (.of k))
    (gX hX : X ⟶ X) (gZ hZ : Z ⟶ Z)
    (gS hS : Spec (.of k) ⟶ Spec (.of k))
    [IsIso gX] [IsIso hX] [IsIso gZ] [IsIso hZ] [IsIso gS] [IsIso hS]
    (wj : gX ≫ j = j ≫ gZ) (vj : hX ≫ j = j ≫ hZ)
    (wp : gZ ≫ p = p ≫ gS) (vp : hZ ≫ p = p ≫ hS)
    (wjo : (hX ≫ gX) ≫ j = j ≫ (hZ ≫ gZ))
    (wpo : (hZ ≫ gZ) ≫ p = p ≫ (hS ≫ gS))
    (K : D Λ X) (θ₁ : (P Λ gX).obj K ⟶ K) (θ₂ : (P Λ hX).obj K ⟶ K) :
    compactReturn Λ j p (hX ≫ gX) (hZ ≫ gZ) (hS ≫ gS) wjo wpo
        ((pComp Λ hX gX).hom.app K ≫ (P Λ hX).map θ₁ ≫ θ₂) =
      compactReturn Λ j p gX gZ gS wj wp θ₁ ≫
        compactReturn Λ j p hX hZ hS vj vp θ₂ := by
  obtain ⟨pst⟩ := condensedOpenProperPasting Λ hΛ
  have he : ∀ L : D Λ X,
      (pComp Λ hS gS).hom.app ((J Λ j ⋙ R Λ p).obj L) ≫
          (P Λ hS).map ((compactExchange Λ j p gX gZ gS wj wp).app L) ≫
          (compactExchange Λ j p hX hZ hS vj vp).app ((P Λ gX).obj L) =
        (compactExchange Λ j p (hX ≫ gX) (hZ ≫ gZ) (hS ≫ gS) wjo wpo).app L ≫
          (J Λ j ⋙ R Λ p).map ((pComp Λ hX gX).hom.app L) := by
    intro L
    apply cancel_inverse_image (J Λ j ⋙ R Λ p) ((pComp Λ hX gX).app L) _ _
    simpa only [Category.assoc, Iso.app_inv] using
      (compactExchange_comp Λ pst j p gX hX gZ hZ gS hS wj vj wp vp wjo wpo L)
  have h := compact_return_composition (J Λ j ⋙ R Λ p)
    (P Λ gX) (P Λ hX) (P Λ (hX ≫ gX))
    (P Λ gS) (P Λ hS) (P Λ (hS ≫ gS)) (pComp Λ hX gX) (pComp Λ hS gS)
    (compactExchange Λ j p gX gZ gS wj wp)
    (compactExchange Λ j p hX hZ hS vj vp)
    (compactExchange Λ j p (hX ≫ gX) (hZ ≫ gZ) (hS ≫ gS) wjo wpo)
    (pointReparametrization Λ gS) (pointReparametrization Λ hS)
    (pointReparametrization Λ (hS ≫ gS)) he
    (pointReparametrization_inv_comp Λ hS gS) K θ₁ θ₂
  exact h

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
