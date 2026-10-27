/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.Paper.FrameProductOnSupport
public import Sheaf.RingTheory.GeneratingTupleChain
import Sheaf.Paper.KummerProductUnitPermutation
import Sheaf.Paper.KummerProductShearHomotopy
import all Sheaf.Paper.SupportedCup
import all Sheaf.Paper.SupportedCupFunctoriality
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.SixFunctors.ProEtale.RingSheaf.UpperStarSquare

/-! # Elementary invariance of concrete supported boundary products

Source: the finite elementary-generator comparison in frame independence.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

namespace WeilConjectures.PurityFiniteSetting

set_option allowUnsafeReducibility true in
attribute [local reducible] constant constantEtale

private def frameUnitIso (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    P.constant X ≅ 𝟙_ (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)) := cupConstantIso P X

private theorem comparison_constant_unit (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (P.frameConstantPullback f).hom ≫ (frameUnitIso P X).hom =
    (upperStar (ModuleCat.{u + 1} P.Coefficient) f).map (frameUnitIso P Y).hom ≫
      Functor.OplaxMonoidal.η (upperStar (ModuleCat.{u + 1} P.Coefficient) f) := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let V := upperStar A f
  let FX := comparisonUpperStar A X
  let FY := comparisonUpperStar A Y
  let E := Etale.upperStar A f
  let τ := comparisonUpperStarCompUpperStarIso A f
  have hk := Etale.upperStarConstantSheafIso_hom_app_tensorUnit A f
  have hu := NatTrans.IsMonoidal.unit (τ := τ.hom)
  have hs : (Scheme.upperStarConstantSheafIso A f).hom.app
      (ModuleCat.of P.Coefficient P.Coefficient) =
      Functor.OplaxMonoidal.η E := hk
  unfold frameConstantPullback frameUnitIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [hs, constant_iso_eta, constant_iso_eta]
  change (τ.hom.app (𝟙_ _ ) ≫ FX.map (Functor.OplaxMonoidal.η E)) ≫
    Functor.OplaxMonoidal.η FX =
    V.map (Functor.OplaxMonoidal.η FY) ≫ Functor.OplaxMonoidal.η V
  apply (cancel_epi (Functor.LaxMonoidal.ε V ≫
    V.map (Functor.LaxMonoidal.ε FY))).mp
  dsimp only [Functor.LaxMonoidal.comp_ε] at hu
  simp only [Category.assoc] at hu ⊢
  rw [reassoc_of% hu]
  change Functor.LaxMonoidal.ε FX ≫
    FX.map (Functor.LaxMonoidal.ε E) ≫ FX.map (Functor.OplaxMonoidal.η E) ≫
    Functor.OplaxMonoidal.η FX =
    Functor.LaxMonoidal.ε V ≫ V.map (Functor.LaxMonoidal.ε FY) ≫
    V.map (Functor.OplaxMonoidal.η FY) ≫ Functor.OplaxMonoidal.η V
  rw [← FX.map_comp_assoc, Functor.Monoidal.ε_η, FX.map_id, Category.id_comp,
    Functor.Monoidal.ε_η, ← V.map_comp_assoc, Functor.Monoidal.ε_η,
    V.map_id, Category.id_comp, Functor.Monoidal.ε_η]

private instance congr_monoidal (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    NatTrans.IsMonoidal (lowerStarCongr (ModuleCat.{u + 1} A) h).hom := by
  subst h
  rw [lowerStarCongr_rfl]
  exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 (lowerStar (ModuleCat.{u + 1} A) f)))

private instance id_monoidal (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    NatTrans.IsMonoidal (lowerStarId (ModuleCat.{u + 1} A) X).hom := by
  unfold lowerStarId
  infer_instance

private theorem iso_monoidal (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    NatTrans.IsMonoidal
      (upperStarIsoLowerStarInv (ModuleCat.{u + 1} P.Coefficient) e).hom := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let : (lowerStarEquivalence A e).symm.functor.Monoidal :=
    show (lowerStar A e.inv).Monoidal from .ofLaxMonoidal _
  let : (lowerStarEquivalence A e).symm.inverse.LaxMonoidal :=
    show (lowerStar A e.hom).LaxMonoidal from inferInstance
  let adj₂ := (lowerStarEquivalence A e).symm.toAdjunction
  have h₂ : NatTrans.IsMonoidal adj₂.unit := by
    change NatTrans.IsMonoidal (lowerStarComp A e.inv e.hom ≪≫
      lowerStarCongr A e.inv_hom_id ≪≫ lowerStarId A Y).inv
    rw [Iso.trans_inv, Iso.trans_inv]
    infer_instance
  exact isMonoidal_leftAdjointUniq_hom (upperStarLowerStarAdjunction A e.hom) adj₂

private theorem scalar_transport {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F G : C ⥤ D) [F.Monoidal] [G.LaxMonoidal] (τ : F ≅ G)
    [NatTrans.IsMonoidal τ.hom] {M : C} (e : M ≅ 𝟙_ C)
    (b : F.obj M ≅ 𝟙_ D)
    (hb : b.hom = F.map e.hom ≫ Functor.OplaxMonoidal.η F) :
    Functor.LaxMonoidal.ε G ≫ G.map e.inv ≫ τ.inv.app M ≫ b.hom = 𝟙 _ := by
  rw [hb, τ.inv.naturality_assoc]
  simp only [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id,
    Category.id_comp]
  rw [NatTrans.IsMonoidal.unit_assoc]
  exact Functor.Monoidal.ε_η F

private theorem frameIso_scalar (P : PurityFiniteSetting.{u})
    {Z W : Scheme.{u}} (e : Z ≅ W) :
    Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} P.Coefficient) e.hom) ≫
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) e.hom).map (frameUnitIso P Z).inv ≫
      (upperStarIsoLowerStarInv (ModuleCat.{u + 1} P.Coefficient) e.symm).inv.app
        (P.constant Z) ≫
      (P.frameConstantPullback e.inv).hom ≫ (frameUnitIso P W).hom = 𝟙 _ := by
  let A := ModuleCat.{u + 1} P.Coefficient
  have := iso_monoidal P e.symm
  exact scalar_transport (upperStar A e.inv) (lowerStar A e.hom)
    (upperStarIsoLowerStarInv A e.symm) (frameUnitIso P Z)
    (P.frameConstantPullback e.inv ≪≫ frameUnitIso P W)
    (comparison_constant_unit P e.inv)

private theorem restriction_congr (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} {i j : Z ⟶ X} (h : i = j) :
    cupCoefficientRestriction P i ≫
      (lowerStarCongr (ModuleCat.{u + 1} P.Coefficient) h).hom.app (P.constant Z) =
        cupCoefficientRestriction P j := by
  subst j
  simp only [lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]

set_option allowUnsafeReducibility true in
private theorem frameRestriction_unit (P : PurityFiniteSetting.{u})
    {Z W : Scheme.{u}} (e : Z ⟶ W) :
    cupCoefficientRestriction P e = (frameUnitIso P W).hom ≫
      Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} P.Coefficient) e) ≫
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) e).map (frameUnitIso P Z).inv :=
by
  exact cupRestriction_eq_laxUnit P e

set_option allowUnsafeReducibility true in
attribute [local irreducible] frameUnitIso

private theorem frameIso_normalized (P : PurityFiniteSetting.{u})
    {Z W X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X) (e : Z ≅ W)
    (h : e.hom ≫ j = i) :
    cupCoefficientRestriction P i ≫ (P.frameClosedCoefficientIso i j e h).hom =
      cupCoefficientRestriction P j := by
  let q := ((upperStarIsoLowerStarInv (ModuleCat.{u + 1} P.Coefficient) e.symm).app
    (P.constant Z)).symm ≪≫ P.frameConstantPullback e.inv
  have hq : cupCoefficientRestriction P e.hom ≫ q.hom = 𝟙 _ := by
    rw [frameRestriction_unit]
    exact frameRestriction_normalized
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) e.hom)
      (frameUnitIso P Z) (frameUnitIso P W) _ q.hom (frameIso_scalar P e)
  exact frameRestriction_iso
    (lowerStar (ModuleCat.{u + 1} P.Coefficient) j)
    (cupCoefficientRestriction P i)
    ((lowerStarCongr (ModuleCat.{u + 1} P.Coefficient) h.symm).app (P.constant Z))
    (cupCoefficientRestriction P j)
    ((lowerStarComp (ModuleCat.{u + 1} P.Coefficient) e.hom j).app (P.constant Z))
    (cupCoefficientRestriction P e.hom) q
    ((restriction_congr P h.symm).trans (cupRestriction_comp P e.hom j).symm) hq

private theorem frameIso_comp (P : PurityFiniteSetting.{u})
    {Z W T X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X) (k : T ⟶ X)
    [IsClosedImmersion i] (e : Z ≅ W) (d : W ≅ T)
    (he : e.hom ≫ j = i) (hd : d.hom ≫ k = j) :
    (P.frameClosedCoefficientIso i j e he).hom ≫
      (P.frameClosedCoefficientIso j k d hd).hom =
      (P.frameClosedCoefficientIso i k (e ≪≫ d)
        (by simp only [Iso.trans_hom, Category.assoc, hd, he])).hom := by
  have := cupRestriction_epi P i
  exact frameNormalized_comp (cupCoefficientRestriction P i)
    (cupCoefficientRestriction P j) (cupCoefficientRestriction P k) _ _ _
    (frameIso_normalized P i j e he) (frameIso_normalized P j k d hd)
    (frameIso_normalized P i k (e ≪≫ d) _)

private theorem frameIso_refl (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (P.frameClosedCoefficientIso i i (Iso.refl Z) (by simp)).hom = 𝟙 _ := by
  have := cupRestriction_epi P i
  exact frameNormalized_id (cupCoefficientRestriction P i) _
    (frameIso_normalized P i i (Iso.refl Z) _)

set_option allowUnsafeReducibility true in
attribute [local irreducible] frameClosedCoefficientIso cupSingle frameBoundaryProduct

private def ProductRelated (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) (f g : Fin c → Γ(X, ⊤)) : Prop :=
  ∃ (e : X.zeroLocusSubscheme (Set.range g) ≅ X.zeroLocusSubscheme (Set.range f))
    (he : e.hom ≫ X.zeroLocusSubschemeι (Set.range f) =
      X.zeroLocusSubschemeι (Set.range g)),
    P.frameBoundaryProduct X aX c g =
      (cupSingle P X).map (P.frameClosedCoefficientIso
        (X.zeroLocusSubschemeι (Set.range g)) (X.zeroLocusSubschemeι (Set.range f))
        e he).hom ≫ P.frameBoundaryProduct X aX c f

private theorem productRelated_refl (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) (f : Fin c → Γ(X, ⊤)) :
    ProductRelated P X aX c f f := by
  refine ⟨Iso.refl _, by simp, ?_⟩
  rw [frameIso_refl, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem productRelated_trans (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) {f g h : Fin c → Γ(X, ⊤)}
    (hfg : ProductRelated P X aX c f g) (hgh : ProductRelated P X aX c g h) :
    ProductRelated P X aX c f h := by
  obtain ⟨e, he, hfg⟩ := hfg
  obtain ⟨d, hd, hgh⟩ := hgh
  refine ⟨d ≪≫ e, by simp only [Iso.trans_hom, Category.assoc, he, hd], ?_⟩
  have hh := frameForwardTransport_trans (cupSingle P X)
    (P.frameClosedCoefficientIso _ _ d hd).hom
    (P.frameClosedCoefficientIso _ _ e he).hom _ _ _ hfg hgh
  rw [frameIso_comp] at hh
  exact hh

private theorem productRelated_step (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) {f g : Fin c → Γ(X, ⊤)}
    (h : Module.GeneratingTupleStep (R := Γ(X, ⊤)) f g) :
    ProductRelated P X aX c f g := by
  classical
  rcases h with ⟨i, a, h⟩ | ⟨i, j, hij, h⟩ | ⟨i, j, a, hij, h⟩
  · let v : Fin c → Γ(X, ⊤)ˣ := fun k ↦ if k = i then a else 1
    have hg : g = fun k ↦ (v k : Γ(X, ⊤)) * f ((Equiv.refl (Fin c)) k) := by
      funext k
      rw [h k]
      by_cases hk : k = i <;> simp [v, hk, smul_eq_mul]
    subst g
    obtain ⟨hs, heq⟩ := P.frameBoundaryProduct_unit_permutation X aX c f
      (Equiv.refl (Fin c)) v
    exact ⟨eqToIso (congrArg Scheme.IdealSheafData.subscheme hs),
      Scheme.IdealSheafData.eqToHom_comp_subschemeι hs, heq⟩
  · have hg : g = fun k ↦ ((1 : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) * f ((Equiv.swap i j) k) := by
      funext k
      rw [h k]
      by_cases hki : k = i
      · subst k
        simp only [Equiv.swap_apply_left, ite_true, Units.val_one, one_mul]
      · by_cases hkj : k = j
        · subst k
          simp only [Equiv.swap_apply_right, if_neg hij.symm, ite_true,
            Units.val_one, one_mul]
        · simp only [Equiv.swap_apply_of_ne_of_ne hki hkj, if_neg hki, if_neg hkj,
            Units.val_one, one_mul]
    subst g
    obtain ⟨hs, heq⟩ := P.frameBoundaryProduct_unit_permutation X aX c f
      (Equiv.swap i j) (fun _ ↦ 1)
    exact ⟨eqToIso (congrArg Scheme.IdealSheafData.subscheme hs),
      Scheme.IdealSheafData.eqToHom_comp_subschemeι hs, heq⟩
  · have hg : g = kummerShearTuple f i j a := funext h
    subst g
    have hc : 2 ≤ c := by
      have hi := i.isLt
      have hj := j.isLt
      by_contra hc
      have : i = j := Fin.ext (by omega)
      exact hij this
    obtain ⟨e, he, _, g0, g1, sq0, sq1, _, _, _, heq⟩ :=
      P.kummerProduct_shear_homotopy aX c hc f i j hij a
    refine ⟨e, he, ?_⟩
    exact frameSingleTransport_cancel (cupSingle P X)
      (P.frameClosedCoefficientIso _ _ e he) _ _ heq

private theorem productRelated_chain (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) {f g : Fin c → Γ(X, ⊤)}
    (h : Relation.ReflTransGen (Module.GeneratingTupleStep (R := Γ(X, ⊤))) f g) :
    ProductRelated P X aX c f g := by
  induction h with
  | refl => exact productRelated_refl P X aX c f
  | tail h hstep ih =>
    exact productRelated_trans P X aX c ih (productRelated_step P X aX c hstep)

/-- Compose elementary Kummer-product invariances on a fixed closed support.
Source: the finite-chain assembly in frame independence
(blueprint: lem-pur-frame-product-elementary).
Proof: unit scalings and transpositions use the unit/permutation theorem. A shear
uses the interpolation theorem; its inverse support transport is cancelled by
postcomposition. Closed-source coefficient transports are normalized on the epic
constant restriction, hence compose. Induct on the finite chain and transport to
the specified common support. Its monic immersion makes the final support isomorphism
unique, so it equals the isomorphism specified at the endpoint. -/
theorem frameProductOnSupport_elementary (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (a : X ⟶ Spec (.of P.field.k)) (c : ℕ) (f g : Fin c → Γ(X, ⊤))
    (ef : X.zeroLocusSubscheme (Set.range f) ≅ Z)
    (hf : ef.hom ≫ i = X.zeroLocusSubschemeι (Set.range f))
    (eg : X.zeroLocusSubscheme (Set.range g) ≅ Z)
    (hg : eg.hom ≫ i = X.zeroLocusSubschemeι (Set.range g))
    (h : Relation.ReflTransGen (Module.GeneratingTupleStep (R := Γ(X, ⊤))) f g) :
    P.frameProductOnSupport i a c f ef hf = P.frameProductOnSupport i a c g eg hg := by
  obtain ⟨d, hd, heq⟩ := productRelated_chain P X a c h
  have hed : d ≪≫ ef = eg := by
    apply Iso.ext
    apply (cancel_mono i).mp
    simp only [Iso.trans_hom, Category.assoc, hf, hg, hd]
  have hc := frameIso_comp P _ _ i d ef hd hf
  simp only [hed] at hc
  have hec : P.frameClosedCoefficientIso _ _ d hd ≪≫
      P.frameClosedCoefficientIso _ i ef hf = P.frameClosedCoefficientIso _ i eg hg :=
    Iso.ext hc
  exact frameSingleTransport_comp (cupSingle P X)
    (P.frameClosedCoefficientIso _ _ d hd) (P.frameClosedCoefficientIso _ i ef hf)
    (P.frameClosedCoefficientIso _ i eg hg) hec _ _ heq

end WeilConjectures.PurityFiniteSetting
