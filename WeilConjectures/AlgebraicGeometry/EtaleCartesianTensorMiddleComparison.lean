/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.FiniteEtaleDualizingNormalization
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleMiddleSigmaCancellation
import WeilConjectures.AlgebraicGeometry.DualizingCocycleSourceEtale

/-! # Tensor comparison across a Cartesian etale middle square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

private theorem eq_iso_app {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (w : F = G) (K : C) :
    (eqToIso w).app K = eqToIso (congrArg (fun T ↦ T.obj K) w) := by
  subst G
  rfl

private theorem app_square_transport {C D : Type*} [Category C] [Category D]
    {F G H I : C ⥤ D} (c : F ≅ G) (c' : H ≅ G) (d : H ≅ I)
    (w : F = H) (hc : c.symm ≪≫ eqToIso w = c'.symm) (K : C) :
    (c.app K).symm ≪≫ eqToIso (congrArg (fun T ↦ T.obj K) w) ≪≫ d.app K =
      (c'.symm ≪≫ d).app K := by
  have hh := congrArg (fun e ↦ (e ≪≫ d).app K) hc
  apply Iso.ext
  simpa only [NatIso.trans_app, eq_iso_app, Iso.trans_assoc, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv] using congrArg Iso.hom hh

private theorem square_pullback_component
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {R Q D E : Scheme.{u}} (J : R ⟶ D) (r : R ⟶ Q) (q : D ⟶ E) (G : Q ⟶ E)
    (sq : CommSq J r q G) (K : _root_.DerivedCategory (Sheaf E.smallEtaleTopology A)) :
    ((Etale.leftDerivedUpperStarComp A r G).app K).symm ≪≫
        eqToIso (congrArg
          (fun a ↦ (Etale.upperStar A a).leftDerivedFunctor.obj K) sq.w.symm) ≪≫
        (Etale.leftDerivedUpperStarComp A J q).app K =
      (Etale.derivedSquareUpperStarIso A sq).app K := by
  exact app_square_transport (Etale.leftDerivedUpperStarComp A r G)
    (Etale.leftDerivedUpperStarComp A r G (J ≫ q) sq.w)
    (Etale.leftDerivedUpperStarComp A J q) _
    (Etale.leftDerivedUpperStarComp_symm_trans_eqToIso A r G (J ≫ q) sq.w) K

private theorem postcompose_two_products {C : Type*} [Category C]
    {A B B' D E : C} (a : A ⟶ B) (b : B ⟶ D)
    (a' : A ⟶ B') (b' : B' ⟶ D) (h : a ≫ b = a' ≫ b') (c : D ⟶ E) :
    a ≫ b ≫ c = a' ≫ b' ≫ c := by
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ c) h

private theorem precompose_three_maps {C : Type*} [Category C]
    {A B D E F : C} (u : A ⟶ B) (a : B ⟶ D) (b : D ⟶ E)
    (c : E ⟶ F) (d : B ⟶ F) (h : a ≫ b ≫ c = d) :
    ((u ≫ a) ≫ b) ≫ c = u ≫ d := by
  simpa only [Category.assoc] using congrArg (fun k ↦ u ≫ k) h

private theorem inverse_beta_calculation {C : Type*} [Category C]
    {L R T A B : C} (β : L ≅ R) (U : T ≅ R) (s : T ⟶ A)
    (c : A ≅ B) (E : B ≅ L)
    (h : β.hom ≫ U.inv ≫ s = E.inv ≫ c.inv) :
    (((𝟙 R) ≫ (U.inv ≫ s)) ≫ c.hom) ≫ E.hom = β.inv := by
  apply (cancel_epi β.hom).1
  simpa only [Category.assoc, Category.id_comp, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun k ↦ k ≫ c.hom ≫ E.hom) h

section Transport
variable (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]

private theorem congr_identity (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    congr P f f rfl = Iso.refl _ := by
  apply Iso.ext
  simp only [AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.congr,
    conjugateIsoEquiv_apply_hom, Etale.unboundedEtaleLowerShriekCongr,
    Iso.refl_hom, conjugateEquiv_id]

private theorem congr_compose (f g h : X ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (w : f = g) (w' : g = h) :
    congr P f g w ≪≫ congr P g h w' = congr P f h (w.trans w') := by
  subst g
  subst h
  rw [congr_identity, Iso.refl_trans]

private theorem sigma_transport (f f' : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (w : f = f') :
    letI := compactification P f
    letI := compactification P f'
    letI := compactification P g
    letI := compactification P (f ≫ g)
    letI := compactification P (f' ≫ g)
    Etale.derivedTensorHom (ModuleCat P.Coefficient)
        ((congr P f f' w).hom.app (coefficientUnit (ModuleCat P.Coefficient) Y))
        (eqToHom (congrArg (fun a ↦ (pull P a).obj (omega P g)) w)) ≫
      sigma P.Coefficient f' g (comp P f' g) =
    sigma P.Coefficient f g (comp P f g) ≫
      (congr P (f ≫ g) (f' ≫ g) (congrArg (fun a ↦ a ≫ g) w)).hom.app
        (coefficientUnit (ModuleCat P.Coefficient) Z) := by
  cases w
  erw [congr_identity, congr_identity]
  simp only [Iso.refl_hom, NatTrans.id_app]
  erw [eqToHom_refl, Etale.derivedTensorHom_id, Category.id_comp, Category.comp_id]

end Transport

/-- The tensor mate across a Cartesian square with etale horizontal arrows.
The first comparison is inverse beta; the second uses E and the canonical
pullback interchange. Source: composition-coherence proof, Step 1
(blueprint: lem-pur-etale-cartesian-tensor-middle-comparison).

Proof: apply the sigma cocycle with the etale middle arrow and remove its unit
factor by sigma_etale_middle. The finite-etale Cartesian normalization identifies
the resulting first input, after E for J, with inverse beta. The source-etale
cocycle for J moves sigma to its J pullback. Equality transport for the square
matches the intermediate composites. Bifunctoriality combines the two input
maps; exceptional congruence composes by equality induction. All cancellations
use the specified isomorphisms, so the argument includes empty schemes and
zero relative dimensions. -/
theorem etale_cartesian_tensor_middle
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {R Q D E B : Scheme.{u}}
    [R.Over (Spec (.of P.field.k))] [Q.Over (Spec (.of P.field.k))]
    [D.Over (Spec (.of P.field.k))] [E.Over (Spec (.of P.field.k))]
    [B.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (R ↘ Spec (.of P.field.k))]
    [QuasiCompact (R ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Q ↘ Spec (.of P.field.k))]
    [QuasiCompact (Q ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (D ↘ Spec (.of P.field.k))]
    [QuasiCompact (D ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (E ↘ Spec (.of P.field.k))]
    [QuasiCompact (E ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of P.field.k))]
    [QuasiCompact (B ↘ Spec (.of P.field.k))]
    (r : R ⟶ Q) [r.IsOver (Spec (.of P.field.k))]
    [IsSeparated r] [LocallyOfFiniteType r] [QuasiCompact r]
    (q : D ⟶ E) [q.IsOver (Spec (.of P.field.k))]
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    (d : ℕ) [SmoothOfRelativeDimension d q] [SmoothOfRelativeDimension d r]
    (G : Q ⟶ E) [G.IsOver (Spec (.of P.field.k))]
    [Etale G] [IsSeparated G] [QuasiCompact G]
    (J : R ⟶ D) [J.IsOver (Spec (.of P.field.k))]
    [Etale J] [IsSeparated J] [QuasiCompact J]
    (p : E ⟶ B) [p.IsOver (Spec (.of P.field.k))]
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (e : ℕ) [SmoothOfRelativeDimension e p]
    (sq : IsPullback J r q G)
    (β : (pull P J).obj (omega P q) ≅ omega P r)
    (hβ : β.hom = beta P q r G J sq) :
    letI := compactification P r
    letI := compactification P q
    letI := compactification P G
    letI := compactification P J
    letI := compactification P p
    letI := compactification P (r ≫ G)
    letI := compactification P (J ≫ q)
    letI := compactification P (G ≫ p)
    letI := compactification P (q ≫ p)
    letI := compactification P (r ≫ G ≫ p)
    let w := sq.w.symm
    let c := (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} P.Coefficient) sq.toCommSq).app
      (omega P p)
    let wtot : r ≫ G ≫ p = J ≫ q ≫ p :=
      (Category.assoc r G p).symm.trans
        ((congrArg (fun a ↦ a ≫ p) w).trans (Category.assoc J q p))
    sigma P.Coefficient r (G ≫ p) (comp P r (G ≫ p)) ≫
        (congr P (r ≫ G ≫ p) (J ≫ q ≫ p) wtot).hom.app (coefficientUnit (ModuleCat.{u + 1}
          P.Coefficient) B) ≫
        (sourceEtale P J (q ≫ p)).hom =
      Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) β.inv
        ((pull P r).map (sourceEtale P G p).hom ≫ c.hom) ≫
      (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) J (omega P q)
        ((pull P q).obj (omega P p))).inv ≫
      (pull P J).map (sigma P.Coefficient q p (comp P q p)) := by
  dsimp only
  let := compactification P r
  let := compactification P q
  let := compactification P G
  let := compactification P J
  let := compactification P p
  let := compactification P (r ≫ G)
  let := compactification P (J ≫ q)
  let := compactification P (G ≫ p)
  let := compactification P (q ≫ p)
  let := compactification P (r ≫ G ≫ p)
  let := compactification P (J ≫ q ≫ p)
  let := compactification P ((r ≫ G) ≫ p)
  let := compactification P ((J ≫ q) ≫ p)
  let := SmoothOfRelativeDimension.smooth d q
  let := SmoothOfRelativeDimension.smooth d r
  let E₁ := sourceEtale P J q
  let U := targetUnit P.Coefficient r G (rho P G)
  let s := sigma P.Coefficient r G (comp P r G)
  let c₀ := (congr P (r ≫ G) (J ≫ q) sq.w.symm).app (coefficientUnit (ModuleCat.{u + 1}
    P.Coefficient) E)
  have hs := (finite_etale_dualizing_normalization P G).smooth_base_change q r J sq
  have he : (((𝟙 (omega P r)) ≫ (U.inv ≫ s)) ≫ c₀.hom) ≫ E₁.hom = β.inv := by
    have hc : (congr P (J ≫ q) (r ≫ G) sq.w).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient)
      E) =
        c₀.symm := by
      apply Iso.ext
      have h := congr_compose P (J ≫ q) (r ≫ G) (J ≫ q) sq.w sq.w.symm
      have hh := congrArg (fun z ↦ z.hom.app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) E))
        h
      simp only [Iso.trans_hom, NatTrans.comp_app, congr_identity,
        Iso.refl_hom, NatTrans.id_app] at hh
      exact (cancel_mono c₀.hom).1 (by simpa [c₀] using hh)
    rw [← hβ] at hs
    change β.hom ≫ U.inv ≫ s = E₁.inv ≫ _ at hs
    have hch := congrArg Iso.hom hc
    simp only [Iso.app_hom, Iso.symm_hom] at hch
    erw [hch] at hs
    exact inverse_beta_calculation β U s c₀ E₁ hs
  have hm := sigma_etale_middle P r d G p e
  have hj := (DualizingLocality.dualizing_cocycle_source_etale P).2 J 0 q d p e
  have ht := sigma_transport P (r ≫ G) (J ≫ q) p sq.w.symm
  have ho :
      (congr P ((r ≫ G) ≫ p) (r ≫ G ≫ p) (Category.assoc r G p)) ≪≫
          (congr P (r ≫ G ≫ p) (J ≫ q ≫ p)
            ((Category.assoc r G p).symm.trans
              ((congrArg (fun a ↦ a ≫ p) sq.w.symm).trans (Category.assoc J q p)))) =
        (congr P ((r ≫ G) ≫ p) ((J ≫ q) ≫ p)
            (congrArg (fun a ↦ a ≫ p) sq.w.symm)) ≪≫
          congr P ((J ≫ q) ≫ p) (J ≫ q ≫ p) (Category.assoc J q p) := by
    rw [congr_compose, congr_compose]
  erw [hm]
  simp only [Category.assoc]
  have hoh := congrArg (fun z ↦ z.hom.app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B)) ho
  simp only [Iso.trans_hom, NatTrans.comp_app] at hoh
  erw [Category.assoc (sigma P.Coefficient (r ≫ G) p (comp P (r ≫ G) p))]
  erw [reassoc_of% hoh]
  have htp := postcompose_two_products _ _ _ _ ht.symm
    ((congr P ((J ≫ q) ≫ p) (J ≫ q ≫ p) (Category.assoc J q p)).hom.app
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B) ≫
        (sourceEtale P J (q ≫ p)).hom)
  erw [htp, hj]
  erw [Etale.derivedTensorHom_comp_assoc, Etale.derivedTensorHom_comp_assoc,
    Etale.derivedTensorHom_comp_assoc]
  erw [he]
  have hsq := congrArg Iso.hom
    (square_pullback_component (ModuleCat.{u + 1} P.Coefficient) J r q G
      sq.toCommSq (omega P p))
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    eqToIso.hom] at hsq
  have hsq' := precompose_three_maps
    ((pull P r).map (sourceEtale P G p).hom) _ _ _ _ hsq
  erw [hsq']
  rfl

end AlgebraicGeometry.ProEtale.FiniteEtaleNormalization
