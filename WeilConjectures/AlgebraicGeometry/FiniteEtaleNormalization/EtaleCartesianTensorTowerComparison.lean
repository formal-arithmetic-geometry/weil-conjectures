/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.EtaleCartesianTensorMiddleComparison
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionEtaleFunctorial
import WeilConjectures.AlgebraicGeometry.Section.SectionTensorSquarePasting
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackSquarePrecomposition
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteTypeExceptionalInverseImage
import WeilConjectures.AlgebraicGeometry.DualizingLocality.DualizingCocycleSourceEtale

/-! # Tensor comparison across a Cartesian etale tower -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

private theorem refl_app_trans {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (K : C) {L : D} (e : F.obj K ≅ L) :
    (Iso.refl F).app K ≪≫ e = e := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.app_hom, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

private theorem postcompose_three_products {C : Type*} [Category C]
    {A B D E B' D' F : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (a' : A ⟶ B') (b' : B' ⟶ D') (c' : D' ⟶ E)
    (h : a ≫ b ≫ c = a' ≫ b' ≫ c') (d : E ⟶ F) :
    a ≫ b ≫ c ≫ d = a' ≫ b' ≫ c' ≫ d := by
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ d) h

private theorem three_iso_homs {C : Type*} [Category C]
    {A B D E B' D' : C} (a : A ≅ B) (b : B ≅ D) (c : D ≅ E)
    (a' : A ≅ B') (b' : B' ≅ D') (c' : D' ≅ E)
    (h : (a ≪≫ b) ≪≫ c = (a' ≪≫ b') ≪≫ c') :
    a.hom ≫ b.hom ≫ c.hom = a'.hom ≫ b'.hom ≫ c'.hom := by
  simpa only [Iso.trans_hom, Category.assoc] using congrArg Iso.hom h

/-- Precompose the Cartesian middle comparison by an etale chart, keeping the
specified names of all structure maps and their equality transports.
Source: composition-coherence proof, Step 1
(blueprint: lem-pur-etale-cartesian-tensor-tower-comparison).

Proof: apply the source-etale sigma identity to H, r, and b. Pull the Cartesian
middle comparison along H. Monoidality of the pullback compositor combines its
two inverse tensor constraints, and pullback interchange precomposition gives
the second input. Functoriality of the normalized source-etale comparison for
H and J identifies the output with E for F. Finally equality induction restores
the specified names a, b, F, k, and h, including all canonical congruences.
This uses no nonempty hypothesis and works with either relative dimension zero. -/
theorem etale_cartesian_tensor_tower
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {W R Q D E B : Scheme.{u}}
    [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
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
    (H : W ⟶ R) [H.IsOver (Spec (.of P.field.k))]
    [Etale H] [IsSeparated H] [QuasiCompact H]
    (a : W ⟶ Q) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (b : Q ⟶ B) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (F : W ⟶ D) [F.IsOver (Spec (.of P.field.k))]
    [Etale F] [IsSeparated F] [QuasiCompact F]
    (k : D ⟶ B) [k.IsOver (Spec (.of P.field.k))]
    [IsSeparated k] [LocallyOfFiniteType k] [QuasiCompact k]
    (h : W ⟶ B) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (ha : a = H ≫ r) (hb : b = G ≫ p) (hF : F = H ≫ J)
    (hk : k = q ≫ p) (hh : h = a ≫ b)
    (sq : IsPullback J r q G) (sqF : CommSq F a q G)
    (β : (pull P J).obj (omega P q) ≅ omega P r)
    (hβ : β.hom = beta P q r G J sq) :
    letI := compactification P a
    letI := compactification P b
    letI := compactification P h
    letI := compactification P F
    letI := compactification P k
    letI := compactification P H
    letI := compactification P r
    letI := compactification P q
    letI := compactification P p
    letI := compactification P G
    letI := compactification P J
    letI := compactification P (H ≫ r)
    letI := compactification P (G ≫ p)
    letI := compactification P (q ≫ p)
    letI := compactification P (a ≫ b)
    let w : h = F ≫ k := (by
      simp only [hh, ha, hb, hF, hk]
      calc
        (H ≫ r) ≫ (G ≫ p) = H ≫ ((r ≫ G) ≫ p) := by simp [Category.assoc]
        _ = H ≫ ((J ≫ q) ≫ p) := by rw [sq.w]
        _ = (H ≫ J) ≫ (q ≫ p) := by simp [Category.assoc])
    let A₁ := (congr P a (H ≫ r) ha).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Q) ≪≫
      sourceEtale P H r ≪≫ (pull P H).mapIso β.symm ≪≫
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) H J F hF).app (omega P
          q)).symm
    let B₁ := (pull P a).mapIso
        ((congr P b (G ≫ p) hb).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B) ≪≫
          sourceEtale P G p) ≪≫
      (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} P.Coefficient) sqF).app (omega P p)
    sigma P.Coefficient a b (comp P a b) ≫
        (congr P (a ≫ b) h hh.symm).hom.app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B) ≫
        (congr P h (F ≫ k) w).hom.app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B) ≫
        (sourceEtale P F k).hom =
      Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) A₁.hom B₁.hom ≫
        (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) F (omega P q)
          ((pull P q).obj (omega P p))).inv ≫
        (pull P F).map
          (sigma P.Coefficient q p (comp P q p) ≫
            (congr P (q ≫ p) k hk.symm).hom.app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient)
              B)) := by
  subst a
  subst b
  subst F
  subst k
  subst h
  let := P.noetherian (W ↘ Spec (.of P.field.k))
  let := P.noetherian (R ↘ Spec (.of P.field.k))
  let := P.noetherian (Q ↘ Spec (.of P.field.k))
  let := P.noetherian (D ↘ Spec (.of P.field.k))
  let := P.noetherian (E ↘ Spec (.of P.field.k))
  let := P.noetherian (B ↘ Spec (.of P.field.k))
  let := compactification P H
  let := compactification P r
  let := compactification P q
  let := compactification P p
  let := compactification P G
  let := compactification P J
  let := compactification P (H ≫ J)
  let := compactification P (H ≫ r)
  let := compactification P (G ≫ p)
  let := compactification P (q ≫ p)
  let := compactification P (r ≫ G)
  let := compactification P (J ≫ q)
  let := compactification P (r ≫ G ≫ p)
  let := compactification P (J ≫ q ≫ p)
  let := compactification P (H ≫ r ≫ G ≫ p)
  let := compactification P ((H ≫ r) ≫ G ≫ p)
  let := compactification P ((H ≫ J) ≫ q ≫ p)
  let := SmoothOfRelativeDimension.smooth d r
  let := SmoothOfRelativeDimension.smooth d q
  let := SmoothOfRelativeDimension.smooth e p
  let LH := pull P H
  let w : r ≫ G ≫ p = J ≫ q ≫ p :=
    (Category.assoc r G p).symm.trans
      ((congrArg (fun a ↦ a ≫ p) sq.w.symm).trans (Category.assoc J q p))
  let E₀ := (congr P (r ≫ G ≫ p) (J ≫ q ≫ p) w).app
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B) ≪≫ sourceEtale P J (q ≫ p)
  let B₀ := (pull P r).mapIso (sourceEtale P G p) ≪≫
    (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} P.Coefficient) sq.toCommSq).app (omega P p)
  have hm := etale_cartesian_tensor_middle P r q d G J p e sq β hβ
  have hm' : sigma P.Coefficient r (G ≫ p) (comp P r (G ≫ p)) ≫ E₀.hom =
      (Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) β.inv B₀.hom) ≫
        (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) J (omega P q)
          ((pull P q).obj (omega P p))).inv ≫
        (pull P J).map (sigma P.Coefficient q p (comp P q p)) := by
    exact hm
  have hp := Etale.section_tensor_square_pasting (ModuleCat.{u + 1} P.Coefficient) H J (H ≫ J) rfl
    (omega P r) ((pull P r).obj (omega P (G ≫ p))) (omega P (r ≫ G ≫ p))
    (omega P q) ((pull P q).obj (omega P p)) (omega P (q ≫ p))
    (omega P (H ≫ r)) ((pull P (H ≫ r)).obj (omega P (G ≫ p)))
    ((pull P (H ≫ J)).obj (omega P q))
    ((pull P (H ≫ J)).obj ((pull P q).obj (omega P p)))
    (sigma P.Coefficient r (G ≫ p) (comp P r (G ≫ p)))
    (sigma P.Coefficient q p (comp P q p))
    (sourceEtale P H r)
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) H r).app (omega P (G ≫ p)))
    β.symm B₀ E₀ (Iso.refl _) (Iso.refl _) hm'
  let : SmoothOfRelativeDimension e (G ≫ p) := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + e) (G ≫ p))
  have hs := (DualizingLocality.dualizing_cocycle_source_etale P).2 H 0 r d (G ≫ p) e
  have hc := WeilConjectures.PurityFiniteSetting.SectionRestriction.source_comp_eq P
    H J (q ≫ p) (r ≫ G ≫ p) ((H ≫ r) ≫ G ≫ p) w
    (Category.assoc H r (G ≫ p))
  have hch := three_iso_homs _ _ _ _ _ _ hc
  have hbcomp :
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) H r).hom.app (omega P (G ≫
        p)) ≫
        LH.map B₀.hom ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) H J).inv.app
          ((pull P q).obj (omega P p)) =
      (pull P (H ≫ r)).map (sourceEtale P G p).hom ≫
        (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} P.Coefficient) sqF).hom.app (omega P p)
          := by
    simp only [B₀, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc]
    have hn := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) H
      r).hom.naturality (sourceEtale P G p).hom
    dsimp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    erw [Etale.pullback_square_precomposition P.Coefficient H J r q G sq.toCommSq
      (H ≫ J) (H ≫ r) rfl rfl sqF (omega P p)]
  simp only [Iso.refl_hom, Iso.refl_inv, Category.comp_id,
    Etale.derivedTensorHom_comp_assoc] at hp
  have hsp := postcompose_three_products _ _ _ _ _ _ hs
    (LH.map E₀.hom ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) H J).inv.app
        (omega P (q ≫ p)))
  erw [← hsp] at hp
  have hcp := postcompose_three_products _ _ _ _ _ _ hch.symm
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) H J).inv.app
      (omega P (q ≫ p)))
  have hcanc :
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) H J).app
        (omega P (q ≫ p))).hom ≫
          (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) H J).inv.app
            (omega P (q ≫ p)) = 𝟙 _ := by
    exact ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) H J).app
      (omega P (q ≫ p))).hom_inv_id
  erw [hcp, hcanc, Category.comp_id] at hp
  erw [hbcomp] at hp
  simp only [congr_identity, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Category.comp_id, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  erw [refl_app_trans]
  exact hp

end AlgebraicGeometry.ProEtale.FiniteEtaleNormalization
