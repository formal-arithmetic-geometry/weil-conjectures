/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.CechTower
public import WeilConjectures.CategoryTheory.Sites.IsCechNerveAt
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar

/-!
# Čech complexes of pulled back injective étale sheaves

Let `S` be a scheme, `A` a Grothendieck abelian category and `I` an injective `A`-valued sheaf on
the small étale site of `S`. For every morphism `q : W ⟶ U` of the affine pro-étale site of `S`,
the Čech complex of the comparison pullback `ν^* I` along `q` is exact in positive degrees
(`AlgebraicGeometry.ProEtale.exactAt_cechComplex_comparisonUpperStar_obj`).

Writing `q` as a cofiltered limit of morphisms `qⱼ : Wⱼ ⟶ Uⱼ` of affine étale `S`-schemes, the
iterated fibre products of `q` are the limits of those of the `qⱼ`
(`AlgebraicGeometry.Scheme.AffineProEt.cechTower`), so that the continuity of the comparison
pullback (`AlgebraicGeometry.ProEtale.isColimit_comparisonUpperStar_mapCocone`) writes the Čech
complex of `ν^* I` along `q` as the filtered colimit of the Čech complexes of `ν_* ν^* I ≅ I`
along the `qⱼ`. These are exact since `I` is injective, and filtered colimits are exact in `A`.
This is the first limit argument of blueprint `lem-weil-pbc-comparison-injective-acyclicity`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section

variable {S : Scheme.{u}} {J : Type u} [SmallCategory J] [IsCofiltered J] {M : S.AffineProEt}

lemma presentationCone_π_app (pres : RelativeLimitPresentation J (AffineEtale.toAffineProEt S) M)
    (j : J) : (presentationCone pres).π.app j = (AffineProEt.toProEt S).map (pres.π.app j) := by
  simp [presentationCone, AffineEtale.toAffineProEtCompToProEtIso]

/-- Blueprint `lem-weil-pbc-comparison-sections`: Sections of the comparison inverse image.

For an object `U = limⱼ Uⱼ` of the affine pro-étale site, presented as a cofiltered limit of
affine étale `S`-schemes, the sections of `ν^* F` over `U` are the filtered colimit of the
sections of `ν^* F` over the `Uⱼ`, which are the sections `F(Uⱼ)` by the invertibility of the
unit `F ⟶ ν_* ν^* F` (`AlgebraicGeometry.ProEtale.isIso_comparisonAdjunction_unit`). -/
theorem isColimit_comparisonUpperStar_presentationCone (F : Sheaf S.smallEtaleTopology A)
    (pres : RelativeLimitPresentation J (AffineEtale.toAffineProEt S) M) :
    Nonempty (IsColimit (((comparisonUpperStar A S).obj F).obj.mapCocone
      (presentationCone pres).op)) :=
  isColimit_comparisonUpperStar_mapCocone A F (presentationDiagram pres) (presentationCone pres)
    (isLimitPresentationCone pres)

end

/-- **Čech complexes of pulled back injectives.** For an injective étale sheaf `I` and a
morphism `q : W ⟶ U` of the affine pro-étale site, the Čech complex of `ν^* I` along `q` is exact
in positive degrees. -/
theorem exactAt_cechComplex_comparisonUpperStar_obj {S : Scheme.{u}}
    (I : Sheaf S.smallEtaleTopology A) [Injective I] {W U : S.AffineProEt} (q : W ⟶ U) (n : ℕ) :
    ((Arrow.mk ((AffineProEt.toProEt S).map q)).cechComplex
      ((comparisonUpperStar A S).obj I).obj).ExactAt (n + 1) := by
  have : HasFilteredColimitsOfSize.{u, u} A :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  have : AB5OfSize.{u, u} A := AB5OfSize_of_univLE.{u, u, u + 1, u + 1} A
  obtain ⟨J, _, _, pW, pU, hom, rfl⟩ := AffineProEt.exists_relativeLimitPresentation_hom _ q
  let T := AffineProEt.cechTower (q := hom.map) (presU := pU) (presW := pW) (fW := hom) rfl
  let G := ((comparisonUpperStar A S).obj I).obj
  -- the étale sheaf `ν_* ν^* I`, isomorphic to `I`, is injective
  let I' := (comparisonLowerStar A S).obj ((comparisonUpperStar A S).obj I)
  have : IsIso ((comparisonAdjunction A S).unit.app I) := by
    have := isIso_comparisonAdjunction_unit A S
    infer_instance
  have : Injective I' := Injective.of_iso (asIso ((comparisonAdjunction A S).unit.app I)) ‹_›
  have : (presheafToSheaf S.smallEtaleTopology A).PreservesHomology := {}
  -- the stage-wise Čech differentials
  let X (k : ℕ) : Jᵒᵖ ⥤ A := (presentationDiagram (T k).presM ⋙ toProEt S).op ⋙ G
  let d (k : ℕ) : X k ⟶ X (k + 1) := ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
    Functor.whiskerRight (NatTrans.op (Functor.whiskerRight (Functor.whiskerRight
      ((T (k + 1)).faceHom (T k) i).natTrans (AffineEtale.Spec S)) (toProEt S))) G
  have hd (k : ℕ) (j : Jᵒᵖ) : (d k).app j =
      ((T (k + 1)).ét j.unop).faceD ((T k).ét j.unop) I'.obj := by
    simp only [d, NatTrans.app_sum, NatTrans.app_zsmul, IsCechNerveAt.faceD]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    rw [← AffineProEt.CechTower.faceHom_app]
    rfl
  have hdd (k : ℕ) : d k ≫ d (k + 1) = 0 := by
    ext j
    rw [NatTrans.comp_app, hd, hd, IsCechNerveAt.faceD_comp_faceD]
    rfl
  let Sh : ShortComplex (Jᵒᵖ ⥤ A) := ShortComplex.mk (d n) (d (n + 1)) (hdd n)
  have hSh : Sh.Exact := by
    rw [ShortComplex.exact_iff_evaluation]
    intro j
    have h := IsCechNerveAt.exact_faceDShortComplex ((T (n + 2)).ét j.unop)
      ((T (n + 1)).ét j.unop) ((T n).ét j.unop) I'.obj
      (Arrow.exactAt_cechComplex_of_adjunction _ (sheafificationAdjunction _ A) I' n)
    refine (ShortComplex.exact_iff_of_iso ?_).2 h
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [Sh, hd]) (by simp [Sh, hd])
  -- the colimit cocones given by the continuity of `ν^*`
  have hc (k : ℕ) := (isColimit_comparisonUpperStar_mapCocone A I
    (presentationDiagram (T k).presM) (presentationCone (T k).presM)
    (isLimitPresentationCone (T k).presM)).some
  have hι (k : ℕ) (j : Jᵒᵖ) : (G.mapCocone (presentationCone (T k).presM).op).ι.app j ≫
      (T (k + 1)).pro.faceD (T k).pro G =
        (d k).app j ≫ (G.mapCocone (presentationCone (T (k + 1)).presM).op).ι.app j := by
    simp only [Functor.mapCocone_ι_app, Cone.op_ι_app, presentationCone_π_app,
      IsCechNerveAt.faceD, Preadditive.comp_sum, Preadditive.comp_zsmul, d, NatTrans.app_sum,
      NatTrans.app_zsmul, Preadditive.sum_comp, Preadditive.zsmul_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    rw [← G.map_comp, ← AffineProEt.CechTower.map_faceHom_map]
    dsimp
    rw [← G.map_comp, ← op_comp, ← op_comp, ← Functor.map_comp, ← Functor.map_comp,
      RelativeLimitPresentation.Hom.map_π]
    rfl
  have h := colim.exact_mapShortComplex Sh hSh (hc n) _ (hc (n + 1)) _ (hc (n + 2))
    ((T (n + 1)).pro.faceD (T n).pro G) ((T (n + 2)).pro.faceD (T (n + 1)).pro G)
    (hι n) (hι (n + 1))
  refine IsCechNerveAt.exactAt_of_exact_faceDShortComplex ((T (n + 2)).pro) ((T (n + 1)).pro)
    ((T n).pro) G ?_
  exact h

end AlgebraicGeometry.ProEtale
