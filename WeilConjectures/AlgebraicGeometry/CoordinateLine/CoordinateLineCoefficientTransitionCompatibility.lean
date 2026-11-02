/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePuritySource
public import WeilConjectures.AlgebraicGeometry.NativeCoordinateLine.NativeCoordinateLineConjugateExponents
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ShiftedExponentTransitionPullback

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoordinateLine
open AffineLinePurity VectorIntegrationSite

/-- The ordinary finite coefficient transition used by the source comparison. -/
def coordinate_line_etale_transition
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (r r' : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0) :
    AffineLinePurity.etaleCoefficient P.coefficients.l P.extension (P.level - 1) T r hA ≅
      AffineLinePurity.etaleCoefficient P.coefficients.l P.extension (P.level - 1) T r' hA' := by
  exact eqToIso (AffineLinePurity.etaleCoefficient_eq P.coefficients.l P.extension
      (P.level - 1) T r hA) ≪≫
    (Etale.ordinaryFinitePullback (Ring P) (ProjectiveLine.affineChart T)).mapIso
      ((shiftFunctor _ (2 : ℤ)).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          (NativeCoordinateLine.transition P (ProjectiveLine T)
            ((ProjectiveLine T ↘ T) ≫ aT) r r' hA hA'))) ≪≫
    (eqToIso (AffineLinePurity.etaleCoefficient_eq P.coefficients.l P.extension
      (P.level - 1) T r' hA')).symm


private theorem common_comparison
    {C : Type*} [Category C] {M X Y Z : C}
    (a : M ≅ X) (b : M ≅ Y) (tr : X ≅ Z) (ts : Y ≅ Z) (tm : M ≅ Z)
    (hr : a ≪≫ tr = tm) (hs : b ≪≫ ts = tm) :
    tr ≪≫ ts.symm = a.symm ≪≫ b := by
  have h := congrArg (fun e ↦ a.symm ≪≫ e ≪≫ ts.symm) (hr.trans hs.symm)
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id,
    Iso.trans_refl] using h

private theorem map_inverse_trans
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {M X Y : C} (a : M ≅ X) (b : M ≅ Y) :
    F.mapIso (a.symm ≪≫ b) = (F.mapIso a).symm ≪≫ F.mapIso b := by
  rw [F.mapIso_trans, F.mapIso_symm]

private theorem map_coordinates
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') (t : X' ≅ Y') :
    F.mapIso (e ≪≫ t ≪≫ e'.symm) =
      F.mapIso e ≪≫ F.mapIso t ≪≫ (F.mapIso e').symm := by
  rw [F.mapIso_trans, F.mapIso_trans, F.mapIso_symm]

private theorem lift_comparison
    {C₀ D₀ C D : Type*} [Category C₀] [Category D₀] [Category C] [Category D]
    (S : C₀ ⥤ C) (T : D₀ ⥤ D) (U : C₀ ⥤ D₀) (F : C ⥤ D)
    (c : S ⋙ F ≅ U ⋙ T) {K L : C₀} {Z : D₀}
    (a : K ⟶ L) (b : U.obj L ⟶ Z) (e : U.obj K ⟶ Z)
    (h : U.map a ≫ b = e) :
    F.map (S.map a) ≫ (c.hom.app L ≫ T.map b) =
      c.hom.app K ≫ T.map e := by
  have hn := c.hom.naturality a
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← T.map_comp, h]

private theorem derived_exponent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    (X : Scheme.{u}) (hX : IsUnit (l : Γ(X, ⊤))) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (VectorIntegrationSite.comparison (Scheme.finiteTateCoefficient l E n) X).mapIso
        ((shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
          (exponentTransition l E n X hX r s hrs hr hs 1))) ≪≫
      twistDerived l E n X hX r hr 1 2 = twistDerived l E n X hX s hs 1 2 := by
  let A := Scheme.finiteTateCoefficient l E n
  let U := comparisonUpperStar (ModuleCat.{u + 1} A) X
  let C := VectorIntegrationSite.comparison A X
  have h : U.mapIso (exponentTransition l E n X hX r s hrs hr hs 1) ≪≫
      twistComparison l E n X hX r hr 1 = twistComparison l E n X hX s hs 1 := by
    simpa only [exponentTransition, twistComparison] using
      ((Scheme.finite_tate_site_descent l E n).choose_spec.2.2.1
        X hX r s hrs hr hs 1).exists.choose_spec.2
  have h₀ := lift_comparison (DerivedCategory.singleFunctor _ 0)
    (DerivedCategory.singleFunctor _ 0) U C (U.mapDerivedCategorySingleFunctor 0)
    (exponentTransition l E n X hX r s hrs hr hs 1).hom
    (twistComparison l E n X hX r hr 1).hom
    (twistComparison l E n X hX s hs 1).hom (congrArg Iso.hom h)
  have h₂ := lift_comparison (shiftFunctor _ (2 : ℤ)) (shiftFunctor _ (2 : ℤ))
    C C (C.commShiftIso (2 : ℤ))
    ((DerivedCategory.singleFunctor _ 0).map
      (exponentTransition l E n X hX r s hrs hr hs 1).hom) _ _ h₀
  apply Iso.ext
  simpa only [twistDerived, Iso.trans_hom, Iso.app, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] using h₂

private theorem pullback_exponent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (l : Γ(Y, ⊤))) (hX : IsUnit (l : Γ(X, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (VectorIntegrationSite.comparison (Scheme.finiteTateCoefficient l E n) X).mapIso
        ((Etale.ordinaryFinitePullback _ f).mapIso
          ((shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
            (exponentTransition l E n Y hY r s hrs hr hs 1)))) ≪≫
      twistPullbackComparison l E n r hr f hY hX =
        twistPullbackComparison l E n s hs f hY hX := by
  let A := Scheme.finiteTateCoefficient l E n
  let C := VectorIntegrationSite.comparison A X
  have hp := shiftedExponentTransition_pullback l E n f hY r s hrs hr hs
    (Etale.projectiveLineTraceTransport (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) A hr)
    (Etale.projectiveLineTraceTransport (l ^ (s + 1))
      (pow_pos (Fact.out : l.Prime).pos _) A hs)
  have hd := congrArg Iso.hom (derived_exponent l E n X hX r s hrs hr hs)
  apply Iso.ext
  simp only [twistPullbackComparison, comparedLinePullback, Iso.trans_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, ← C.map_comp, hp, C.map_comp, Category.assoc]
  exact congrArg (fun g ↦ C.map
    (Etale.ordinaryFiniteShiftedLinePullback A (l ^ (s + 1)) hs
      (Etale.projectiveLineTraceTransport (l ^ (s + 1))
        (pow_pos (Fact.out : l.Prime).pos _) A hs) f
      (by simpa only [Nat.cast_pow] using hY.pow (s + 1))).hom ≫ g) hd

private theorem power_comparison_eq
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) (r s : ℕ) (hrs : r ≤ s)
    (hr : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hs : ((P.coefficients.l ^ (s + 1) : ℕ) : Ring P) = 0) :
    NativeCoordinateLine.powerComparison P Y aY r s hrs hr hs =
      exponentTransition P.coefficients.l P.extension (P.level - 1) Y
        (primeUnit P Y aY) r s hrs hr hs 1 := by
  have ht := (twistCompatibility P.coefficients.l P.extension (P.level - 1)).2.2
    Y (primeUnit P Y aY) r s hrs hr hs 1
  apply ht.unique
  · exact ht.exists.choose_spec
  · simpa only [exponentTransition, twistComparison] using
      ((Scheme.finite_tate_site_descent P.coefficients.l P.extension
        (P.level - 1)).choose_spec.2.2.1
          Y (primeUnit P Y aY) r s hrs hr hs 1).exists.choose_spec

set_option maxHeartbeats 800000 in
-- Elaborating the canonical derived-category coordinate transports exceeds the default budget.
/-- Compatibility of the normalized pro-etale Tate line with the ordinary transition.

Source: the root-normalized finite Tate comparison and its pullback square in
`FiniteTateNormalizedCoherence` and `ShiftedExponentTransitionPullback`
(blueprint: lem-route-coordinate-line-coefficient-twist-compatibility).

Proof: compare both exponent transitions with the unique root-power-normalized
map at the common exponent.  The defining comparison equation for
`twistCompatibility` identifies their maps after site comparison; pullback
naturality and the shift comparison then identify the affine-chart map. -/
theorem coordinate_line_coefficient_twist_compatibility
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (r r' : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0)
    (hP : IsUnit (P.coefficients.l : Γ(ProjectiveLine T, ⊤)))
    (hX : IsUnit (P.coefficients.l : Γ(AffineSpace PUnit.{u + 1} T, ⊤))) :
    coefficientTwistIso P.coefficients.l P.extension (P.level - 1) T r hA hP hX ≪≫
      (coefficientTwistIso P.coefficients.l P.extension (P.level - 1) T r' hA' hP hX).symm =
    (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).mapIso
      (coordinate_line_etale_transition P T aT r r' hA hA') := by
  let M := max r r'
  have hM : ((P.coefficients.l ^ (M + 1) : ℕ) : Ring P) = 0 :=
    (Nat.cast_pow P.coefficients.l (M + 1)).trans
      (pow_eq_zero_of_le (Nat.add_le_add_right (Nat.le_max_left r r') 1)
        ((Nat.cast_pow P.coefficients.l (r + 1)).symm.trans hA))
  have hr := pullback_exponent P.coefficients.l P.extension (P.level - 1)
    (ProjectiveLine.affineChart T) hP hX r M (Nat.le_max_left r r') hA hM
  have hs := pullback_exponent P.coefficients.l P.extension (P.level - 1)
    (ProjectiveLine.affineChart T) hP hX r' M (Nat.le_max_right r r') hA' hM
  rw [← power_comparison_eq P (ProjectiveLine T) ((ProjectiveLine T ↘ T) ≫ aT)
    r M (Nat.le_max_left r r') hA hM] at hr
  rw [← power_comparison_eq P (ProjectiveLine T) ((ProjectiveLine T ↘ T) ≫ aT)
    r' M (Nat.le_max_right r r') hA' hM] at hs
  let C := VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)
  let B := Etale.ordinaryFinitePullback (Ring P) (ProjectiveLine.affineChart T)
  let S := DerivedCategory.singleFunctor
    (Sheaf (ProjectiveLine T).smallEtaleTopology (ModuleCat.{u + 1} (Ring P))) 0
  let H := shiftFunctor (Etale.DerivedCategoryModule (Ring P) (ProjectiveLine T)) (2 : ℤ)
  let F := S ⋙ H ⋙ B ⋙ C
  let pr := NativeCoordinateLine.powerComparison P (ProjectiveLine T)
    ((ProjectiveLine T ↘ T) ≫ aT) r M (Nat.le_max_left r r') hA hM
  let ps := NativeCoordinateLine.powerComparison P (ProjectiveLine T)
    ((ProjectiveLine T ↘ T) ≫ aT) r' M (Nat.le_max_right r r') hA' hM
  let tr := twistPullbackComparison P.coefficients.l P.extension (P.level - 1)
    r hA (ProjectiveLine.affineChart T) hP hX
  let ts := twistPullbackComparison P.coefficients.l P.extension (P.level - 1)
    r' hA' (ProjectiveLine.affineChart T) hP hX
  let tm := twistPullbackComparison P.coefficients.l P.extension (P.level - 1)
    M hM (ProjectiveLine.affineChart T) hP hX
  change F.mapIso pr ≪≫ tr = tm at hr
  change F.mapIso ps ≪≫ ts = tm at hs
  have he := common_comparison (F.mapIso pr) (F.mapIso ps) tr ts tm hr hs
  let t := NativeCoordinateLine.transition P (ProjectiveLine T)
    ((ProjectiveLine T ↘ T) ≫ aT) r r' hA hA'
  have ht : (F.mapIso pr).symm ≪≫ F.mapIso ps = F.mapIso t := by
    exact (map_inverse_trans F pr ps).symm
  let er := eqToIso (etaleCoefficient_eq P.coefficients.l P.extension
    (P.level - 1) T r hA)
  let es := eqToIso (etaleCoefficient_eq P.coefficients.l P.extension
    (P.level - 1) T r' hA')
  have h := congrArg (fun e ↦ C.mapIso er ≪≫ e ≪≫ (C.mapIso es).symm) (he.trans ht)
  have hc : C.mapIso er ≪≫ F.mapIso t ≪≫ (C.mapIso es).symm =
      C.mapIso (coordinate_line_etale_transition P T aT r r' hA hA') := by
    exact (map_coordinates C er es (B.mapIso (H.mapIso (S.mapIso t)))).symm
  simpa only [coefficientTwistIso, eqToIso_refl, Iso.refl_trans,
    Iso.trans_symm, Iso.trans_assoc] using h.trans hc

end AlgebraicGeometry.ProEtale.CoordinateLine
