/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassRootLimitProjection
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionPullback
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionSiteComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictCoextendScalars
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Logic.Small.Defs
import all WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-! # Canonical finite Cartier coordinates after geometric inverse image

Source: diagonal coefficient changes (3), Cartier and Kummer pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace
attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.comp Ext.mapExactFunctor
  DerivedCategory Functor.mapDerivedCategory
private def finiteScalarPull_iso (l n : ℕ) [Fact l.Prime]
    {Z Z' : Scheme.{u}} (g : Z' ⟶ Z) :
    diagonalFiniteToPadic l n Z ⋙
        upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) g ≅
      upperStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) g ⋙
        diagonalFiniteToPadic l n Z' := by
  let q := diagonalResidueProjection.{u} l n
  let adjZ := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Z) q
  let adjZ' := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Z') q
  exact (conjugateIsoEquiv
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} (diagonalResidue.{u} l n)) g).comp adjZ')
    (adjZ.comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) g))).symm
      (Iso.refl _)
private theorem reduced_eq_canonical
    (l : ℕ) [Fact l.Prime] (r : ℕ) (hr : 0 < r)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hZ : IsUnit ((l ^ r : ℕ) : Γ(Z, ⊤))) :
    cartierResidueReducedPro l (Fact.out : l.Prime) r i hI hZ =
      geoCartierCanonicalClass (cartierResidueRing.{u} l r) (l ^ r)
        (pow_pos (Fact.out : l.Prime).pos r) (cartierResidue_cast l r) i hI hZ := by
  let A := cartierResidueRing.{u} l r
  let : Finite A := cartierResidue_finite l (Fact.out : l.Prime) r
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hu⟩ :=
    cartier_reduction_site_comparison l (Fact.out : l.Prime) r hr A
      (cartierResidue_cast l r) i hI hZ
  symm
  apply hu
  refine ⟨Etale.geoCartierEtaleClass A (l ^ r)
    (pow_pos (Fact.out : l.Prime).pos r) (cartierResidue_cast l r) i hI hZ, ?_, ?_⟩
  · exact (Etale.geoCartierEtaleClass_spec A (l ^ r)
      (pow_pos (Fact.out : l.Prime).pos r) (cartierResidue_cast l r) i hI hZ).1
  · exact geoCartierCanonicalClass_comparison A (l ^ r)
      (pow_pos (Fact.out : l.Prime).pos r) (cartierResidue_cast l r) i hI hZ


private theorem finiteCartier_pullback_coordinates
    {l : ℕ} [Fact l.Prime] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤))) (n : ℕ) :
    let F := diagonalClassPull l (baseW g)
    let P := (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
      ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
        (diagonalImmersion Y)).obj
          (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y)))
    let P' := (diagonalFiniteToPadic l n (diagonalSurface Y')).obj
      ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
        (diagonalImmersion Y')).obj
          (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y')))
    let Q := (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
      (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y))
    let Q' := (diagonalFiniteToPadic l n (diagonalSurface Y')).obj
      (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y'))
    ∃ (s : F.obj P ≅ P') (t : F.obj Q ≅ Q'),
      (Ext.mk₀ s.inv).comp
        (((finiteCartierClass l Y hY n).mapExactFunctor F).comp
          (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2) =
        finiteCartierClass l Y' hY' n := by
  let A := diagonalResidue.{u} l n
  let : Finite A := cartierResidue_finite l (Fact.out : l.Prime) (n + 1)
  let N := l ^ (n + 1)
  have hN : 0 < N := pow_pos (Fact.out : l.Prime).pos _
  let hA : (N : A) = 0 := cartierResidue_cast l (n + 1)
  let F := upperStar (ModuleCat.{u + 1} A) (baseW g)
  let W := diagonalClassPull l (baseW g)
  let U := diagonalFiniteToPadic l n (diagonalSurface Y)
  let U' := diagonalFiniteToPadic l n (diagonalSurface Y')
  let P := (lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
    (geoCartierConstant A (ProjectiveLine Y))
  let Q := geoCartierLine A N hA (diagonalSurface Y)
  let κ := geoCartierCanonicalClass A N hN hA (diagonalImmersion Y)
    (diagonalImmersion_cartier Y) (diagonalSurface_power_unit l Y hY n)
  let κ' := geoCartierCanonicalClass A N hN hA (diagonalImmersion Y')
    (diagonalImmersion_cartier Y') (diagonalSurface_power_unit l Y' hY' n)
  obtain ⟨r, hr⟩ := geoCartierCanonicalClass_pullback A N hN hA
  obtain ⟨hsource, hclass⟩ := hr (diagonalImmersion Y) (diagonalImmersion Y')
    (baseW g) (baseP g) (diagonalBaseChange_cartesian g)
    (diagonalImmersion_cartier Y) (diagonalImmersion_cartier Y')
    (diagonalSurface_power_unit l Y hY n) (diagonalSurface_power_unit l Y' hY' n)
  let φ := finiteScalarPull_iso l n (baseW g)
  let source := geoCartierExchange A (diagonalImmersion Y) (diagonalImmersion Y')
    (baseW g) (baseP g) (diagonalBaseChange_cartesian g).toCommSq
  let : IsIso source := hsource
  let line := geoCartierLinePullback A N hA r (baseW g)
    (diagonalSurface_power_unit l Y hY n)
  let s := φ.app P ≪≫ U'.mapIso (asIso source)
  let t := φ.app Q ≪≫ U'.mapIso line
  refine ⟨s, t, ?_⟩
  have h := congrArg (fun z ↦
    (Ext.mk₀ (φ.hom.app P)).comp (z.mapExactFunctor U') (zero_add 2)) hclass
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀] at h
  rw [← Ext.comp_assoc_of_third_deg_zero,
    exact_functor_square U W F U' φ κ, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀] at h
  have hh : (Ext.mk₀ s.hom).comp (κ'.mapExactFunctor U') (zero_add 2) =
      ((κ.mapExactFunctor U).mapExactFunctor W).comp (Ext.mk₀ t.hom) (add_zero 2) := by
    simpa only [s, t, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      asIso_hom, Ext.mk₀_comp_mk₀_assoc] using h
  have hcancel := congrArg (fun z ↦ (Ext.mk₀ s.inv).comp z (zero_add 2)) hh
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    s.inv_hom_id, Ext.mk₀_id_comp] at hcancel
  simpa only [finiteCartierClass, diagonalExactFunctorExtImage,
    reduced_eq_canonical l (n + 1) (Nat.succ_pos n), κ, κ', U, U', W, A, N, hA] using
      hcancel.symm
end AlgebraicGeometry.ProEtale.DiagonalCoefficients



universe w
namespace CategoryTheory
private theorem coordinate_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasExt.{w} A] [HasExt.{w} B] [HasExt.{w} C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} C]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (V : B ⥤ C) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {S H : A} (c : Ext S H 2) {P Q : C}
    (s : V.obj (F.obj S) ≅ P) (t : V.obj (F.obj H) ≅ Q)
    (δ : Ext P Q 2)
    (hnorm : (Ext.mk₀ s.inv).comp
      (((c.mapExactFunctor F).mapExactFunctor V).comp (Ext.mk₀ t.hom) (add_zero 2))
        (zero_add 2) = δ) :
    let z := F.mapDerivedCategory.map c.hom ≫
      (F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor A 0).obj H) ≫
      (((F.mapDerivedCategorySingleFunctor 0).hom.app H)⟦(2 : ℤ)⟧')
    ∃ (s' : V.mapDerivedCategory.obj
        (F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj S)) ≅
      (DerivedCategory.singleFunctor C 0).obj P),
      V.mapDerivedCategory.map z ≫
          (V.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
            ((DerivedCategory.singleFunctor B 0).obj (F.obj H)) ≫
          (((V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj H))⟦(2 : ℤ)⟧') ≫
          (((DerivedCategory.singleFunctor C 0).map t.hom)⟦(2 : ℤ)⟧') =
        s'.hom ≫ δ.hom := by
  dsimp only
  let a := (F.mapDerivedCategorySingleFunctor 0).app S
  let b := (V.mapDerivedCategorySingleFunctor 0).app (F.obj S)
  let s' := V.mapDerivedCategory.mapIso a ≪≫ b ≪≫
    (DerivedCategory.singleFunctor C 0).mapIso s
  refine ⟨s', ?_⟩
  have hc : ((c.mapExactFunctor F).mapExactFunctor V).hom ≫
      (((DerivedCategory.singleFunctor C 0).map t.hom)⟦(2 : ℤ)⟧') =
      (DerivedCategory.singleFunctor C 0).map s.hom ≫ δ.hom := by
    have h := congrArg (fun x ↦ (Ext.mk₀ s.hom).comp x (zero_add 2)) hnorm
    simp only [Ext.mk₀_comp_mk₀_assoc, s.hom_inv_id, Ext.mk₀_id_comp] at h
    have hh := congrArg Ext.hom h
    simpa only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
      ShiftedHom.comp_mk₀, Nat.cast_ofNat] using hh
  have hz : V.mapDerivedCategory.map
        (F.mapDerivedCategory.map c.hom ≫
          (F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
            ((DerivedCategory.singleFunctor A 0).obj H) ≫
          (((F.mapDerivedCategorySingleFunctor 0).hom.app H)⟦(2 : ℤ)⟧')) ≫
        (V.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor B 0).obj (F.obj H)) ≫
        (((V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj H))⟦(2 : ℤ)⟧') =
      V.mapDerivedCategory.map a.hom ≫ b.hom ≫
        ((c.mapExactFunctor F).mapExactFunctor V).hom := by
    simp only [Abelian.Ext.mapExactFunctor_hom, ShiftedHom.map,
      a, b, Iso.app_hom, Functor.map_comp, Nat.cast_ofNat, Category.assoc]
    rw [Iso.hom_inv_id_app_assoc]
    rw [← V.mapDerivedCategory.map_comp_assoc
      ((F.mapDerivedCategorySingleFunctor 0).hom.app S)
      ((F.mapDerivedCategorySingleFunctor 0).inv.app S), Iso.hom_inv_id_app]
    simp only [V.mapDerivedCategory.map_id, Category.id_comp]
  have hz' := congrArg (fun f ↦ f ≫
    (((DerivedCategory.singleFunctor C 0).map t.hom)⟦(2 : ℤ)⟧')) hz
  simp only [Category.assoc] at hz'
  rw [hz']
  simp only [s', Iso.trans_hom, Functor.mapIso_hom]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ V.mapDerivedCategory.map a.hom ≫ b.hom ≫ f) hc
end CategoryTheory

namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace


set_option maxHeartbeats 2000000 in
-- The two exact-functor composition comparisons need extra elaboration.
/-- The evaluated pullback of a normalized system Cartier class has coordinates
in the canonical supported finite constant and finite roots line on the new
surface. This is an equality of arrows, with no test maps or detection assertion.
Source: diagonal coefficient changes (3), naturality of the relative pole
extension and Kummer maps, and the finite positive normalization.
(blueprint: lem-diagonal-pulled-finite-cartier-coordinates).

Proof: take the source and roots coordinates at n from finite_normalization.
Commute exact evaluation with the geometric inverse-image functor. Its
single and shift comparisons give the comparisons displayed below. Commute
fixed p-adic restriction with inverse image using the unit-normalized scalar
comparison. The source then identifies with the finite supported constant by
closed base change, and the roots line identifies with the new roots line by
the canonical Kummer kernel pullback. Both are isomorphisms. The diagonal
base-change square is cartesian and both diagonal ideals are invertible.
Apply geoCartierCanonicalClass_pullback and the reduction/site comparison to
identify the conjugated class with finiteCartierClass on the new surface.
Reassociate the exact-functor single and shift comparisons. These operations
produce the stated equality; no derived functor is assumed faithful. The
normalizations are unchanged and the construction works for empty bases. -/
theorem diagonalPulledFiniteCartier_coordinates
    {l : ℕ} [Fact l.Prime] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    {hY : IsUnit (l : Γ(Y, ⊤))} (hY' : IsUnit (l : Γ(Y', ⊤)))
    {D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))}
    (d : ClassLimitPresentation l Y hY D) (n : ℕ) :
    let F := diagonalClassTowerPull l (baseW g)
    let G := F.mapDerivedCategory
    let V := (evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y'))).obj (op n)
    let L := (diagonalFiniteToPadic l n (diagonalSurface Y')).obj
      (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y'))
    let P := (diagonalFiniteToPadic l n (diagonalSurface Y')).obj
      ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
        (diagonalImmersion Y')).obj
          (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y')))
    ∃ (s : V.mapDerivedCategory.obj
          (G.obj ((DerivedCategory.singleFunctor _ 0).obj
            (D.ordinary.E.obj (diagonalIntegralSource Y)))) ≅
        (DerivedCategory.singleFunctor _ 0).obj P)
      (t : V.obj (F.obj d.H) ≅ L),
      V.mapDerivedCategory.map
          (G.map d.c.hom ≫
            (G.commShiftIso (2 : ℤ)).hom.app
              ((DerivedCategory.singleFunctor _ 0).obj d.H) ≫
            (((F.mapDerivedCategorySingleFunctor 0).hom.app d.H)⟦(2 : ℤ)⟧')) ≫
        (V.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor _ 0).obj (F.obj d.H)) ≫
        (((V.mapDerivedCategorySingleFunctor 0).hom.app (F.obj d.H))⟦(2 : ℤ)⟧') ≫
        (((DerivedCategory.singleFunctor _ 0).map t.hom)⟦(2 : ℤ)⟧') =
      s.hom ≫ (finiteCartierClass l Y' hY' n).hom := by
  dsimp only
  let F := diagonalClassTowerPull l (baseW g)
  let V := (evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y'))).obj (op n)
  let E := (evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj (op n)
  let U := diagonalClassPull l (baseW g)
  have hn := d.finite_normalization
  unfold FiniteCartierNormalization diagonalFiniteCycleNormalization at hn
  obtain ⟨s₀, t₀, _, _, h₀⟩ := hn n
  obtain ⟨s₁, t₁, h₁⟩ := finiteCartier_pullback_coordinates g hY hY' n
  let s := U.mapIso s₀ ≪≫ s₁
  let t := U.mapIso t₀ ≪≫ t₁
  let : IsGrothendieckAbelian.{u + 1} (DiagonalMod l (diagonalSurface Y)) := inferInstance
  let : IsGrothendieckAbelian.{u + 1} (DiagonalSystems l (diagonalSurface Y)) :=
    CategoryTheory.tower_grothendieck _
  have hcomp := exact_functor_square E U F V (Iso.refl _) d.c
  simp only [Iso.refl_hom, NatTrans.id_app, Functor.comp_obj, Ext.mk₀_id_comp,
    Ext.comp_mk₀_id] at hcomp
  have hmap := congrArg (fun z ↦ z.mapExactFunctor U) h₀
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀] at hmap
  have hnorm : (Ext.mk₀ s.inv).comp
      (((d.c.mapExactFunctor F).mapExactFunctor V).comp (Ext.mk₀ t.hom) (add_zero 2))
        (zero_add 2) = finiteCartierClass l Y' hY' n := by
    rw [hcomp]
    have hh := congrArg (fun z ↦ (Ext.mk₀ s₁.inv).comp
      (z.comp (Ext.mk₀ t₁.hom) (add_zero 2)) (zero_add 2)) hmap
    rw [h₁] at hh
    simpa only [s, t, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Functor.map_comp, E, Ext.mk₀_comp_mk₀_assoc,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀] using hh
  obtain ⟨s', hs'⟩ := CategoryTheory.coordinate_transport F V d.c s t
    (finiteCartierClass l Y' hY' n) hnorm
  exact ⟨s', t, hs'⟩


end AlgebraicGeometry.ProEtale.DiagonalCoefficients
