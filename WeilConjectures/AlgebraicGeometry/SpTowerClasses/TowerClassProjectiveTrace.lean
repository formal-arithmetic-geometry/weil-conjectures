/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Projective.TowerClassProjective
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceTwistedSplittingComponents
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPositiveUnitSquare

/-! # Trace normalization of the prescribed projective system

Source: latest blueprint geometric tower classes, clause (4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
open DiagonalTrace
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem projective_twisted_components
    {S : Scheme.{u}} {b : SpTowerShriek.Base l E}
    {cS : Chern l E S} {cP : Chern l E (ProjectiveLine S)}
    {tS : Twisting l E cS} {tP : Twisting l E cP}
    (p : Projective l E b S cS cP tS tP) :
    let T := tS.T l E ⋙ shiftFunctor (D S (Arings l E S)) (2 : ℤ)
    let a := (shiftFunctor (D S (Arings l E S)) (2 : ℤ)).mapIso
      (tS.positiveUnit l E).symm
    let β := (shiftFunctor (D S (Arings l E S)) (2 : ℤ)).mapIso
        (((tS.T l E).commShiftIso (-2 : ℤ)).app (inverseLine l E cS)) ≪≫
      (shiftFunctorCompIsoId (D S (Arings l E S)) (-2 : ℤ) 2 (by decide)).app
        ((tS.T l E).obj (inverseLine l E cS)) ≪≫ tS.contract l E
    p.twistedUnit l E =
        a.hom ≫ T.map biprod.inl ≫ T.map (p.bq l E) ≫ (p.twistedPush l E).hom ∧
      p.chernAdjoint l E =
        β.inv ≫ T.map biprod.inr ≫ T.map (p.bq l E) ≫ (p.twistedPush l E).hom := by
  let L := SpTowerShriek.pull l E b p.geometry
  let R := SpTowerShriek.push l E b p.geometry
  let adj : L ⊣ R := SpTowerShriek.adjunction l E b p.geometry
  let F := tS.T l E
  let N := tS.N l E
  let V := tP.T l E
  let α := p.positivePullback.derivedIso l E
  let q := (p.coefficientPullback.derivedIso l E).hom
  let r := (p.linePullback.derivedIso l E).hom
  let ps := tS.positiveUnit l E
  let px := tP.positiveUnit l E
  let : p.geometry.pull.Additive := p.geometry.pullAdditive
  let : p.geometry.push.Additive := p.geometry.pushAdditive
  let : PreservesFiniteLimits p.geometry.pull := p.geometry.pullLimits
  let : PreservesFiniteColimits p.geometry.pull := p.geometry.pullColimits
  let : HasKInjectiveResolutions
      (Systems (ProjectiveLine S) (Arings l E (ProjectiveLine S))) :=
    b.kinjective (ProjectiveLine S)
  let : adj.CommShift ℤ :=
    CategoryTheory.canonicalRightDerivedAdjunctionShift
      (C := Systems S (Arings l E S))
      (D := Systems (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
      p.geometry.ordinaryAdjunction
  constructor
  · have hu : adj.homEquiv _ _ r = ps.inv ≫ F.map (unitArrow l E p.coefficientPullback) ≫
        projection l E p.geometry p.positivePullback
          (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))) ≫
          R.map px.hom := by
      apply (cancel_epi ps.hom).mp
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← adj.homEquiv_naturality_left]
      change adj.homEquiv _ _ (L.map ps.hom ≫ r) = _
      rw [positivePullback_unit_square l E p.geometry p.coefficientPullback
        p.linePullback p.positivePullback]
      change adj.homEquiv _ _ (α.hom.app _ ≫ V.map q ≫ px.hom) = _
      rw [← Category.assoc, adj.homEquiv_naturality_right]
      congr 1
      exact (projection_mate_unit L R adj F V α q).symm
    change p.twistedUnit l E =
      ((shiftFunctor _ (2 : ℤ)).mapIso ps.symm).hom ≫
        (F ⋙ shiftFunctor _ (2 : ℤ)).map biprod.inl ≫
        (F ⋙ shiftFunctor _ (2 : ℤ)).map (p.bq l E) ≫ (p.twistedPush l E).hom
    rw [← Functor.map_comp_assoc, Projective.bq, biprod.inl_desc]
    change adj.homEquiv _ _
        ((L.commShiftIso (2 : ℤ)).hom.app _ ≫ r⟦(2 : ℤ)⟧') = _
    rw [adjoint_shift L R adj r, hu]
    simp only [Projective.twistedPush, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Iso.app_hom, Functor.comp_map, Functor.map_comp, Category.assoc,
      asIso_hom]
    rfl
  · let γ := tS.cancelNegative l E
    let δ : N ⋙ F ≅ 𝟭 (D S (Arings l E S)) :=
      (Functor.mapDerivedCategoryCompIso tS.equivalence.inverse
        tS.equivalence.functor).symm ≪≫
      Functor.mapDerivedCategoryNatIso tS.equivalence.counitIso ≪≫
      Functor.mapDerivedCategoryIdIso (Systems S (Arings l E S))
    have htriangle (Y : D S (Arings l E S)) :
        F.map (γ.hom.app Y) = δ.hom.app (F.obj Y) := by
      simpa only [γ, δ, Twisting.cancelNegative, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app] using derived_inverse_triangle tS.equivalence Y
    have hc := retwist_inverse F N γ δ htriangle (tS.inverseUnit l E)
      (p.twistedPush l E) (p.chernAdjoint l E)
    change p.chernAdjoint l E = _
    rw [← Functor.map_comp_assoc, Projective.bq, biprod.inr_desc]
    simpa only [Projective.second, Twisting.contract, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_hom, Iso.symm_inv, Iso.app_inv, Iso.app_hom, Functor.mapIso_inv,
      Functor.mapIso_hom, Functor.comp_map, NatTrans.comp_app, δ,
      Category.assoc] using hc
/-- The actual inverse-splitting trace kills the twisted unit and normalizes Chern.

Source: latest blueprint `sk-prop-sp-tower-geometric-classes.proof.md`, clause (4).
(blueprint: lem-sp-tower-class-projective-trace).

Proof: the coefficient and positive-line pullback squares identify the positive
twist of the first component of bq with the twisted geometric unit, by the
adjunction mate equation and shift compatibility. Untwisting and retwisting
the definition of its second component cancels by the derived tensor/Hom
triangle identity, identifying it with the Chern adjunct. Substitute these
equalities in the trace formula. The twisted pushforward cancels its inverse,
then bq cancels its inverse. The remaining composites are inl followed by snd,
which is zero, and inr followed by snd, which is identity. These are equalities
of actual derived system arrows, before finite evaluation. -/
theorem projective_trace_components
    {S : Scheme.{u}} {b : SpTowerShriek.Base l E}
    {cS : Chern l E S} {cP : Chern l E (ProjectiveLine S)}
    {tS : Twisting l E cS} {tP : Twisting l E cP}
    (p : Projective l E b S cS cP tS tP) [IsIso (p.bq l E)] :
    p.twistedUnit l E ≫ p.trace l E = 0 ∧
      p.chernAdjoint l E ≫ p.trace l E = 𝟙 _ := by
  let T := tS.T l E ⋙ shiftFunctor (D S (Arings l E S)) (2 : ℤ)
  let a := (shiftFunctor (D S (Arings l E S)) (2 : ℤ)).mapIso
    (tS.positiveUnit l E).symm
  let β := (shiftFunctor (D S (Arings l E S)) (2 : ℤ)).mapIso
      (((tS.T l E).commShiftIso (-2 : ℤ)).app (inverseLine l E cS)) ≪≫
    (shiftFunctorCompIsoId (D S (Arings l E S)) (-2 : ℤ) 2 (by decide)).app
      ((tS.T l E).obj (inverseLine l E cS)) ≪≫ tS.contract l E
  obtain ⟨hu, hc⟩ := projective_twisted_components l E p
  change p.twistedUnit l E =
    a.hom ≫ T.map biprod.inl ≫ T.map (p.bq l E) ≫ (p.twistedPush l E).hom at hu
  change p.chernAdjoint l E =
    β.inv ≫ T.map biprod.inr ≫ T.map (p.bq l E) ≫ (p.twistedPush l E).hom at hc
  have ht : p.trace l E = (p.twistedPush l E).inv ≫
      T.map (inv (p.bq l E)) ≫ T.map biprod.snd ≫ β.hom := by
    rfl
  have hunit : p.twistedUnit l E ≫ p.trace l E = 0 := by
    calc
      _ = a.hom ≫ T.map
          (biprod.inl ≫ p.bq l E ≫ inv (p.bq l E) ≫ biprod.snd) ≫
            β.hom := by
        rw [hu, ht]
        simp only [T.map_comp, Category.assoc,
          (p.twistedPush l E).hom_inv_id_assoc]
      _ = 0 := by
        simp only [IsIso.hom_inv_id_assoc, biprod.inl_snd, Functor.map_zero,
          comp_zero, zero_comp]
  have hchern : p.chernAdjoint l E ≫ p.trace l E = 𝟙 _ := by
    calc
      _ = β.inv ≫ T.map
          (biprod.inr ≫ p.bq l E ≫ inv (p.bq l E) ≫ biprod.snd) ≫
            β.hom := by
        rw [hc, ht]
        simp only [T.map_comp, Category.assoc,
          (p.twistedPush l E).hom_inv_id_assoc]
      _ = 𝟙 _ := by
        simp only [IsIso.hom_inv_id_assoc, biprod.inr_snd]
        rw [T.map_id]
        exact (congrArg (fun k ↦ β.inv ≫ k) (Category.id_comp β.hom)).trans
          β.inv_hom_id
  exact ⟨hunit, hchern⟩
end AlgebraicGeometry.ProEtale.SpTowerClasses
