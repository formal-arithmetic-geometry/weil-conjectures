/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingFixedCoordinates
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingOpenRestrictionCoordinates

/-! # Open-unit normalization of the explicit finite proper/open comparison

## References

* [Stacks, Tag 03D6]
* [Stacks, Tag 03DI]
* [Stacks, Tag 0F7B]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.finite
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local irreducible] finiteFixedOpenIso finiteFixedPushIso

private theorem conjugate_open_normalization
    {C D T : Type*} [Category C] [Category D] [Category T]
    {J₁ : C ⥤ D} {J₂ : C ⥤ T} {U₁ : D ⥤ C} {U₂ : T ⥤ C} {P : D ⥤ T}
    (a₁ : J₁ ⊣ U₁) (a₂ : J₂ ⊣ U₂) (ρ : P ⋙ U₂ ⟶ U₁)
    {K L : C} (w : K ≅ L) (m : J₂.obj K ⟶ P.obj (J₁.obj K))
    (hm : a₂.homEquiv _ _ m ≫ ρ.app (J₁.obj K) = a₁.unit.app K) :
    a₂.homEquiv _ _ (J₂.map w.inv ≫ m ≫ P.map (J₁.map w.hom)) ≫
      ρ.app (J₁.obj L) = a₁.unit.app L := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc] at hm ⊢
  have h₂ := a₂.unit.naturality w.inv
  have h₁ := a₁.unit.naturality w.hom
  have hρ := ρ.naturality (J₁.map w.hom)
  dsimp only [Functor.comp_map, Functor.id_map] at h₁ h₂ hρ
  rw [← reassoc_of% h₂, hρ]
  calc
    _ = w.inv ≫ (a₂.unit.app K ≫ U₂.map m ≫ ρ.app (J₁.obj K)) ≫
        U₁.map (J₁.map w.hom) := by simp only [Category.assoc]
    _ = w.inv ≫ (a₁.unit.app K ≫ U₁.map (J₁.map w.hom)) := by
      rw [hm]
    _ = a₁.unit.app L := by rw [← h₁, Iso.inv_hom_id_assoc]

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- Transport of the canonical proper/open map preserves the open-adjunction transpose.
This is only the open triangle: no outer proper map or compact-support coordinate occurs. -/
theorem finiteFixedRefinementOpenIso_normalization
    {X Y : Scheme.{w}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (O : FrobeniusExchange.CompactOrigin (Padic.coefficientExtensionRing l E (n + 1)) X)
    (hi : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (c.i ≫ r.hom) =
      proEtaleRingCompositeCoefficients c.i r.hom
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring d.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring c.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull r.hom)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull c.i)) :
    (PurCompactSupport.openDerivedAdjunction
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) d.i).homEquiv _ _
        (finiteFixedRefinementOpenIso l E n r O).hom ≫
      PurCompactSupport.refinementRestriction
        (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) r hi O.K =
    (PurCompactSupport.openDerivedAdjunction
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) c.i).unit.app O.K := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  let e := sfIntrinsicDerivedEquivalence X A
  let K := e.inverse.obj O.K
  let a := (e.counitIso.app O.K).symm
  let : IsIso (PurCompactSupport.openDerivedAdjunction R c.i).unit :=
    PurCompactSupport.openDerivedAdjunction_unit_isIso R c.i
  let : IsIso (AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
    B c.i).unit := Adjunction.isIso_mapDerivedCategoryAdjunction_unit
    (AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction B c.i)
  have hf :
      (AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        B d.i).homEquiv _ _ (FrobeniusExchange.fixedRefinementOpen A r O).hom ≫
      (AlgebraicGeometry.ProEtale.properOpenRestriction (ULift.{w + 1} A)
        r.hom c.i d.i r.i_hom).app
        ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek B c.i).mapDerivedCategory.obj K) =
      (AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        B c.i).unit.app K := by
    have h₀ := AlgebraicGeometry.ProEtale.properOpenProEtaleIso_unit
      (ULift.{w + 1} A) r.hom c.i d.i r.i_hom O.L
    exact conjugate_open_normalization
      (AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction B c.i)
      (AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction B d.i)
      (AlgebraicGeometry.ProEtale.properOpenRestriction (ULift.{w + 1} A)
        r.hom c.i d.i r.i_hom)
      (FrobeniusExchange.fixedOriginWitness A X O)
      (AlgebraicGeometry.ProEtale.properOpenProEtaleIso
        (ULift.{w + 1} A) r.hom c.i d.i r.i_hom O.L).hom h₀
  have ht := finiteOpenRestriction_endomorphism_coordinates l E n r hi K O.K a
    (FrobeniusExchange.fixedRefinementOpen A r O).hom
  dsimp only at ht
  have hunit : (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      B c.i).unit.app K ≫
      (asIso (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        B c.i).unit).inv.app K = 𝟙 K :=
    (asIso (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      B c.i).unit).hom_inv_id_app K
  rw [hf] at ht
  dsimp only [B] at hunit
  rw [hunit] at ht
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, a.hom_inv_id] at ht
  have hword :
      ((PurCompactSupport.openDerivedAdjunction R d.i).homEquiv _ _
        (finiteFixedRefinementOpenIso l E n r O).hom ≫
          PurCompactSupport.refinementRestriction R r hi O.K) ≫
          (asIso (PurCompactSupport.openDerivedAdjunction R c.i).unit).inv.app O.K =
        𝟙 O.K := by
    change ((PurCompactSupport.openDerivedAdjunction R d.i).homEquiv _ _
      (finiteFixedRefinementOpenIso l E n r O).hom ≫
      PurCompactSupport.refinementRestriction R r hi O.K) ≫
      (asIso (PurCompactSupport.openDerivedAdjunction R c.i).unit).inv.app O.K = _ at ht
    exact ht
  exact (cancel_mono ((asIso
    (PurCompactSupport.openDerivedAdjunction R c.i).unit).inv.app O.K)).mp
      (hword.trans ((asIso (PurCompactSupport.openDerivedAdjunction R c.i).unit
        ).hom_inv_id_app O.K).symm)

end WeilConjectures.ConstructibleExceptionalCoefficients
