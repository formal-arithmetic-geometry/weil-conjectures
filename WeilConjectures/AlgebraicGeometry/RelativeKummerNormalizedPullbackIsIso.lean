/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeKummerNormalizedStalkDefinitions
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyPullbackDerivedUnit
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Invertibility of the actual geometric Kummer pullback
Source: blueprint latest, relative Kummer calculation, Step 2.
(blueprint: new-pur-relative-kummer-normalized-pullback-is-iso). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private theorem iso_derivedUnit_isIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).derivedPlus.unit.app K) := by
  apply Adjunction.isIso_derivedPlus_unit_app_of_rightAcyclic
  · intro I _
    infer_instance
  · intro I _
    exact (lowerStar (ModuleCat.{u + 1} A) f).rightAcyclic_of_injective _

/-- The actual geometric pullback from the absolute Kummer line to the iterated
strict-local family is an isomorphism.
Source: blueprint latest, relative Kummer calculation, Step 2; Stacks 0EYU and 03Q9.
(blueprint: new-pur-relative-kummer-normalized-pullback-is-iso).

Proof: equip the small strict-henselization ring with the k-algebra structure from its
structural map. Pullback pasting identifies the iterated family with the canonical
family over this ring. Strict-local invariance makes the canonical normalized unit
invertible, hence its derived adjunction unit is invertible after cancelling the
coefficient comparison. The pasting isomorphism has invertible derived adjunction unit;
the canonical composition formula therefore gives invertibility of the adjunction
unit for the actual h. The module pullback is derived global sections of this unit,
followed by Leray and coefficient comparison, all isomorphisms. -/
theorem normalizedKummerH_isIso (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ N : ℕ) (hℓ : ℓ.Prime) (hN : 1 ≤ N) (hℓk : IsUnit (ℓ : k))
    (A : Type (u + 1)) [CommRing A] [Algebra (ZMod (ℓ ^ N)) A]
    [Module.Free (ZMod (ℓ ^ N)) A] [Module.Finite (ZMod (ℓ ^ N)) A]
    (ζ : k) (hζ : IsPrimitiveRoot ζ (ℓ ^ N))
    (B : Scheme.{u}) (p : B ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B) (b : Bool) :
    IsIso (normalizedKummerH A (ℓ ^ N) (relativeKummerPositive ℓ N hℓ)
      (relativeKummerAnnihilator A (ℓ ^ N))
      (relativeKummerFieldExponentUnit ℓ N hℓk) p b s) := by
  let g := Scheme.strictHenselizationStructuralMap s
  let H := Scheme.strictHenselizationRing s
  let : Algebra k H := (Spec.preimage (g ≫ p)).hom.toAlgebra
  have hg : relativeKummerBaseMap k H = g ≫ p := Spec.map_preimage (g ≫ p)
  let e : normalizedKummerStrictFamily p b s ≅ relativeKummerBaseCurve k H b :=
    pullbackLeftPullbackSndIso (KummerLine.structureMap k b) p g ≪≫
      pullback.congrHom rfl hg.symm
  have he : e.hom ≫ relativeKummerProjection k H b = normalizedKummerStrictH p b s := by
    dsimp only [e, Iso.trans_hom, relativeKummerProjection, normalizedKummerStrictH,
      normalizedKummerStrictV]
    simp [normalizedKummerProjection, g]
  let K := relativeKummerLinePlus A (ℓ ^ N)
    (relativeKummerAnnihilator A (ℓ ^ N)) (KummerLine.curve k b)
  obtain ⟨hlocal, hstrict⟩ := strictHenselizationLocalStructure s
  let : IsLocalRing H := hlocal
  let : IsStrictlyHenselianLocalRing H := hstrict
  have hi := (relativeKummer_strictLocal_invariance k ℓ N hℓ hN hℓk A ζ hζ H).1 b
  rw [RelativeKummerPullbackInvariance] at hi
  have hu := hi.1
  rw [relativeKummerUnit] at hu
  have hcan : IsIso
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        (relativeKummerProjection k H b)).derivedPlus.unit.app K) :=
    IsIso.of_isIso_comp_right _
      ((lowerStar (ModuleCat.{u + 1} A)
        (relativeKummerProjection k H b)).rightDerivedFunctorPlus.map
        (relativeKummerLinePullback A (ℓ ^ N) (relativeKummerPositive ℓ N hℓ)
          (relativeKummerAnnihilator A (ℓ ^ N)) (relativeKummerProjection k H b)
          (relativeKummerExponentUnit (ℓ ^ N) (relativeKummerFieldExponentUnit ℓ N hℓk)
            _ (KummerLine.structureMap k b))
          (relativeKummerExponentUnit (ℓ ^ N) (relativeKummerFieldExponentUnit ℓ N hℓk)
            _ (relativeKummerBaseStructure k H b))).hom)
  have : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e.hom).derivedPlus.unit.app
      ((upperStar (ModuleCat.{u + 1} A)
        (relativeKummerProjection k H b)).mapDerivedCategoryPlus.obj K)) :=
    iso_derivedUnit_isIso A e.hom _
  have hc := derivedPlus_unit_comp_upperStarCompDerivedPlus (ModuleCat.{u + 1} A)
    e.hom (relativeKummerProjection k H b) (normalizedKummerStrictH p b s) he.symm K
  have huactual : IsIso
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        (normalizedKummerStrictH p b s)).derivedPlus.unit.app K) := by
    have : IsIso
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
          (normalizedKummerStrictH p b s)).derivedPlus.unit.app K ≫
          (lowerStar (ModuleCat.{u + 1} A)
            (normalizedKummerStrictH p b s)).rightDerivedFunctorPlus.map
              ((upperStarCompDerivedPlus (ModuleCat.{u + 1} A) e.hom
                (relativeKummerProjection k H b) (normalizedKummerStrictH p b s)
                  he.symm).hom.app K)) := by
      rw [hc]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((lowerStar (ModuleCat.{u + 1} A)
        (normalizedKummerStrictH p b s)).rightDerivedFunctorPlus.map
          ((upperStarCompDerivedPlus (ModuleCat.{u + 1} A) e.hom
            (relativeKummerProjection k H b) (normalizedKummerStrictH p b s)
              he.symm).hom.app K))
  rw [normalizedKummerH, relativeKummerGlobalPullback,
    moduleDerivedCohomologyPullback_eq_derivedUnit]
  infer_instance

end AlgebraicGeometry.Etale
