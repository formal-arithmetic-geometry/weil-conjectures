/-
Copyright (c) 2026 The Weil conjectures formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (u9 C1), after a suggestion of Nailin Guan (Zulip #1864)
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteTateLineReading
public import WeilConjectures.WeilSheaf.SmoothPurityReadingComposition
public import WeilConjectures.WeilSheaf.SmoothPurityIntegralTateReductionPullback
import WeilConjectures.Tactic.ExactModProofs

/-! # A separate coefficient interface for finite Tate reading

The coefficient types and all comparison data are hidden from importing modules.
Each compatibility equation is checked here; composition uses only this exported API.
-/

set_option profiler true
set_option profiler.threshold 1

public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
namespace K4FiniteCoefficient

open Scheme CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

/-- The finite ring in the universe used by sheaves. -/
@[no_expose] def coefficient : Type (u + 1) := ULift.{u + 1} T

lemma coefficient_eq : coefficient.{u} T = ULift.{u + 1} T := (rfl)

@[no_expose] noncomputable instance coefficientRing : CommRing (coefficient.{u} T) :=
  inferInstanceAs (CommRing (ULift.{u + 1} T))

/-- The associated condensed ring. -/
@[no_expose] noncomputable def ringObj : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  Profinite.continuousMapRingObj T

lemma ringObj_eq : ringObj.{u} T = Profinite.continuousMapRingObj T := (rfl)

@[no_expose] noncomputable instance ringObjMon : MonObj (ringObj.{u} T) :=
  inferInstanceAs (MonObj (Profinite.continuousMapRingObj T))

instance ringObjComm : IsCommMonObj (ringObj.{u} T) :=
  inferInstanceAs (IsCommMonObj (Profinite.continuousMapRingObj T))

/-- The coefficient model equivalence. -/
@[no_expose] noncomputable def comparison (Z : Scheme.{u}) :
    Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj (ringObj T) Z) ≌
      Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (coefficient T)) :=
  finiteCoefficientModEquivalence Z T

/-- The pullback comparison uses only the exported coefficient vocabulary. -/
@[no_expose] noncomputable def comparePull {X Y : Scheme.{u}} (g : X ⟶ Y) :
    CondensedRing.upperStar (ringObj T) g ⋙ (comparison T X).functor ≅
      (comparison T Y).functor ⋙ ProEtale.upperStar (ModuleCat.{u + 1} (coefficient T)) g :=
  upperStarFiniteCoefficientModEquivalenceIso g T

variable (N : ℕ) (hN : 0 < N) (hchar : ringChar (coefficient.{u} T) = N)

/-- Reading the root line over the separate coefficient interface. -/
@[no_expose] noncomputable def rootReading (Z : Scheme.{u}) (hZ : IsUnit (N : Γ(Z, ⊤))) :
    (comparison T Z).functor.obj
        ((Mod.freeFunctor (condensedRingObj (ringObj T) Z)).obj (rootsOfUnitySheaf Z N)) ≅
      ν^*(Z)[ModuleCat.{u + 1} (coefficient T)].obj (Etale.tateSheaf (coefficient T) Z) :=
  purityFiniteRootTateReadingIso T N hN hchar Z hZ

@[no_expose] noncomputable def tatePull {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (ProEtale.upperStar (ModuleCat.{u + 1} (coefficient T)) g).obj
        (ν^*(Y)[ModuleCat.{u + 1} (coefficient T)].obj
          (Etale.tateSheaf (coefficient T) Y)) ⟶
      ν^*(X)[ModuleCat.{u + 1} (coefficient T)].obj (Etale.tateSheaf (coefficient T) X) :=
  (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (coefficient T)) g).hom.app
      (Etale.tateSheaf (coefficient T) Y) ≫
    ν^*(X)[ModuleCat.{u + 1} (coefficient T)].map
      (Etale.upperStarTateSheafToTateSheaf (coefficient T) g)

/-- The reading equation, checked before the finite ring is specialized. -/
lemma rootReading_pullback (hT : (N : T) = 0) {X Y : Scheme.{u}} (g : X ⟶ Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))) :
    (comparison T X).functor.map
          ((freeFunctorCompUpperStarIso (ringObj T) g).hom.app (rootsOfUnitySheaf Y N)) ≫
        (comparison T X).functor.map
          ((Mod.freeFunctor (condensedRingObj (ringObj T) X)).map
            (upperStarRootsOfUnitySheafHom g N)) ≫
        (rootReading T N hN hchar X hX).hom =
      (comparePull T g).hom.app
          ((Mod.freeFunctor (condensedRingObj (ringObj T) Y)).obj (rootsOfUnitySheaf Y N)) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} (coefficient T)) g).map
          (rootReading T N hN hchar Y hY).hom ≫
        tatePull T g := by
  have h := purityFiniteRootTateReadingIso_pullback T N hN hchar hT g hY hX
  dsimp only [comparison, comparePull, rootReading, tatePull, ringObj, ringObjMon,
    ringObjComm, coefficient, coefficientRing, Functor.comp_obj, Functor.comp_map] at h ⊢
  exact_mod_proofs h

end K4FiniteCoefficient
end AlgebraicGeometry.ProEtale
