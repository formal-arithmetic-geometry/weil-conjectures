/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.FreeRootsReading
public import WeilConjectures.WeilSheaf.SmoothPurityFiniteTateLineReading

/-! # Independent coefficient/pullback infrastructure: TateReading -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] (N : ℕ) (hN : 0 < N)
  (hchar : ringChar (coeffType.{u} T) = N)

/-- The free root line, read as the usual étale Tate sheaf. -/
noncomputable def purityFiniteRootTateReadingIso
    (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) :
    (finiteCoefficientModEquivalence X T).functor.obj
        ((Mod.freeFunctor (condensedRingObj (coeffRing T) X)).obj
          (rootsOfUnitySheaf X N)) ≅
      ν^*(X)[ModuleCat.{u + 1} (coeffType.{u} T)].obj
        (Etale.tateSheaf (coeffType.{u} T) X) :=
  finiteCoefficientModEquivalenceFreeRootsOfUnityIso X N T hN hX ≪≫
    ν^*(X)[ModuleCat.{u + 1} (coeffType.{u} T)].mapIso
      ((Etale.extendScalars _ X).mapIso
        (eqToIso (congrArg (X.rootsOfUnitySheaf) hchar.symm)))

/-- The reading carries the actual free-root pullback to the usual étale Tate
pullback, including the change from the root exponent to the coefficient characteristic. -/
lemma purityFiniteRootTateReadingIso_pullback
    (hT : (N : T) = 0) {X Y : Scheme.{u}} (g : X ⟶ Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))) :
    (finiteCoefficientModEquivalence X T).functor.map
          ((Strategy3.freeFunctorCompUpperStarIso
            (coeffRing T) g).hom.app (rootsOfUnitySheaf Y N)) ≫
        (finiteCoefficientModEquivalence X T).functor.map
          ((Mod.freeFunctor (condensedRingObj (coeffRing T) X)).map
            (upperStarRootsOfUnitySheafHom g N)) ≫
        (purityFiniteRootTateReadingIso T N hN hchar X hX).hom =
      (upperStarFiniteCoefficientModEquivalenceIso g T).hom.app
          ((Mod.freeFunctor (condensedRingObj (coeffRing T) Y)).obj
            (rootsOfUnitySheaf Y N)) ≫
        (g)^*[ModuleCat.{u + 1} (coeffType.{u} T)].map
          (purityFiniteRootTateReadingIso T N hN hchar Y hY).hom ≫
        (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (coeffType.{u} T)) g).hom.app
          (Etale.tateSheaf (coeffType.{u} T) Y) ≫
        ν^*(X)[ModuleCat.{u + 1} (coeffType.{u} T)].map
          (Etale.upperStarTateSheafToTateSheaf (coeffType.{u} T) g) := by
  subst N
  simpa only [purityFiniteRootTateReadingIso, eqToIso_refl, Functor.mapIso_refl,
    Iso.trans_refl, Etale.tateSheaf, Etale.upperStarTateSheafToTateSheaf] using
    purity_finiteCoefficientModEquivalenceFreeRootsOfUnityIso_pullback
      T (ringChar (coeffType.{u} T)) hN hT g hY hX


end AlgebraicGeometry.ProEtale.Strategy3
