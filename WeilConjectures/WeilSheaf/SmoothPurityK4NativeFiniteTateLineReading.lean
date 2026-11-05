/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeFiniteFreeRootsReading
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf

/-! # Reading the finite Tate line with its canonical geometric datum -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.K4Native

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (n : ℕ) (N : ℕ) (hN : 0 < N)
  (hchar : ringChar (integersModPowCoeff.{u} ℓ E n) = N)

/-- The free root line, read as the usual étale Tate sheaf. -/
noncomputable def purityFiniteRootTateReadingIso
    (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) :
    (finiteCoefficientModEquivalence ℓ E n X).functor.obj
        ((Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)).obj
          (rootsOfUnitySheaf X N)) ≅
      ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].obj
        (Etale.tateSheaf (integersModPowCoeff.{u} ℓ E n) X) :=
  finiteCoefficientModEquivalenceFreeRootsOfUnityIso ℓ E n N hN X hX ≪≫
    ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].mapIso
      ((Etale.extendScalars _ X).mapIso
        (eqToIso (congrArg (X.rootsOfUnitySheaf) hchar.symm)))

/-- The reading carries the actual free-root pullback to the usual étale Tate
pullback, including the change from the root exponent to the coefficient characteristic. -/
lemma purityFiniteRootTateReadingIso_pullback
    (hT : (N : (PadicAlgCl.integersModPow ℓ E n)) = 0) {X Y : Scheme.{u}} (g : X ⟶ Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))) :
    (finiteCoefficientModEquivalence ℓ E n X).functor.map
          ((CondensedRing.freeFunctorCompUpperStarIso
            (Profinite.integersModPowRingObj ℓ E n) g).hom.app (rootsOfUnitySheaf Y N)) ≫
        (finiteCoefficientModEquivalence ℓ E n X).functor.map
          ((Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X)).map
            (upperStarRootsOfUnitySheafHom g N)) ≫
        (purityFiniteRootTateReadingIso ℓ E n N hN hchar X hX).hom =
      (upperStarFiniteCoefficientModEquivalenceIso ℓ E n g).hom.app
          ((Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) Y)).obj
            (rootsOfUnitySheaf Y N)) ≫
        (g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          (purityFiniteRootTateReadingIso ℓ E n N hN hchar Y hY).hom ≫
        (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g).hom.app
          (Etale.tateSheaf (integersModPowCoeff.{u} ℓ E n) Y) ≫
        ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          (Etale.upperStarTateSheafToTateSheaf (integersModPowCoeff.{u} ℓ E n) g) := by
  subst N
  simpa only [purityFiniteRootTateReadingIso, eqToIso_refl, Functor.mapIso_refl,
    Iso.trans_refl, Etale.tateSheaf, Etale.upperStarTateSheafToTateSheaf] using
    purity_finiteCoefficientModEquivalenceFreeRootsOfUnityIso_pullback
      ℓ E n (ringChar (integersModPowCoeff.{u} ℓ E n)) hN hT g hY hX

end AlgebraicGeometry.ProEtale.K4Native
