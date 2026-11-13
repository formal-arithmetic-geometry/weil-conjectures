/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps

/-! # The degree-zero finite-twist evaluation as a flat single-object pairing
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Etale

/-- Express the fixed degree-zero evaluation using the flat single-object pairing.
(Stacks, Tag 06YQ.) -/
theorem finiteTwistDegreeZeroEvaluation_pairing
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤)))
    (hL : ObjectProperty.flat (Scheme.finiteEtaleTateLine T N A hA)) :
    p1DecompositionDegreeZeroEvaluation A N hN hA T hT =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N T hA (-1)))).app
        (ordinaryFiniteLine A N hA T) ≫
      singleFunctorFlatPairing
        (Scheme.finiteEtaleTateLine T N A hA)
        (Scheme.finiteEtaleTateSheaf A N T hA (-1))
        (ordinaryFiniteConstant A T)
        hL
        ((ihom.ev (Scheme.finiteEtaleTateLine T N A hA)).app
          (ordinaryFiniteConstant A T)) := by
  delta p1DecompositionDegreeZeroEvaluation p1DecompositionDegreeZeroTensor
    singleFunctorFlatPairing
  delta ordinaryFiniteLine ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor
  rfl

end AlgebraicGeometry.Etale
