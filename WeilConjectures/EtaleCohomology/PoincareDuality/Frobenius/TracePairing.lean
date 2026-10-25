/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Shift.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing

/-!
# Perfectness of the pairing of a trace

Let `a : X ⟶ Y` admit a compactification and `t : (Ra_! Λ_X)[n] ⟶ Λ_Y` be a trace which is a
counit: every morphism `(Ra_! U)[n] ⟶ Λ_Y` is `(Ra_! z)[n] ≫ t` for a unique `z : U ⟶ Λ_X`.
Then the pairing of `t`,
`Ra_! K ⊗ᴸ (Ra_* K^∨)[n] ⟶ Λ_Y`
(`AlgebraicGeometry.Etale.poincarePairingOfTrace`), is perfect for every `K` at which the
projection formula holds. This is the argument of
`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isDetecting`, for the untwisted
evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X`, which is a counit for every `K`.

## Main statements

- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairingOfTrace`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

namespace Etale

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a]

omit [ConcreteCategory (ModuleCat.{u + 1} Λ) FA] [HasSmallSiteSheafify (ModuleCat.{u + 1} Λ)]
    [Etale.UpperStarPreservesFlat (ModuleCat.{u + 1} Λ)]
  [(CategoryTheory.forget (ModuleCat.{u + 1} Λ)).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget (ModuleCat.{u + 1} Λ))]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u + 1}
      Λ))]
  [HasCompactification a] in
/-- The evaluation part of the pairing of a trace: maps `h : N ⟶ Ra_* K^∨` correspond
bijectively to maps `K ⊗ᴸ La^* N ⟶ Λ_X`, through `K ⊗ᴸ La^* h`, `K ⊗ᴸ` the counit of
`La^* ⊣ Ra_*` and the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X`. -/
theorem bijective_derivedTensor_map_comp_counit_comp_coefficientEvaluation (K : 𝐃(X, (ModuleCat.{u +
    1} Λ)))
    (N : 𝐃(Y, (ModuleCat.{u + 1} Λ))) :
    Function.Bijective (fun h : N ⟶ (R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K)) ↦
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map ((L((a)^*[ModuleCat.{u + 1} Λ])).map h) ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map ((derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} Λ) a).counit.app _) ≫
          DerivedCategory.coefficientEvaluation K) := by
  have e : (fun h : N ⟶ (R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K)) ↦
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map ((L((a)^*[ModuleCat.{u + 1} Λ])).map h) ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map ((derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} Λ) a).counit.app _) ≫
          DerivedCategory.coefficientEvaluation K) =
      ((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) K).homEquiv _ _).symm ∘
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).homEquiv _ _).symm := by
    funext h
    simp [Adjunction.homEquiv_counit, DerivedCategory.coefficientEvaluation]
    rfl
  rw [e]
  exact (Equiv.bijective _).comp (Equiv.bijective _)

set_option maxRecDepth 4000 in
omit in
omit [HasSmallSiteSheafify (ModuleCat.{u + 1} Λ)] in
/-- **The pairing of a trace which is a counit is perfect** (form with the trace read on
`Ra_!(Λ_X[n])`). -/
theorem isPerfectPairing_poincarePairingOfTrace_aux (K : 𝐃(X, (ModuleCat.{u + 1} Λ))) (n : ℤ)
    (t : (R(a)_![ModuleCat.{u + 1} Λ]).obj ((𝟙_ _)⟦n⟧) ⟶ 𝟙_ _)
    (ht : ∀ U : 𝐃(X, (ModuleCat.{u + 1} Λ)), Function.Bijective (fun z : U ⟶ 𝟙_ _ ↦
        (R(a)_![ModuleCat.{u + 1} Λ]).map (z⟦n⟧') ≫ t))
    (hPF : ∀ N, HasProjectionFormula (ModuleCat.{u + 1} Λ) a K N) :
    IsPerfectPairing (poincarePairingOfTrace a K n
      (((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso n).inv.app _ ≫ t)) := by
  constructor
  rw [poincarePairingOfTrace, mixedSupportCupProduct, Category.assoc]
  refine MonoidalClosed.isIso_curry_of_projection _ _ _ _ _ _ _ _ _ (fun _ ↦ True)
    (fun _ _ u hu ↦ isIso_of_bijective_comp_shift n u fun N ↦ hu N trivial) (fun N _ ↦ hPF N)
    ?_ ?_
  · exact bijective_derivedTensor_map_comp_counit_comp_coefficientEvaluation Λ a K
  · exact ht

end Etale

end AlgebraicGeometry
