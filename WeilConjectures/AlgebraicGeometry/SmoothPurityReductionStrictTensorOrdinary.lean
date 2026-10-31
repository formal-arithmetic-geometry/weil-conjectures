/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionMonoidalData

/-! # Ordinary balancing for normalized reduction

Source: Stacks 03EL and 07A4; blueprint integral direct-image proof (3)
(blueprint: lem-sp-reduction-strict-tensor-balancing-ordinary).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The ordinary comparison family and its two pure-generator normalizations.
Source: Stacks 03EL and 07A4.
(blueprint: lem-sp-reduction-strict-tensor-balancing-ordinary).

Proof plan: realize the normalized ordinary reduction by extension along the
sequence coefficient projection.  The sheaf tensor universal property descends
the maps sending `(x tensor y) tensor a` to `(x tensor 1) tensor (y tensor a)`
and `(x tensor a) tensor (y tensor b)` to `(x tensor y) tensor (a*b)`.
The balanced relations prove the two maps inverse, while multiplicativity and
unit preservation of quotient transitions prove naturality in the sequence
index.  Sheafification then gives the displayed formulas on all local sections.
The construction is independent of the chain-level totalization comparison. -/
theorem sp_reduction_strict_tensor_ordinary_exists
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D) :
    ∃ (ordinary : ∀ M N : spIntegralSectionModules l E T,
      (spMonoidalOrdinary l E T D r).obj
          (ordinaryTensor.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
            (spIntegralSectionRing l E T) M N) ≅
        ordinaryTensor.{u + 1, u, u + 1}
          (coefficientSequenceTopology (Scheme.ProEt.topology T))
          (spMonoidalSystemRing l E T)
          ((spMonoidalOrdinary l E T D r).obj M)
          ((spMonoidalOrdinary l E T D r).obj N)),
      (∀ (M N : spIntegralSectionModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
        (x : M.val.obj U) (y : N.val.obj U)
        (a : ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj U),
        ((ordinary M N).hom.val.app (op (n, U.unop)))
          (spMonoidalGenerator l E T D r _ n U a
            (tensorSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
              (spIntegralSectionRing l E T) M N U x y)) =
          tensorSection.{u + 1, u, u + 1}
            (coefficientSequenceTopology (Scheme.ProEt.topology T))
            (spMonoidalSystemRing l E T) _ _ (op (n, U.unop))
            (spMonoidalGenerator l E T D r M n U 1 x)
            (spMonoidalGenerator l E T D r N n U a y)) ∧
      (∀ {M M' N N' : spIntegralSectionModules l E T}
        (f : M ⟶ M') (g : N ⟶ N'),
        (spMonoidalOrdinary l E T D r).map
            (ordinaryTensorHom.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
              (spIntegralSectionRing l E T) f g) ≫ (ordinary M' N').hom =
          (ordinary M N).hom ≫
            (ordinaryTensorHom.{u + 1, u, u + 1}
              (coefficientSequenceTopology (Scheme.ProEt.topology T))
              (spMonoidalSystemRing l E T)
              ((spMonoidalOrdinary l E T D r).map f)
              ((spMonoidalOrdinary l E T D r).map g))) ∧
      (∀ (M N : spIntegralSectionModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
        (x : M.val.obj U) (y : N.val.obj U)
        (a b : ((spCoefficientCommRings.{u, u} l E T).obj (op n)).obj.obj U),
        ((ordinary M N).inv.val.app (op (n, U.unop)))
          (tensorSection.{u + 1, u, u + 1}
            (coefficientSequenceTopology (Scheme.ProEt.topology T))
            (spMonoidalSystemRing l E T) _ _ (op (n, U.unop))
            (spMonoidalGenerator l E T D r M n U a x)
            (spMonoidalGenerator l E T D r N n U b y)) =
          spMonoidalGenerator l E T D r _ n U (a * b)
            (tensorSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
              (spIntegralSectionRing l E T) M N U x y)) := by
  sorry

end AlgebraicGeometry.ProEtale
