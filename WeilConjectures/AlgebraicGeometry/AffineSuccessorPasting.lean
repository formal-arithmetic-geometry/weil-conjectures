/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction

/-! # Successor counit pasting for ordered adjunction towers
Source: Mathlib adjunction composition, used in general-ring smooth purity,
proof (3), ordered affine induction.
(blueprint: lem-sp-affine-successor-pasting).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- Successor counit pasting for two ordered towers with a prescribed transition.
Source: general-ring smooth purity, proof (3), ordered affine induction, and the
component formula for the counit of a composite adjunction.
(blueprint: lem-sp-affine-successor-pasting).

Proof: expand both successor counits. Functoriality moves the last-coordinate square
inside the preceding left functor. Split the mapped composite and then use the
preceding counit square. Associativity gives the desired successor square. -/
theorem affine_successor_pasting {C : ℕ → Type*} [∀ n, Category (C n)]
    {L : ∀ n, C (n + 1) ⥤ C n} {R : ∀ n, C n ⥤ C (n + 1)}
    {R' : ∀ n, C n ⥤ C (n + 1)}
    (a : ∀ n, L n ⊣ R n) (a' : ∀ n, L n ⊣ R' n)
    (d : ℕ) (K : C 0)
    (eD : (affineTraceRightTower R d).obj K ⟶
      (affineTraceRightTower R' d).obj K)
    (eSucc : (affineTraceRightTower R (d + 1)).obj K ⟶
      (affineTraceRightTower R' (d + 1)).obj K)
    (hline : (L d).map eSucc ≫
        (a' d).counit.app ((affineTraceRightTower R' d).obj K) =
      (a d).counit.app ((affineTraceRightTower R d).obj K) ≫ eD)
    (ih : (affineTraceLeftTower L d).map eD ≫
        (affineTraceAdjunctionTower a' d).counit.app K =
      (affineTraceAdjunctionTower a d).counit.app K) :
    (affineTraceLeftTower L (d + 1)).map eSucc ≫
        (affineTraceAdjunctionTower a' (d + 1)).counit.app K =
      (affineTraceAdjunctionTower a (d + 1)).counit.app K := by
  rw [affineTraceAdjunctionTower_counit_succ,
    affineTraceAdjunctionTower_counit_succ]
  change (affineTraceLeftTower L d).map ((L d).map eSucc) ≫
      (affineTraceLeftTower L d).map
        ((a' d).counit.app ((affineTraceRightTower R' d).obj K)) ≫
      (affineTraceAdjunctionTower a' d).counit.app K = _
  have h := congrArg (fun z ↦ (affineTraceLeftTower L d).map z) hline
  calc
    _ = (affineTraceLeftTower L d).map
          ((L d).map eSucc ≫
            (a' d).counit.app ((affineTraceRightTower R' d).obj K)) ≫
          (affineTraceAdjunctionTower a' d).counit.app K := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (affineTraceLeftTower L d).map
          ((a d).counit.app ((affineTraceRightTower R d).obj K) ≫ eD) ≫
          (affineTraceAdjunctionTower a' d).counit.app K := by rw [h]
    _ = (affineTraceLeftTower L d).map
          ((a d).counit.app ((affineTraceRightTower R d).obj K)) ≫
          (affineTraceLeftTower L d).map eD ≫
          (affineTraceAdjunctionTower a' d).counit.app K := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by rw [ih]

end AlgebraicGeometry.Etale
