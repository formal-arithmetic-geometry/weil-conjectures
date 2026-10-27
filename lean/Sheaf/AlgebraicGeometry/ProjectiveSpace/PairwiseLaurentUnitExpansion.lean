/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits

/-! # Pairwise Laurent expansions on projective-space overlaps

Source: Stacks Project, divisors.tex, Tag 0BXJ, lemma-Pic-projective-space-UFD.
(blueprint: new-sfb-projective-pairwise-laurent-unit-expansion)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

noncomputable section

variable (k : Type u) [Field k] (r : ℕ)

/-- The structural constant map from the base field to sections on a standard open. -/
def standardOpenConst (i : ULift.{u} (Fin r)) :
    k →+* Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)),
      standardOpen _ (Spec (.of k)) i) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫
    (ℙ(ULift.{u} (Fin r); Spec (.of k)) ↘ Spec (.of k)).appTop ≫
    (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map (homOfLE le_top).op).hom

/-- The unit induced by a nonzero constant on a standard chart. -/
def standardOpenConstUnit (i : ULift.{u} (Fin r)) (c : kˣ) :
    Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)),
      standardOpen _ (Spec (.of k)) i)ˣ :=
  Units.map (standardOpenConst k r i).toMonoidHom c

/-- Every unit on a distinct standard overlap has one Laurent exponent and a scalar
coefficient.  This is the pairwise Laurent-polynomial calculation used by the
normalization theorem.

Source: Stacks Project, divisors.tex, Tag 0BXJ, the double-overlap calculation.
(blueprint: new-sfb-projective-pairwise-laurent-unit-expansion)

Proof: identify the double-overlap section ring with a polynomial ring in the
remaining affine coordinates and one invertible ratio.  Degree comparison in the
remaining variables forces a unit to have degree zero there.  The extremal
Laurent exponents add under multiplication, so a unit has exactly one exponent;
the coefficient is a nonzero scalar.  The full calculation is intentionally
split from the cocycle comparison, which is the next intermediate theorem.
-/
theorem exists_pairwise_laurent_unit_expansion (k : Type u) [Field k]
    (r : ℕ) (hr : 3 ≤ r)
    (t : ∀ i j : ULift.{u} (Fin r),
      Γ(ℙ(ULift.{u} (Fin r); Spec (.of k)),
        standardOpen _ (Spec (.of k)) i ⊓ standardOpen _ (Spec (.of k)) j)ˣ) :
    ∃ e : ∀ i j : ULift.{u} (Fin r), ℤ,
      ∃ c : ∀ i j : ULift.{u} (Fin r), kˣ,
        ∀ i j : ULift.{u} (Fin r), i ≠ j →
          (t i j).val =
            (ℙ(ULift.{u} (Fin r); Spec (.of k))).presheaf.map
              (homOfLE inf_le_left).op (standardOpenConstUnit k r i (c i j)).val *
              (transitionUnit _ (Spec (.of k)) (e i j) i j).val := by
  sorry

end

end AlgebraicGeometry.ProjectiveSpace
