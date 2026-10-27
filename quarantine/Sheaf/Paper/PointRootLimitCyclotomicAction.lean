/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.Paper.PointSignedCyclotomicActionData

/-! # Cyclotomic action on the completed root tower

Source: Deligne, Weil I (2.2), pp. 280--281.
(blueprint: lem-pur-point-root-limit-cyclotomic-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointSignedCyclotomicAction

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Restriction followed by the specified root-tower comparison is the inverse
cardinality scalar on every compatible root section.

Source: Deligne, Weil I (2.2), pp. 280--281; Weil II (1.1.7), pp. 150--151
(blueprint: lem-pur-point-root-limit-cyclotomic-action).

Proof: Compose both sides with each projection of the root tower. The defining
limit.post and lim.map equations identify the left projection with the finite
root comparison applied after the inverse-image unit and restriction. The adjunct
projection formula for roots and the pullback projection identity identify it
with geometric field Frobenius on that root. The Frobenius-root-power theorem
identifies this coordinatewise action on the ordinary cyclotomic Tate module
with multiplication by the inverse unit q. The sheaf's completed coefficient
action is defined by these same finite Z/l^(r+1) actions, and the map from the
constant p-adic integers to the completed coefficients is defined by their
residues. Thus the right projection is precisely the same root. Evaluation of
sheaf limits preserves limits, so their projections are jointly injective. -/
theorem root_limit_cyclotomic_action (hl : l ≠ D.p)
    (e : (purTwistZlOne (point D) l).obj.obj (op (finalObject D))) :
    rootLimitAction D l e =
      @SMul.smul _ _ (purTwistZlAction (point D) l (op (finalObject D))).toSMul
        ((purTwistZlCompletionMap (point D) l).hom.app (op (finalObject D))
          (((toSheafify (ProEt.topology (point D))
            ((Functor.const (point D).ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{u + 1} (PadicInt l))))).app (op (finalObject D)))
                (ULift.up (Ring.inverse (D.q : ℤ_[l])))))
        e := by sorry

end WeilConjectures.PointSignedCyclotomicAction
