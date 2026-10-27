/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.Paper.TowerChernPullbackData

/-! # Integral inverse image with its Kummer and flat-complex realizations

Source: blueprint classes proof (2), integral coefficient stage.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Construct inverse image at the integral quotient stage, independently of any
ordinary or derived extension to the coefficient ring A. The middle Kummer map
is the pullback of full units, as is the last map required by the data record.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
integral reduction; Stacks `sites-cohomology`, lemma-pullback-K-flat, and
`sites-modules`, lemma-pullback-flat.
(blueprint: lem-sp-tower-integral-coefficient-pullback-existence).

Proof: realize abelian towers as sheaves on the vertical sequence site. Pull back
module sheaves with their actions by the exact geometric inverse image. The
constant-sheaf comparison for Z/ell^(n+1) is an isomorphism; its naturality in ring
maps identifies the quotient transitions. Transport the module actions along it.
Use ordinaryInverseSystem_exists on these finite inverse images to assemble
the exact whole-system functor, with its component and transition equations.
The section identities of Forget identify the underlying abelian component
comparisons, and their transition equations give the whole forgetful square.
Multiplication identifies its coefficient unit with the coefficient
unit on X. The integer generator maps to the integer generator because the
constant comparison preserves one, giving unit_normalization. Pull back the
Kummer sequence, using unitsPull for both full-units components. Restriction of
roots is its kernel map, and is invertible because roots of unity are cartesian
when ell is invertible. Transport it through rootForget on each side. Integer
multiplication commutes with restriction, so the root map is R-linear. All these
maps commute with the ell-power and quotient transitions. They give d and both
Kummer normalizations, including the displayed middle-component equation.
On the same sequence sites this is precisely pullback for the ringed-topos map
with the above constant-ring comparison. Pullback preserves flat sheaves by
lemma-pullback-flat and preserves flat-term K-flat complexes by
lemma-pullback-K-flat. Transport these properties through the identification of
module categories to obtain the displayed resolving property. The construction
uses actual inverse image, not a selected arbitrary module structure; it also
works on empty charts and for the positive level indexed by zero. -/
theorem integralCoefficientPullback_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsUnit (l : Γ(X, ⊤))) (hY : IsUnit (l : Γ(Y, ⊤)))
    (cY : Chern l E Y) (cX : Chern l E X) :
    ∃ d : IntegralCoefficientPullback l E f cY cX,
      (∀ n : ℕ, d.kummer.τ₂.app (Opposite.op n) =
        (unitsPull f).app (Opposite.op n)) ∧
      (∀ (P : CochainComplex (Systems Y (Rrings l Y)) ℤ),
          CochainComplex.IsKFlatIndependentCoefficients
            (R := WeilConjectures.SemilinearSections.systemRing
              (Scheme.ProEt.topology Y) (fun n ↦ (Rrings l Y).obj (Opposite.op n))
                (fun n ↦ (Rrings l Y).map (homOfLE (Nat.le_succ n)).op)) P →
          (∀ i : ℤ, SheafOfModules.IsFlatOnSite
            (J := WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology Y))
            (R := WeilConjectures.SemilinearSections.systemRing
              (Scheme.ProEt.topology Y) (fun n ↦ (Rrings l Y).obj (Opposite.op n))
                (fun n ↦ (Rrings l Y).map (homOfLE (Nat.le_succ n)).op)) (P.X i)) →
          CochainComplex.IsKFlatIndependentCoefficients
            (R := WeilConjectures.SemilinearSections.systemRing
              (Scheme.ProEt.topology X) (fun n ↦ (Rrings l X).obj (Opposite.op n))
                (fun n ↦ (Rrings l X).map (homOfLE (Nat.le_succ n)).op))
            ((d.pull.mapHomologicalComplex (.up ℤ)).obj P)) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses
