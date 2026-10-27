/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CondensedTateIntegralTowerData
public import Sheaf.Paper.TateTensorGeneratorCompatibility
import Sheaf.Paper.TateTensorGeneratorZero
import Sheaf.Paper.TateTensorGeneratorOne
import Sheaf.Paper.TateTensorGeneratorStep

/-! Fixed-level root-generator comparison for the integral Tate tensor.

Source: smooth-purity transport, normalized Tate tower, Step 1.
(blueprint: lem-pur-tate-tensor-generator-map)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- A morphism inducing the quotient projection on all compatible root generators.
No invertibility is asserted here.

Source: current blueprint, sec-smooth-purity/sk-thm-purity-transport, Step 2,
ordinary quotient comparison of the integral root tensor.
(blueprint: lem-pur-tate-tensor-generator-map)

Proof: on the compatible primitive-root covering, identify the inverse-limit root
module with the completed coefficient unit by compatible scalar coordinates.
Project these coordinates to the finite coefficient ring and tensor the root
projections in the prescribed order. For degree zero use coefficient multiplication.
The projection formula is balanced in every coefficient, hence defines a morphism
on the sheafified tensor. Changing a primitive root changes both coordinates by
the same unit, so these local morphisms agree on overlaps and glue. Restriction
commutes with the root projections, giving the displayed formula for every lift.
On the empty scheme the unique morphism has the same formula. -/
theorem tateTensorQuotient_generator_map
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ) :
    ∃ f : (realization T ell n).obj (finiteSheaf T ell n d) ⟶ quotientLine T ell n d,
      GeneratorCompatible T ell n d f := by
  have h1 := tateTensorQuotient_generator_one T ell hT n
  induction d with
  | zero => exact tateTensorQuotient_generator_zero T ell n
  | succ d ih =>
    cases d with
    | zero => exact h1
    | succ d =>
      obtain ⟨f, hf⟩ := ih
      obtain ⟨g, hg⟩ := h1
      exact tateTensorQuotient_generator_step T ell n d f g hf hg

end AlgebraicGeometry.Scheme.PurityIntegralTower
