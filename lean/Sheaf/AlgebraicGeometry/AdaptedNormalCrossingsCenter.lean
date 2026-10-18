/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Sheaf.RingTheory.IsRegularSystemOfParameters

/-!
# Centers adapted to a labelled normal-crossings boundary

Source: ILO, Expose X, 1.7 Claim and its coordinate description, printed pp. 144--145
(blueprint: def-per-adapted-normal-crossings-center).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- At each point of the center the boundary components through that point have equations
`z`, and the center has equations the first `m` boundary coordinates followed by additional
parameters `y`. All these germs are distinct members of one regular system of parameters.
The label embedding identifies exactly the components through the point; the other
components have unit ideal on the chosen neighbourhood. The condition is imposed only
on the center and permits the empty center sequence. Source: ILO X 1.7, pp. 144--145
(blueprint: def-per-adapted-normal-crossings-center). -/
def HasAdaptedNormalCrossingsCenter {X : Scheme.{u}} (I : X.IdealSheafData)
    {r : ℕ} (W : Fin r → X.IdealSheafData) : Prop :=
  ∀ x : X, x ∈ I.support →
    ∃ (U : X.affineOpens) (hx : x ∈ U.1) (s m n : ℕ)
      (z : Fin s → Γ(X, U.1)) (y : Fin n → Γ(X, U.1))
      (label : Fin s ↪ Fin r) (hR : IsNoetherianRing (X.presheaf.stalk x))
      (t : List (X.presheaf.stalk x)),
      m ≤ s ∧
      @IsLocalRing.IsRegularSystemOfParameters (X.presheaf.stalk x) _ _ hR t ∧
      (List.map (X.presheaf.germ U.1 x hx).hom
        (List.ofFn z ++ List.ofFn y)).Sublist t ∧
      (∀ j : Fin r, x ∈ (W j).support ↔ j ∈ Set.range label) ∧
      (∀ k : Fin s, (W (label k)).ideal U = Ideal.span {z k}) ∧
      (∀ j : Fin r, j ∉ Set.range label → (W j).ideal U = ⊤) ∧
      I.ideal U = Ideal.ofList ((List.ofFn z).take m ++ List.ofFn y)

end AlgebraicGeometry
