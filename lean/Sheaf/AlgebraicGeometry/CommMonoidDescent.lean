/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# Descent of the commutative monoid operations

Source: blueprint lem-pd-group-scheme-descent, multiplication and unit step;
Stacks Project, Descent, Tag 02W0.
(blueprint: lem-pd-comm-monoid-operations-descent).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

/-- Multiplication and the unit descend to a commutative monoid structure, before the
inverse is descended. Source: blueprint lem-pd-group-scheme-descent, multiplication and
unit step; Stacks Project, Tag 02W0.
(blueprint: lem-pd-comm-monoid-operations-descent).

Proof: The product of two base-change squares is the base-change square for the
product over the base. Give V times_X V the componentwise transport. The compatibility
of multiplication is exactly hμ, and the unit datum on X has its unique transport.
Compatibility of the unit is hη. Full faithfulness of fpqc base change (02W0) descends
multiplication and unit uniquely to V₀ times_Y V₀ and Y. Their defining factorization
equations give the two point identities below. Base change commutes with products and
terminal objects. Pulling back each monoid axiom gives the corresponding axiom of V;
faithfulness therefore proves associativity and both unit laws downstairs. The same
argument applied to the factor-swap proves commutativity. No inverse is used in this
construction. Empty schemes introduce no exception, since the unit still supplies the
required map from the base. -/
theorem exists_commMonObj_of_effective_projection
    {X Y : Scheme.{u}} {p : X ⟶ Y} [Flat p] [Surjective p] [QuasiCompact p]
    {V : Over X} [MonObj V] [IsCommMonObj V] (D : Over.DescentDatum p V)
    {V₀ : Over Y} (qV : V.left ⟶ V₀.left) (hqV : IsPullback qV V.hom V₀.hom p)
    (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
      (a : Over.mk f₁ ⟶ V), (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)
    (hμ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
      (a b : Over.mk f₁ ⟶ V), D.transport f₁ f₂ h (lift a b ≫ μ[V]) =
        lift (D.transport f₁ f₂ h a) (D.transport f₁ f₂ h b) ≫ μ[V])
    (hη : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p),
      D.transport f₁ f₂ h (toUnit _ ≫ η[V]) = toUnit _ ≫ η[V]) :
    ∃ M : MonObj V₀, letI := M;
      IsCommMonObj V₀ ∧
      (∀ {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V),
        (lift a b ≫ μ[V]).left ≫ qV =
          (lift (Over.homMk (a.left ≫ qV) (by
            simp only [Over.mk_hom, Category.assoc, hqV.w]
            rw [← Category.assoc, Over.w a]
            rfl) : Over.mk (f ≫ p) ⟶ V₀)
            (Over.homMk (b.left ≫ qV) (by
            simp only [Over.mk_hom, Category.assoc, hqV.w]
            rw [← Category.assoc, Over.w b]
            rfl) : Over.mk (f ≫ p) ⟶ V₀) ≫ μ[V₀]).left) ∧
      (∀ {T : Scheme.{u}} (f : T ⟶ X),
        (toUnit (Over.mk f) ≫ η[V]).left ≫ qV =
          (toUnit (Over.mk (f ≫ p)) ≫ η[V₀]).left) := by
  sorry

end CategoryTheory.Over.DescentDatum
