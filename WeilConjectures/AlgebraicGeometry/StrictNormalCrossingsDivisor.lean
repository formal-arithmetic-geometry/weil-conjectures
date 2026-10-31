/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Strict normal crossings divisors over a field

Source: ILO, Travaux de Gabber, Expose X, p. 149, definition following Theorem 2.1;
Expose VI, 1.4--1.5 (blueprint: def-trf-strict-normal-crossings-divisor).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A reduced effective Cartier divisor with finitely many smooth integral components and
smooth scheme-theoretic intersections of the expected codimension. The sum of component
ideals defines their scheme-theoretic intersection. Codimension is measured by the difference
of local-ring dimensions at corresponding points. The empty family represents the empty
divisor. On a smooth finite-type scheme over a field these conditions say exactly that the
components are the irreducible components and meet with strict normal crossings.
Source: ILO, Expose X, p. 149, following Theorem 2.1; Expose VI, 1.4--1.5
(blueprint: def-trf-strict-normal-crossings-divisor). -/
def IsStrictNormalCrossingsDivisor {F : Type u} [Field F] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of F)) (D : X.IdealSheafData) : Prop :=
  D.IsInvertible ∧ D.radical = D ∧
    ∃ (n : ℕ) (C : Fin n → X.IdealSheafData),
      Function.Injective (fun i ↦ (C i).support) ∧
      (∀ i, IsIntegral (C i).subscheme) ∧
      (∀ x : X, x ∈ D.support ↔ ∃ i, x ∈ (C i).support) ∧
      ∀ s : Finset (Fin n),
        Smooth ((⨆ i ∈ s, C i).subschemeι ≫ p) ∧
        ∀ z : (⨆ i ∈ s, C i).subscheme,
          ringKrullDim (X.presheaf.stalk ((⨆ i ∈ s, C i).subschemeι z)) =
            ringKrullDim ((⨆ i ∈ s, C i).subscheme.presheaf.stalk z) + (s.card : ℕ)

end AlgebraicGeometry.Scheme.IdealSheafData
