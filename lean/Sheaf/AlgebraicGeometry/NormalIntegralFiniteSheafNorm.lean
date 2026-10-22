/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Norm.Transitivity
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC

/-! # Norms for finite integral covers of normal integral schemes

Source: Stacks Project, Divisors, Tag 0BD3 (lemma-norm-in-normal-case),
with the norm conditions of Section 0BCX (section-norms)
(blueprint: lem-sfb-normal-integral-finite-sheaf-norm).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite surjective morphism of integral schemes onto a scheme with integrally closed
local domains admits a multiplicative sheaf norm of positive degree. Its value on a pulled-back
section is the degree-th power, and vanishing at a point implies vanishing of the norm at its
image, with values taken in residue fields.

Source: Stacks Project, Divisors, Tag 0BD3 (lemma-norm-in-normal-case),
Section 0BCX (section-norms), conditions (1) and (2)
(blueprint: lem-sfb-normal-integral-finite-sheaf-norm).

Proof:
1. Over a nonempty affine open `Spec B`, its inverse image is `Spec A` with `A` finite over
   `B`. Surjectivity makes `B → A` injective. The fraction fields give a finite extension
   by `lem-trf-finite-domain-fraction-degree`; their identifications with the generic stalks
   by `lem-sc-integral-function-field-affine-fraction` show that its positive degree `d`
   is independent of the affine open. Naturality uses
   `lem-weil-pbc-spec-map-residue-field-naturality`.
2. Normality of each stalk and `lem-sc-integral-scheme-stalks-in-function-field` put any
   integral element of the function field in every stalk. Then
   `lem-sc-function-field-sections-glue` puts it in `B`, so `B` is integrally closed.
3. Every element of `A` is integral over `B` by `lem-weil-pbc-finite-algebra-is-integral`.
   Apply `lem-sfb-integral-minpoly-fraction-descent` and the signed constant-term formula
   `lem-sfb-finite-field-norm-minpoly` to see that the field norm lies in `B`.
   Injectivity into the fraction field gives multiplicativity, preservation of one,
   and the scalar formula `a ↦ a ^ d`.
4. On nested nonempty affine opens both norms have the same generic germ, so they agree
   by `lem-sc-integral-scheme-stalks-in-function-field`. Cover intersections by affine opens
   to obtain agreement on arbitrary overlaps; intersections need not themselves be affine.
5. Glue the affine norms using the structure sheaf axiom. Uniqueness gives restriction
   compatibility and the multiplicative and scalar identities on every open. On the empty
   open use the unique map between the one-element section rings.
6. If a section vanishes at a point with prime `q`, its annihilating monic polynomial
   shows that its constant coefficient lies in `q ∩ B`. Its signed positive power is the
   norm, by `lem-sfb-finite-field-norm-minpoly`, and thus vanishes at the image point by
   `lem-weil-pbc-affine-open-section-vanishing-prime` and
   `lem-weil-pbc-spec-map-residue-field-naturality`. Restriction proves this on every open.
-/
theorem exists_normalIntegralFiniteSheafNorm
    {Y Z : Scheme.{u}} (p : Y ⟶ Z) [IsFinite p] [Surjective p]
    [IsIntegral Y] [IsIntegral Z]
    (hZ : ∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
      IsIntegrallyClosed (Z.presheaf.stalk z)) :
    ∃ d : ℕ, 1 ≤ d ∧
      ∃ ν : ∀ V : Z.Opens, Γ(Y, p ⁻¹ᵁ V) →* Γ(Z, V),
        (∀ (V W : Z.Opens) (h : W ≤ V) (b : Γ(Y, p ⁻¹ᵁ V)),
          ν W (Y.presheaf.map (homOfLE (p.preimage_mono h)).op b) =
            Z.presheaf.map (homOfLE h).op (ν V b)) ∧
        (∀ (V : Z.Opens) (a : Γ(Z, V)), ν V (p.app V a) = a ^ d) ∧
        (∀ (V : Z.Opens) (b : Γ(Y, p ⁻¹ᵁ V)) (y : Y) (hy : y ∈ p ⁻¹ᵁ V),
          Y.evaluation (p ⁻¹ᵁ V) y hy b = 0 →
            Z.evaluation V (p y) hy (ν V b) = 0) := by
  sorry

end AlgebraicGeometry
