/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

import Sheaf.CategoryTheory.WeakTriangulatedGenerator
import Sheaf.CategoryTheory.CompactGeneratorsBuildObjects
import Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact
import Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators

/-!
# Finite-Tor constructible objects generate the ordinary étale derived category

Source: blueprint main-20261015, `sec-six-functors-basics`,
`sk-prop-ctf-finite-comparison/sk-prop-ctf-finite-comparison-whole.md` and its proof;
Stacks Project, Derived Categories, Tag 09SN (blueprint: det-ctf-finite-comparison-whole).

The localizing hull is the defining intersection of full replete triangulated
subcategories closed under ambient coproducts indexed in the fixed universe `u + 1`.
The ambient category is the ordinary unbounded derived category of module sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Bounded constructible complexes of finite Tor amplitude generate the entire ordinary
unbounded étale derived category over a finite admissible ring. The intersection is over
full replete triangulated subcategories containing these complexes and closed under all
small ambient coproducts, including the empty coproduct.

Source: blueprint main-20261015, `sk-prop-ctf-finite-comparison-whole.md`, and its proof,
Compactness, Detection and Generation; Stacks Project, Tag 09SN
(blueprint: det-ctf-finite-comparison-whole).

Proof:
1. Apply `lem-pur-etale-finite-ring-compact-generators` with `T = X` and `C = A`.
   The field `D.k` is algebraically closed, and the prime ℓ is invertible because it
   differs from `D.p`. Finite type and the finite ℓ-primary coefficient hypothesis
   give a small family `E_s` of bounded constructible finite-Tor objects detecting
   isomorphisms, ambient coproducts, and locally small Hom spaces. Apply
   `det-ctf-finite-compact-etale` to make every `E_s` compact.
2. If all maps from all shifts of `E_s` to `K` vanish, detection applied to `0 → K`
   makes `K` zero. For nonzero `K`, a nonzero map from a shifted generator becomes
   a nonzero map from `E_s` into a shift of `K`. Extend it by zero on the other
   summands of the coproduct of the `E_s`. Its restriction to summand `s` remains
   nonzero, so this coproduct is a weak generator, as in `def-pc-generators`.
3. Apply `lem-pc-compact-generators-build-objects` to an arbitrary unbounded `K`.
   It gives a sequence `X_n` with `X_0` and the successive triangle objects `Z_n`
   coproducts of shifts of `E_s`, distinguished triangles
   `Z_n → X_n → X_(n+1) → Z_n[1]`, and a telescope triangle
   `P → P → K → P[1]`, where `P` is the coproduct of the `X_n` and its first arrow
   is identity minus shift.
4. Every full replete triangulated coproduct-closed subcategory containing the
   finite-Tor constructible objects contains all `E_s`, their shifts, `X_0`, and
   all `Z_n`. Rotate the successive triangles and use the middle-object condition
   of `def-weil-triangulated-subcategory` inductively to put all `X_n` in it.
   Coproduct and shift closure put `P` and `P[1]` in it. The rotated telescope
   triangle `P → K → P[1] → P[1]` then puts `K` in it. Since `K` was arbitrary,
   their intersection is the full object property. -/
theorem finiteTorConstructible_etale_localizing_eq_top
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) (hℓprime : Nat.Prime ℓ) (hℓne : ℓ ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ℓ : A) ^ r = 0) :
    sInf {P : ObjectProperty (DerivedCategoryModule A X) |
      (∀ K : DerivedCategoryModule A X,
        DerivedCategory.isBoundedConstructible A X K →
        (∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A X a b K) → P K) ∧
      P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated ∧
      ∀ I : Type (u + 1), Nonempty (P.IsClosedUnderColimitsOfShape (Discrete I))} =
        (⊤ : ObjectProperty (DerivedCategoryModule A X)) := by
  sorry

end AlgebraicGeometry.Etale
