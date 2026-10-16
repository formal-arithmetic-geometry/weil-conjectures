/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import Sheaf.FieldTheory.CommonExtensionFields
import WeilConjectures.FieldTheory.SeparableExtension
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.RingTheory.NormalAlgebraSeparableScalarExtension
import Sheaf.RingTheory.NormalRingFieldExtensionDescent

/-!
# Testing geometric normality over a perfect purely inseparable extension

Source: Stacks Project, Varieties, Tag 038O, equivalence (2) and (6), and Algebra,
Tag 046W, uniqueness of the perfect closure
(blueprint: lem-weil-pbc-normality-perfect-closure-test).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A scheme becomes normal over a perfect purely inseparable extension exactly when it
becomes normal over every field extension. Normality means that every stalk is an
integrally closed domain; the scheme need not be integral or nonempty.

Source: Stacks Project, Varieties, Tag 038O, (2) iff (6), and Algebra, Tag 046W.
(blueprint: lem-weil-pbc-normality-perfect-closure-test).

Proof:
1. Normality over every extension specializes to the given extension K/k.
2. Conversely, for L/k choose a common overfield M of K and L using
   lem-weil-common-extension-fields. Every finitely generated subextension of M/K admits
   a separating transcendence basis by lem-weil-pbc-perfect-field-separating-basis.
   Thus M/K is separable in the sense of def-weil-pbc-separable-field-extension.
3. Cover T by affine opens Spec A. Their base changes are Spec (A tensor H), and their
   stalks agree with those in T_H. The spectrum-stalk localization identification
   lem-weil-pbc-spec-domain-stalks-function-field makes A tensor K normal.
4. Apply lem-weil-pbc-normal-algebra-separable-scalar-extension to M/K. The balancing
   relations give inverse ring maps (a tensor c) tensor m maps to a tensor (cm), and
   a tensor m maps to (a tensor 1) tensor m. Hence A tensor M is normal.
5. The same associativity maps identify (A tensor L) tensor M with A tensor M.
   Apply lem-weil-pbc-normal-ring-field-extension-descent along M/L to make A tensor L
   normal. Ring isomorphisms preserve primes, localizations and integral equations.
6. The spectrum-stalk identification makes every stalk of each base-changed affine open
   an integrally closed domain. These opens cover T_L, so every stalk of T_L is normal.
   For the empty scheme both universal stalk conditions are vacuous. -/
theorem normal_stalks_perfectClosure_iff
    (k K : Type u) [Field k] [Field K] [Algebra k K] [PerfectField K]
    (hpower : ∀ a : K, ∃ n : ℕ, ∃ b : k, algebraMap k K b = a ^ (ringExpChar k ^ n))
    (T : Scheme.{u}) (f : T ⟶ Spec (CommRingCat.of k)) :
    (∀ x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}),
      IsDomain ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x) ∧
      IsIntegrallyClosed
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk x)) ↔
    ∀ (L : Type u) [Field L] [Algebra k L],
      ∀ x : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Scheme.{u}),
        IsDomain ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x) ∧
        IsIntegrallyClosed
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x) := by
  sorry

end AlgebraicGeometry
