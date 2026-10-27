/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q6
-/
module

public import Sheaf.AlgebraicGeometry.CartierKummerData

/-! # Existence of a simultaneous Cartier Kummer realization

Source: blueprint, final paragraph of lem-amb-cartier-kummer-map.proof.md.
(blueprint: lem-amb-cartier-kummer-realization-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor ChangeOfRings
namespace AlgebraicGeometry.Etale
open Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- A normalized ordinary Cartier Kummer family admits a simultaneous realization.

Source: blueprint latest, sec-six-functors-basics/sk-lem-geo-cartier/
lem-amb-cartier-kummer-map.proof.md, final paragraph; parent descent proof steps
8--11 and the existence part of step 13.
(blueprint: lem-amb-cartier-kummer-realization-existence).

Proof: For each coefficient level choose an annihilating exponent and the unique
root-projection-normalized Tate comparison. Postcompose the constructed canonical
Cartier class with this comparison. Its source mate is invertible, and its
comparison equation identifies its pullback with the supplied ordinary class by
uniqueness of the ordinary supported boundary. The adjunction mate-unit identity,
checked on sheafification generators, identifies the supported quotient
normalization with constant comparison followed by the pro-etale quotient unit.
For r ≤ s construct the root projection by rootsOfUnityPowMap. Its kernel
inclusion equation says its underlying unit value is the l^(s-r) power. Thus the
coherent etale transition from finite Tate descent satisfies the pure root tensor
formula required by geoCartierCanonicalClass_modulus. Apply that theorem and
postcompose with the normalized Tate comparison. Uniqueness of normalized
comparisons identifies the coherent choices with the comparisons chosen above;
associativity of Ext gives equality of the transported classes. Compare two
arbitrary annihilating exponents with their maximum. Hence the class chosen at
each coefficient level realizes every exponent. Choice assembles these into the
required family. This argument applies also to the zero coefficient ring, empty
schemes and empty divisors: all quotient and comparison formulas remain valid.
This statement asserts existence only; uniqueness is proved in the parent. -/
theorem cartier_kummer_realization_exists
    (hkill : ∀ n : ℕ, ∃ r : ℕ,
      ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (κ : CartierEtaleKummerFamily l E)
    (hκ : CartierEtaleKummerNormalization l E κ) :
    ∃ c : CartierKummerFamily l E, CartierKummerRealization l E κ c := by
  sorry

end AlgebraicGeometry.Etale
