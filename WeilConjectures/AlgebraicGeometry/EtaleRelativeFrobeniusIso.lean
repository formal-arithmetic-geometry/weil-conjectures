/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeCharacteristic
public import WeilConjectures.AlgebraicGeometry.Morphisms.AbsoluteFrobenius
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Relative Frobenius of an étale morphism

Source: Stacks Project, Étale Morphisms, Tag 0EBS, lemma-relative-frobenius-etale,
lines 1438--1456 (blueprint: lem-fd-etale-relative-frobenius-iso).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- For an étale morphism into a scheme of characteristic `p`, the relative Frobenius
is an isomorphism, with the stated naturality and affine description.

Source: Stacks Project, Étale Morphisms, Tag 0EBS, lemma-relative-frobenius-etale,
lines 1438--1456; affine formula from Varieties, Tags 0CC9 and 0CCB
(blueprint: lem-fd-etale-relative-frobenius-iso).

Here `F_X`, `F_U` are `iterateFrobenius … 1`, the fibre product is
`pullback u F_X` and `F_{U/X} = (F_U, u)` is `relativeIterateFrobenius … 1 u`. In the
affine clause `A` acts on the second tensor factor through `F_A(α) = α ^ p`: both module
structures of `TensorProduct A B A` are given explicitly as `Algebra.toModule` of the two
local algebras, because instance search would otherwise pick the ordinary action
`Semiring.toModule` of `A` on itself.

Proof (node steps 1--6):
1. The ring maps of `u` send `p • 1 = 0` to `p • 1 = 0`, so `U` has characteristic `p`;
   `u^♯(s ^ p) = (u^♯ s) ^ p` and both Frobenii are the identity on spaces, so
   `u ∘ F_U = F_X ∘ u`. The fibre-product universal property gives
   `r = (F_U, u) : U ⟶ T := U ×_{X, F_X} X` with `π₁ r = F_U` and `π₂ r = u`
   (Stacks 0CC7, 0CC9).
2. By the universal-homeomorphism theorem for relative Frobenius (Stacks 0CCB, with
   `S = X`, `Y = U`, `f = u`; uniqueness in the fibre product identifies it with `r`),
   `r` is a universal homeomorphism; no finiteness or reducedness assumption is needed.
3. `π₂ : T ⟶ X` is the base change of the étale `u` along `F_X`, hence étale (02GO);
   since `π₂ ∘ r = u` is étale, `r` is étale by étale cancellation (02GW).
4. Every base change of `r` is a homeomorphism, hence injective: `r` is universally
   injective, i.e. radicial (01S4); the identity base change shows `r` surjective.
5. A radicial étale morphism is an open immersion (025G); being surjective, `r` is an
   isomorphism, so `F_{U/X} = r` is an isomorphism.
6. For `X = Spec A`, `U = Spec B` with `A → B` étale, the affine fibre product is
   `Spec (B ⊗_{A, F_A} A)` (01I4, 01JQ) with projections `b ↦ b ⊗ 1`, `a ↦ 1 ⊗ a`;
   `π₁ r = F_U` and `π₂ r = u` make the ring map of `r` send `b ⊗ a ↦ b ^ p * φ a`
   (balanced since `φ(α) ^ p * φ a = φ(α ^ p * a)`), and the inverse of `r` gives the
   inverse ring map.
-/
theorem etale_relativeFrobenius_isIso (p : ℕ) (hp : p.Prime)
    {X : Scheme.{u}} (hX : X.IsCharacteristic p)
    {U : Scheme.{u}} (u : U ⟶ X) [Etale u] :
    U.IsCharacteristic p ∧
      u ≫ X.iterateFrobenius hp (hX.2 ⊤) 1 =
        U.iterateFrobenius hp (IsOfCharacteristic.of_hom (hX.2 ⊤) u) 1 ≫ u ∧
      (relativeIterateFrobenius hp (hX.2 ⊤) 1 u ≫
          Limits.pullback.fst u (X.iterateFrobenius hp (hX.2 ⊤) 1)) =
        U.iterateFrobenius hp (IsOfCharacteristic.of_hom (hX.2 ⊤) u) 1 ∧
      relativeIterateFrobenius hp (hX.2 ⊤) 1 u ≫
          Limits.pullback.snd u (X.iterateFrobenius hp (hX.2 ⊤) 1) = u ∧
      IsIso (relativeIterateFrobenius hp (hX.2 ⊤) 1 u) ∧
      (∀ (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B)
        (hA : (p : A) = 0), φ.Etale →
        letI : Algebra A B := φ.toAlgebra
        letI : Algebra A A := (iterateFrobeniusOfPrime A hp hA 1).toAlgebra
        ∃ e : @TensorProduct A _ B A _ _ Algebra.toModule Algebra.toModule ≃+* B,
          ∀ b a, e (@TensorProduct.tmul A _ B A _ _ Algebra.toModule Algebra.toModule b a) =
            b ^ p * φ a)
    := by sorry

end AlgebraicGeometry.Scheme
