/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.MeromorphicModule
public import WeilConjectures.RingTheory.WeaklyAssociated
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # The affine calculation for generic meromorphic sections -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical fraction map is bijective on an affine open with finitely many components.
Source: Stacks Project, Divisors, Lemma 31.24.6, Tag 0EMF, affine calculation in the proof.
(blueprint: lem-sc-meromorphic-affine-generic-sections).

Proof: Write the affine open as Spec A. Its finitely many components correspond to the
minimal primes q_i of A. Weak association localizes (Tag 0566), so the hypothesis on
local rings puts every weakly associated prime of A among the q_i. A section of A is a
meromorphic denominator exactly when it is a non-zero-divisor: this can be checked in all
prime localizations. The total quotient algebra is consequently the finite product of
A_{q_i}, by the total-quotient minimal-prime product theorem. Quasi-coherence identifies
F on this affine with the sheaf of its section module M. Tensoring the algebra decomposition
with M gives S^{-1}M = product_i M_{q_i}; tensor commutes with this finite product.
The germ map identifies M_{q_i} with F_{eta_i}. At a generic point the spectrum of the
local ring has only one point, so its associated sheaf has sections F_{eta_i} on the
preimage of U. A generic point outside U contributes the zero module. Evaluation preserves
products, identifying the categorical product with this finite product and zero factors.
These identifications send m/1 to its germ at each generic point. Since fractions are
determined by m/1 and inversion of denominators, their resulting isomorphism equals phi. -/
theorem meromorphic_affine_generic_sections_isIso (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent]
    (hweak : ∀ x : X, IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
      Ideal.WeakAss (X.presheaf.stalk x) → x ∈ genericPoints X)
    (U : X.Opens) (hU : IsAffineOpen U) (hfinite : (irreducibleComponents U).Finite)
    (φ : (meromorphicPresheaf X F).obj (op U) ⟶
      (∏ᶜ (fun η : {x : X // x ∈ genericPoints X} ↦
        (pushforward (X.fromSpecStalk η.val)).obj
          (tilde (ModuleCat.of (X.presheaf.stalk η.val)
            (F.presheaf.stalk η.val))))).val.obj (op U))
    (hφ : ∀ (η : {x : X // x ∈ genericPoints X}) (hη : η.val ∈ U) (m : Γ(F, U)),
      (φ ≫ (Pi.π (fun ξ : {x : X // x ∈ genericPoints X} ↦
        (pushforward (X.fromSpecStalk ξ.val)).obj
          (tilde (ModuleCat.of (X.presheaf.stalk ξ.val) (F.presheaf.stalk ξ.val))))
        η).val.app (op U)).hom (LocalizedModule.mk m 1) =
        tilde.toOpen (ModuleCat.of (X.presheaf.stalk η.val) (F.presheaf.stalk η.val))
          (X.fromSpecStalk η.val ⁻¹ᵁ U) (F.presheaf.germ U η.val hη m)) :
    IsIso φ := by sorry

end AlgebraicGeometry.Scheme.Modules
