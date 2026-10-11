/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Characteristic polynomial of a locally free module
Source: literature/stacks-project/more-algebra.tex, Lemma Tag 09XI
(blueprint: lem-weil-pbc-charpoly-locally-free-existence)
-/

universe u v w

open scoped TensorProduct

namespace Algebra

/-- Existence and uniqueness of the characteristic polynomial on a finite locally free module.
Source: literature/stacks-project/more-algebra.tex, Lemma Tag 09XI, proof of (3)⇒(1)
(blueprint: lem-weil-pbc-charpoly-locally-free-existence).
1. Use `lem-weil-pbc-localization-module-tensor` to identify each localized endomorphism
with scalar extension. In a local basis take its matrix characteristic polynomial
(`def-weil-pbc-charpoly-free-module`); basis independence and the monic expansion follow
from `lem-weil-pbc-charpoly-free-module-properties` (a), (c).
2. For any ring map inverting a cover element, factor through its localization and use
`lem-weil-pbc-module-base-change-transitive` and the localization-tensor comparison.
Naturality and free characteristic-polynomial properties (b), (d) identify the resulting
characteristic polynomial with the image of the local one.
3. Apply this comparison twice over the localization at the product of two cover elements.
The two local polynomials agree there, hence so do all their coefficients.
4. Glue each coefficient uniquely by `lem-weil-pbc-standard-covering-glue` (ii).
Uniqueness forces coefficients above n to vanish and the coefficient at n to be one.
These coefficients define the displayed polynomial, restricting to every local polynomial.
5. After any base change where the module is free, the images of the cover elements still
generate the unit ideal. Over their localizations, transitive base change and free
characteristic-polynomial properties compare both polynomials with the local ones.
Coefficientwise injectivity in `lem-weil-pbc-standard-covering-glue` (i) gives equality.
6. Any other polynomial with the base-change property restricts to the same local
polynomials. Apply the same coefficientwise injectivity to obtain uniqueness.
7. In the free case take the identity ring map, identify scalar extension with the original
module, and use free characteristic-polynomial properties (b) to obtain the usual polynomial.
-/
theorem charpoly_locallyFree_exists_unique
    {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]
    {n r : ℕ} (f : Fin r → A)
    (hgen : Ideal.span (Set.range f) = ⊤)
    (hfree : ∀ i : Fin r,
      ∃ e : Module.Basis (Fin n) (Localization.Away (f i))
        (LocalizedModule.Away (f i) M), True)
    (φ : M →ₗ[A] M) :
    let P : Polynomial A → Prop := fun χ ↦
      ∀ (A' : Type (max u w)) [CommRing A'] (ρ : A →+* A'),
        letI : Algebra A A' := RingHom.toAlgebra ρ;
        ∀ e : Module.Basis (Fin n) A' (A' ⊗[A] M),
          χ.map ρ = (LinearMap.toMatrix e e (φ.baseChange A')).charpoly;
    ∃ χ : Polynomial A,
      (P χ ∧ ∀ χ' : Polynomial A, P χ' → χ' = χ) ∧
      (∃ c : Fin n → A,
        χ = Polynomial.X ^ n +
          ∑ k : Fin n, Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)) ∧
      ((Nonempty (Module.Basis (Fin n) A M)) →
        ∀ e : Module.Basis (Fin n) A M,
          χ = (LinearMap.toMatrix e e φ).charpoly) := by
  sorry

end Algebra
