import Mathlib.RingTheory.RingHom.Flat
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option autoImplicit false

/-! # I-power torsion modules and flat base change

Source: Stacks Project, More on Algebra, Lemma 05E9 (implication (2) => (1))
(blueprint: lem-weil-pbc-torsion-module-flat-base-change-iso).
-/

open scoped TensorProduct

namespace RingTheory

/-- For a flat ring map inducing an isomorphism modulo an ideal, base change
preserves every module whose elements are killed by powers of that ideal.
The proof follows Lemma 05E9: the case killed by `I`, induction through
`I ^ n M`, and passage to the directed union of the bounded torsion parts.
- (blueprint: lem-weil-pbc-torsion-module-flat-base-change-iso)
- Proof source: Stacks Project, More on Algebra, Lemma 05E9, lines 24277--24298;
  it uses only flatness, tensor right exactness and colimit compatibility.
-/
theorem torsionModule_flat_baseChange_bijective
    {R S T : Type*} [CommRing R] [CommRing S] [AddCommGroup T] [Module R T]
    (φ : R →+* S) (hflat : RingHom.Flat φ) (I : Ideal R)
    (hiso : ∃ e : (R ⧸ I) ≃+* (S ⧸ I.map φ),
      ∀ r : R, e (Ideal.Quotient.mk I r) =
        Ideal.Quotient.mk (I.map φ) (φ r)) :
    (∀ x : T, ∃ n : ℕ, 0 < n ∧
      ∀ y : R, y ∈ I ^ n → y • x = 0) →
    Function.Bijective
      (fun x : T =>
        @TensorProduct.mk R _ T S _ _ _ (Module.compHom S φ) x 1) := by
  sorry

end RingTheory
