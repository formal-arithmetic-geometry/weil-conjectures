/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Transport of the symmetric presentation conormal module

Source: Stacks Project, Lemma 07CE, equation (16.3.1.1), at `a = 1`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace Algebra.Presentation

/-- Changing the quotient coefficient ring, its conormal module, and the indexing of
polynomial variables preserves the conormal of the canonical symmetric presentation.
This transport statement does not assume projectivity or assert freeness.

Source: Stacks Project, Lemma 07CE, the polynomial presentation preceding
(16.3.1.1), https://stacks.math.columbia.edu/tag/07CE.
(blueprint: lem-weil-pbc-symmetric-conormal-presentation-transport)

Proof. Identify `P.Quotient` with `A` by `P.quotientEquiv`. On conormal representatives,
the identity identifies `P.ker.Cotangent` with `P.toExtension.Cotangent`, semilinearly
for this coefficient equivalence. Compose with `e`. The symmetric algebra universal
property gives a ring equivalence from the symmetric algebra over `P.Quotient` to
`SymmetricAlgebra A M`: on coefficients it is the quotient equivalence followed by
the coefficient embedding, and on degree-one generators it is the conormal equivalence
followed by `ι`. Applying the universal property to the inverse coefficient and module
equivalences supplies its inverse. Their compositions fix coefficients and all
degree-one generators, hence are identities.
Flatten the iterated polynomial ring with the polynomial sum equivalence, and reindex
`Fin n ⊕ Fin m` by `finSumFinEquiv`. On constants, old variables, and new variables,
the resulting commuting square compares exactly the displayed maps `φ` and `f`.
The domain ring equivalence maps `ker f` onto `ker φ` and maps their squares onto
one another, because the codomain ring map is injective. Restrict it to the ideals
and descend it and its inverse to the quotients by their squares. The resulting
additive equivalence is semilinear for the quotient-ring equivalence. Compose that
scalar equivalence with the first-isomorphism equivalence induced by the surjective
map `φ`. Reinterpret its ideal cotangent as the extension cotangent: both are the
same quotient, and the scalar actions agree on every polynomial representative.
This gives `ρ` and the asserted equivalence. Neither this argument nor the universal
properties require projectivity, a nonzero ring, or nonempty variable sets. -/
theorem symmetric_conormal_presentation_transport
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {n m : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin m))
    (M : Type w) [AddCommGroup M] [Module A M]
    (e : P.toExtension.Cotangent ≃ₗ[A] M)
    [Algebra R (SymmetricAlgebra A M)] [IsScalarTower R A (SymmetricAlgebra A M)] :
    let I : Ideal (MvPolynomial (Fin n) R) := P.ker
    let C := SymmetricAlgebra (MvPolynomial (Fin n) R ⧸ I) I.Cotangent
    let φ : MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →+* C :=
      MvPolynomial.eval₂Hom ((algebraMap (MvPolynomial (Fin n) R ⧸ I) C).comp
        (Ideal.Quotient.mk I))
        (fun j ↦ SymmetricAlgebra.ι (MvPolynomial (Fin n) R ⧸ I) I.Cotangent
          (I.toCotangent ⟨P.relation j, P.relation_mem_ker j⟩))
    let f : MvPolynomial (Fin (n + m)) R →ₐ[R] SymmetricAlgebra A M :=
      MvPolynomial.aeval (fun i ↦ Sum.elim
        (fun j ↦ algebraMap A (SymmetricAlgebra A M) (P.val j))
        (fun j ↦ SymmetricAlgebra.ι A M
          (e (Extension.Cotangent.mk ⟨P.relation j, P.relation_mem_ker j⟩)))
        (finSumFinEquiv.symm i))
    ∀ hφ : Function.Surjective φ,
      ∃ ρ : (MvPolynomial (Fin (n + m)) R ⧸ RingHom.ker f.toRingHom) ≃+* C,
        Nonempty ((RingHom.ker f.toRingHom).Cotangent
          ≃ₛₗ[(↑ρ : (MvPolynomial (Fin (n + m)) R ⧸ RingHom.ker f.toRingHom) →+* C)]
          (Extension.ofSurjective φ.toIntAlgHom hφ).Cotangent) := by sorry

end Algebra.Presentation
