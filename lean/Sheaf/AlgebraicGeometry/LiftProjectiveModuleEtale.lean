import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.LinearAlgebra.TensorProduct.Quotient

universe u v

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-!
# Finite projective modules lift over an etale neighbourhood

Source: Stacks Project, More on Algebra, Lemma Tag 07M5
(blueprint: lem-weil-pbc-lift-projective-module-etale).
-/

/--
A finite projective module over `A/I` lifts to a finite projective module over an
étale `A`-algebra `A'` whose induced map `A/I → A'/IA'` is an isomorphism: there is a
finite projective `A'`-module `P'` with `P'/IP' ≅ (A'/IA') ⊗_{A/I} P̄` as `A'/IA'`-modules,
the tensor product formed via `α` (Mathlib's base-change order `B ⊗ M`).

Source: Stacks Project, More on Algebra, Lemma Tag 07M5
(blueprint: lem-weil-pbc-lift-projective-module-etale).
Proof: write `P̄` as the image of an idempotent projector on `(A/I)^n`, lift it to an
endomorphism `p` of `A^n`, let `B = A[x]/(χ_p(x))` (Cayley–Hamilton), lift the idempotent of
`B/IB` given by the projector over an étale `A → A'` inducing `A/I ≅ A'/IA'`
(lem-weil-pbc-lift-idempotent-upstairs), and take `P'` the image of the resulting
idempotent endomorphism of `A'^n`.
-/
theorem lift_finite_projective_module_etale
    (A : Type u) [CommRing A] (I : Ideal A)
    (Pbar : Type v) [AddCommGroup Pbar] [Module (A ⧸ I) Pbar]
    [Module.Finite (A ⧸ I) Pbar] [Module.Projective (A ⧸ I) Pbar] :
    ∃ (A' : CommRingCat.{u}) (g : CommRingCat.of A ⟶ A'),
      letI : Algebra A A' := g.hom.toAlgebra;
      Etale (Spec.map g) ∧
      ∃ α : A ⧸ I ≃+* A' ⧸ I.map (algebraMap A A'),
        (∀ a : A, α (Ideal.Quotient.mk I a) =
          Ideal.Quotient.mk _ (algebraMap A A' a)) ∧
        ∃ (P' : Type u) (_ : AddCommGroup P') (_ : Module A' P'),
          Module.Finite A' P' ∧ Module.Projective A' P' ∧
          letI : Algebra (A ⧸ I) (A' ⧸ I.map (algebraMap A A')) :=
            α.toRingHom.toAlgebra;
          Nonempty ((P' ⧸ (I.map (algebraMap A A') • (⊤ : Submodule A' P'))) ≃ₗ[
              A' ⧸ I.map (algebraMap A A')]
            ((A' ⧸ I.map (algebraMap A A')) ⊗[A ⧸ I] Pbar)) := by
  sorry

end AlgebraicGeometry
