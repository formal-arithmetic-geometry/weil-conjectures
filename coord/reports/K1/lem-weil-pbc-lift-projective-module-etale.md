## Worker report

States Stacks 07M5 as `AlgebraicGeometry.lift_finite_projective_module_etale`: `A` commutative, `I : Ideal A`, `Pbar` a finite (`Module.Finite`) projective (`Module.Projective`) `A ⧸ I`-module; conclusion: `A' : CommRingCat.{u}`, `g : of A ⟶ A'` with `Algebra A A' := g.hom.toAlgebra`, `Etale (Spec.map g)` (def-weil-etale-morphism), `α : A ⧸ I ≃+* A' ⧸ I.map (algebraMap A A')` tied to the induced map on classes, a finite projective `A'`-module `P' : Type u`, and an `A'/IA'`-linear equivalence `P' ⧸ (IA' • ⊤) ≃ₗ (A'/IA') ⊗[A ⧸ I] Pbar` with `Algebra (A ⧸ I) (A'/IA')` from `α` (Mathlib's base-change order; `Pbar ⊗ A'/IA'` carries no `A'/IA'`-module instance). Form follows G1's landed lem-weil-pbc-lift-idempotent-upstairs.

## Second reading by K1

K1's second reading kept `≃+` as "the strongest typable encoding" and did not notice that `α` was untied. Reviewer fix (R-lpm1152): the delivery had (1) `α` an arbitrary bijective ring map, not the induced map A/I → A'/IA'; (2) only an additive equivalence `≃+` instead of an isomorphism of A'/IA'-modules, and `P' ⊗ A'/IA'` in place of P'/IP'. Both restated as above.
