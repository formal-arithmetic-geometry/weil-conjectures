## Worker report

`exists_generic_finite_algebra_splitting` binds a Noetherian domain `A` and a finite `A`-algebra `B : Type v` and concludes: a nonzero `c : A`; `A' : Type u` with an `A[1/c]`-algebra structure, the induced `A`-algebra structure (`IsScalarTower A (Localization.Away c) A'`), finite, `Algebra.Etale`, `Spec A' → Spec A[1/c]` surjective; `r : ℕ` and `D : Fin r → Type u` finite `A'`-domains with each `Spec (D j) → Spec A'` `IsFinite`, `Surjective` and `(topologically IsHomeomorph).universally` (def-weil-universal-homeomorphism has no Mathlib class; this is its definition verbatim); and an `A'`-algebra isomorphism `(B ⊗[A] A') ⧸ nilradical ≃ₐ[A'] ∀ j, D j` with the `Algebra.TensorProduct.rightAlgebra` convention, as the sibling `lem-weil-pbc-generic-separable-algebra-splitting` (M1 c3aa8ce20).

Reviewer fix: the delivered form replaced `(B ⊗[A] A')_red` by an arbitrary reduced `Rred` with a surjective ring map `q` whose kernel is the nilradical and an `Rred ≃ₐ[A'] ∏ D j` for an `A'`-algebra structure on `Rred` unrelated to `q` (so the `A'`-structure of the reduction was not pinned); it also bound the fraction field `K` (only named by the node, never used, and not inferable as an implicit), restricted `B` to the universe of `A`, and repeated three imports. Now the quotient by the nilradical with the right-factor `A'`-structure, no `K`, `B : Type v`.

Edge cases: `B = 0` gives `r = 0` and the zero ring on both sides.

## Second reading by G1

G1's second reading matched the clauses but missed that the `A'`-algebra structure on `Rred` was unconstrained by `q` (so the isomorphism with `∏ D j` was not one of `A'`-algebras of the reduction of `B ⊗[A] A'`), the unused non-inferable `K`, and the universe restriction on `B`; reviewer R-gfa1058 fixed all three (see above).
