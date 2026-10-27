## Worker report

The module `Sheaf.LinearAlgebra.TorusEquivariantFrobeniusModuleBasis` states
`SkewPolynomial.exists_homogeneous_basis_of_frobenius_weights`. It contains one theorem,
with `sorry`, and no new definitions or proofs. Only the item's `lean` field changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field k is `{k : Type u} [Field k]`. This is the exact `Field` declaration named by
  `def-weil-field.mathlib_match` (Mathlib.Algebra.Field.Defs, line 180); that dependency is
  Mathlib, so it needs no Lean record or dependency repair.
- Prime characteristic p > 0 is `(p : ℕ) [Fact p.Prime] [CharP k p]`. Primality includes
  p >= 2. Neither characteristic zero nor composite p is admitted.
- The ring A is Mathlib's `SkewPolynomial k`. Its underlying type is finite coefficient
  families on `Multiplicative ℕ`, with coefficientwise addition. Its multiplication is
  specified by the binder `[MulSemiringAction (Multiplicative ℕ) k]` and
  `hφ : SkewPolynomial.φ (R := k) = frobenius k p`. The Mathlib formula
  `SkewPolynomial.monomial_mul_monomial` reads
  `(a F^r)(b F^t) = a φ^[r](b) F^(r+t)`, hence exactly `a b^(p^r) F^(r+t)` under hφ.
  The action is the implementation parameter for this specified multiplication, not
  an additional mathematical restriction. It is always supplied by iterating the
  Frobenius endomorphism; it requires no inverse or surjectivity of Frobenius.
  Equality of the generator specifies the entire action by `φ_iterate_apply`.
- A left A-module M is `{M : Type v} [AddCommGroup M] [Module (SkewPolynomial k) M]`.
  The independent universe v permits every module size covered by the node.
- The two nonnegative integers are `(d s : ℕ)`.
- The given isomorphism to A^d is
  `hfree : Nonempty (M ≃ₗ[SkewPolynomial k] (Fin d → SkewPolynomial k))`.
  Linear equivalences over this possibly noncommutative ring are additive bijections
  respecting left scalar multiplication. The function module uses coordinatewise left
  multiplication, precisely as the node specifies.
- The lattice Z^s is `Fin s → ℤ`. The family of k-subspaces is W. Its type is explicitly
  `@Submodule k M _ _ (Module.compHom M SkewPolynomial.CRingHom)` at each lattice weight.
  Thus scalar multiplication is definitionally `C c • m`, the stated restriction along
  constant polynomials. There is no independently chosen vector-space structure or
  extra scalar-compatibility assumption.
- Unique finite homogeneous decomposition is `hW : DirectSum.IsInternal W`.
  This is bijectivity of the canonical summation map from the external direct sum of
  the subspaces to M. It asserts both existence and uniqueness, not just spanning.
- The weight condition is `hF : ∀ ν m, m ∈ W ν → X • m ∈ W (p • ν)`.
  `SkewPolynomial.X` is `monomial 1 1`, hence the node's F. Natural scalar multiplication
  on `Fin s → ℤ` multiplies every lattice coordinate by p.
- The conclusion gives `b : Module.Basis (Fin d) (SkewPolynomial k) M` and
  `ν : Fin d → (Fin s → ℤ)` with `∀ j, b j ∈ W (ν j)`.
  `Module.Basis` represents an actual left-linear coordinate equivalence with finitely
  supported coefficients. Since `Fin d` is finite, this is exactly a d-element A-basis,
  with a specified lattice weight for each vector.
- There is no perfectness, finite-dimensionality over k, positivity of d or s, exclusion
  of zero weight, or additional hypothesis in the signature.

Dependencies and declarations read:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs:180.
- `SkewPolynomial`, `SkewPolynomial.φ`, `SkewPolynomial.φ_iterate_apply`,
  `SkewPolynomial.monomial_mul_monomial`, `SkewPolynomial.CRingHom`, and
  `SkewPolynomial.X`: Mathlib.Algebra.SkewPolynomial.Basic. Read its module docstring
  and full declarations, including the finite-support implementation and left twist.
- `frobenius`: Mathlib.Algebra.CharP.Lemmas:321, the ring homomorphism `c ↦ c^p`.
- `Module.compHom`: Mathlib.Algebra.Module.RingHom:57, restriction with action `f c • m`.
- `DirectSum.IsInternal`: Mathlib.Algebra.DirectSum.Basic:440, and its submodule API in
  Mathlib.Algebra.DirectSum.Module. Read the definition of the canonical summation map.
- `Module.Basis`: Mathlib.LinearAlgebra.Basis.Defs:90, including its coordinate-equivalence
  definition and the finite-index `Basis.equivFun`/`Basis.ofEquivFun` interface.
- The three proof dependencies currently have no `lean` records or Mathlib matches:
  `lem-sfb-frobenius-skew-free-submodules`, `lem-sfb-dilating-weight-nakayama`, and
  `lem-sfb-coefficient-endomorphism-preserves-independence`. Thus no unavailable proof
  module is imported. Their arguments and node names are preserved step by step in
  the theorem's proof-plan docstring. No statement needs their declarations.

Sources checked: the complete assigned node and its sole statement dependency; the
current blueprint `latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
unit statement and direct-images proof, clause (3); Milne iAG2017 printed p.293
(PDF p.305), the relation `Fc = c^p F`, and printed p.296 (PDF p.308), Proposition
14.50 and the adjacent division algorithms. The node explicitly calls the homogeneous
refinement agent-formulated; Milne is cited only for the ungraded input. The delivery
does not falsely attribute the homogeneous refinement to Proposition 14.50.

Edge cases checked against both the node and the Lean signature:

- d = 0: the given equivalence forces M to be the zero module. The conclusion is the
  empty basis and empty weight family; `Fin 0` imposes no impossible choice of vectors.
- s = 0: `Fin 0 → ℤ` is a singleton, namely zero. Internalness forces its sole summand
  to be all M. Any given basis is homogeneous; no nonzero-weight hypothesis appears.
- Zero weights for arbitrary s: F maps the zero component into itself, and the conclusion
  permits any or all basis weights to be zero.
- Imperfect k, for example F_p(t): Frobenius is a ring endomorphism and is not assumed
  surjective. The action and all ring/module types require only its forward iterates.
- The zero vector and the zero module are allowed by all subspace and direct-sum types.
- An ungraded free rank-d module with all weight zero satisfies the assumptions, so the
  hypotheses do not accidentally exclude the most basic intended examples.

Searches actually run for this item:

- `msearch.py ... leanfinder "A finite free left Frobenius skew polynomial module with
  integer lattice weight grading admits a homogeneous basis"`: 8 hits. Candidates were
  `Algebra.PreSubmersivePresentation.basis`, `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous`,
  its nonzero variant, weighted homogeneous polynomial APIs, `Polynomial.Sequence.basis`,
  `Polynomial.degreeLT.basis`, and `LinearMap.toMvPolynomial_isHomogeneous`. None states
  a free left skew-polynomial module's homogeneous-basis theorem.
- `msearch.py ... loogle 'Module.Basis, "homogeneous"'`: 2 hits,
  `LinearMap.toMvPolynomial_isHomogeneous` and
  `LinearMap.polyCharpoly_coeff_isHomogeneous`; neither concerns this statement.
- `msearch.py ... grep 'homogeneous|[Bb]asis' Algebra/SkewPolynomial`: 0 hits.
- `rg` in `lean/WeilConjectures` for the node id: 0 hits. Searches there and in
  `lean/Sheaf` for `SkewPolynomial`, Frobenius/skew terms, and homogeneous-basis names
  found the two-sided skew division theorem and connected-graded projective freeness.
  Read `Sheaf.RingTheory.SkewPolynomialTwoSidedDivision`: it assumes the twist bijective
  and states division only. Read `Sheaf.RingTheory.ConnectedGradedProjectiveFree`: it
  concerns a commutative algebra with additive nonnegative grading, not Frobenius
  dilation of lattice weights on a left skew module. Neither can be reused as this node.
- Exact proposed declaration-name search in Mathlib/project naming inputs found no
  collision. The sole statement dependency already uses Mathlib's Field, and every
  other notion here has the Mathlib implementation listed above. No definition node
  or private copy is needed.

The first server check identified a missing import for `frobenius`; replaced the CharP
Basic import by CharP Lemmas, the owning module. All compilation uses `scompile.py`.
The wrapper's local compile encountered `OSError(28, 'No space left on device')` and
then its prescribed confirmation against current server sources succeeded (1.1 s).
The final standalone check, including `set_option autoImplicit false`, also succeeded
on the current server sources (1.4 s), with no errors or unexpected warnings.
`deliver2.py Q66 lem-sfb-torus-equivariant-frobenius-module-basis --no-push` printed
`OK (dry run)`: the packet passes server preflight and compiles. The wrapper used its
server confirmation after the same local disk-space failure; that fallback completed
successfully. The prescribed wrappers and all launcher files were left unchanged.

No statement correction, disputed assertion, or dependency-interface fault was found.

## Second reading by Q66

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
