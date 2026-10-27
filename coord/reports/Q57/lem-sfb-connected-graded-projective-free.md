## Worker report

The module `Sheaf.RingTheory.ConnectedGradedProjectiveFree` states
`GradedAlgebra.exists_homogeneous_basis_of_finite_projective`, with `sorry` as its
only proof. There are no definitions, additional theorems, or node corrections.

Hypotheses and clauses matched against the node:

- The field is `{k : Type u} [Field k]`.
- The commutative unital algebra is `{A : Type v} [CommRing A] [Algebra k A]`.
- The subspaces are `𝒜 : ℕ → Submodule k A`. `[GradedAlgebra 𝒜]` is Mathlib's
  internal decomposition with compatible multiplication and unit in degree zero.
  Its decomposition data is unique and equivalent to an internal-direct-sum proof;
  it places no additional mathematical restriction on the grading.
- The connected condition via the given structure map is
  `hzero : 𝒜 0 = Submodule.span k ({1} : Set A)`. The scalar multiples of `1`
  are exactly the image of `algebraMap k A`.
- The integer-graded module is `{P : Type w} [AddCommGroup P] [Module A P]`, with
  `ℙ : ℤ → AddSubgroup P` and `hℙ : DirectSum.IsInternal ℙ`.
  Its scalar compatibility is `hsmul`, taking scalar degree `a : ℕ` and module
  degree `j : ℤ` to degree `(a : ℤ) + j`. Additive subgroups suffice: degree-zero
  constants preserve them by `hsmul`, so they are also vector subspaces for the
  induced scalar action. No independent scalar action on `P` is assumed.
- Ungraded finiteness and projectivity are exactly `[Module.Finite A P]` and
  `[Module.Projective A P]`.
- The finite index set is `Fin r`, for an existential natural number `r`. Every
  finite basis can be reindexed this way, including the empty basis `Fin 0`.
  The integer degrees are `e : Fin r → ℤ`; the basis is
  `b : Module.Basis (Fin r) A P`; `∀ i, b i ∈ ℙ (e i)` states homogeneity.
- The equivalent shifted isomorphism is the existing linear equivalence
  `b.repr.symm : (Fin r →₀ A) ≃ₗ[A] P`. By the definition of a basis it sends
  `c` to the sum of `c i • b i`. The final equivalence says that this sum belongs
  to `ℙ j` exactly when every coefficient is in `A_(j-e i)`, interpreted as zero
  when `j-e i < 0`. This describes precisely the degree-`j` component of
  `⨁ i, A(-e i)` and expresses preservation of degree in both directions, rather
  than assuming an arbitrary isomorphism or adding a shift definition.
- Negative scalar degrees are encoded by the `else c i = 0` branch; nonnegative
  degrees use `(j-e i).toNat`. This has the required sign for the convention
  `A(d)_j = A_(j+d)`.
- There is no nonzero, Noetherian, finite-type, or characteristic hypothesis.
  The field, algebra, and module have independent universes `u`, `v`, and `w`.
  `set_option autoImplicit false` is unnecessary: every identifier and universe
  in the declaration is explicitly bound.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, including its full
  signature and docstring.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`, with field `fg_top`.
- `def-weil-pbc-projective-module`: `Module.Projective`,
  `Mathlib.Algebra.Module.Projective`, and the documented lifting property.
- Mathlib's `GradedAlgebra`, `DirectSum.IsInternal`, and `Module.Basis` are used
  directly; their defining interfaces were inspected, including the coordinate
  equivalence `Basis.repr` and basis-vector definition.
- The proof dependency `lem-sfb-graded-nakayama-connected` currently has neither
  a Lean record nor a Mathlib match, so there is no recorded module to import.
  It is used only in the future proof, not to form this statement; the docstring
  names its two clauses exactly. The projective-module proof dependency is
  already imported because it is also a statement dependency.

Source checked: `literature/stacks-project/algebra.tex`, `lemma-graded-NAK`
(Tag 0EKB), parts (1) and (4), and `lemma-characterize-projective` (Tag 05CF),
including its splitting proof. The module docstring gives all five steps of the
node's argument: homogeneous residue basis, shifted free cover and residue
isomorphism, projective section and finite graded kernel, kernel Nakayama, and
inverse degree preservation. This is the node's extracted consequence, not a
claim that Stacks literally states this stronger homogeneous-basis conclusion.

Edge cases checked mathematically before writing: `P = 0` admits `r = 0`, for
which all coordinate conditions and all basis-vector conditions are vacuous,
and the zero element is in every component. The zero algebra is not excluded;
its unital modules are zero. For `A = k`, a basis vector of any integer degree
has coefficients only in scalar degree zero, as required. A free summand with
negative generator degree satisfies the same sign convention. Nilpotents in
`A`, arbitrary characteristic, and infinitely many algebra generators do not
alter any binder or introduce a Noetherian requirement.

Searches for an existing exact statement (2026-10-24):

- `msearch.py`, leanfinder: "A finite projective module with an internal integer
  grading over a connected nonnegative graded algebra over a field has a finite
  homogeneous basis". Eight hits concerned homogeneous finite algebra generators,
  homogeneous submodules, Proj, and homogeneous localization. No exact theorem.
- `msearch.py`, loogle: `Module.Projective, GradedAlgebra, Module.Basis`.
  Zero hits.
- `msearch.py`, grep: `graded.*projective|projective.*graded|homogeneous.*basis`.
  Six hits, on Proj and a Lie-algebra argument; no exact theorem.
- Direct `rg` of Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` for the concept,
  node id, and chosen full declaration name; inspected the relevant hits.
  `WeilConjectures.RingTheory.GradedNakayamaFree` states a theorem only over
  `MvPolynomial (Fin 2) k` with a Tor-vanishing hypothesis, so it cannot represent
  this node over an arbitrary connected graded algebra. The upstream name index
  was searched too. The parent `Sheaf.RingTheory.PolynomialGradedHilbertSyzygy`
  refers to this item only in its proof docstring.

Validation: the delivered module compiled through `scompile.py` against the
published live build, with no errors or non-sorry warnings. The signature in
`lean.statement` is extracted verbatim from the module. The original node is
preserved outside `lean`; there are no new nodes or dependency modules.

## Second reading by Q57

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
