## Worker report

The module `Sheaf.RingTheory.HomogeneousPrimaryTest` states
`Ideal.IsHomogeneous.isPrimary_of_homogeneous_factors`, with a single `sorry` proof.
It introduces no definitions. The node is unchanged except for its `lean` field.

The hypothesis and conclusion correspondence is as follows.

- A commutative ring is `{R : Type u} [CommRing R]`, with arbitrary universe `u`.
- The additive subgroups indexed by nonnegative integers are
  `𝒜 : ℕ → AddSubgroup R`. The instance `[GradedRing 𝒜]` supplies precisely the
  unique finite decomposition, `1 ∈ 𝒜 0`, and multiplication from degrees `a,b`
  into degree `a+b`: it extends `DirectSum.Decomposition` and
  `SetLike.GradedMonoid`. The decomposition is an inverse of canonical finite
  summation, not an additional choice of mathematical structure.
- Noetherianity is `[IsNoetherianRing R]`.
- The proper ideal is `{J : Ideal R}` with `hJ_ne_top : J ≠ ⊤`.
- Homogeneity of J is `hJ : J.IsHomogeneous 𝒜`; its definition says that every
  homogeneous component of an element of J lies in J.
- The homogeneous-factor test quantifies over arbitrary `{a b : R}` and uses
  `SetLike.IsHomogeneousElem 𝒜 a` and `SetLike.IsHomogeneousElem 𝒜 b`. Each means
  membership in some graded piece, including the zero element. The next two
  hypotheses are exactly `a * b ∈ J` and `a ∉ J`. Its conclusion is
  `∃ h : ℕ, 1 ≤ h ∧ b ^ h ∈ J`. Positive integers are represented by positive
  naturals, exactly the exponents defined for arbitrary ring elements.
- The conclusion `J.IsPrimary` is Mathlib's primary ideal predicate, not a
  private version. `Ideal.isPrimary_iff` identifies it with properness and, for
  arbitrary u,v with uv in J, either u in J or v in `J.radical`. By
  `Ideal.mem_radical_iff`, radical membership means some natural power lies in
  J. A zero exponent would put 1 in the proper ideal, so that exponent is
  necessarily at least 1. Thus this renders exactly the node's last clause
  for arbitrary, possibly inhomogeneous, u and v.

Dependency declaration used: the sole statement dependency
`def-weil-pbc-noetherian-ring` records `IsNoetherianRing` in
`Mathlib.RingTheory.Noetherian.Defs`, which is imported publicly. Its complete
signature and docstring were read: it abbreviates `IsNoetherian R R`, meaning
all ideals are finitely generated. The node has no proof dependencies.
Other existing notions used are `GradedRing` in
`Mathlib.RingTheory.GradedAlgebra.Basic`, `DirectSum.Decomposition` in
`Mathlib.Algebra.DirectSum.Decomposition`, `SetLike.GradedMonoid` and
`SetLike.IsHomogeneousElem` in `Mathlib.Algebra.GradedMonoid`,
`Ideal.IsHomogeneous` in `Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal`,
and `Ideal.IsPrimary` in `Mathlib.RingTheory.Ideal.IsPrimary`. Their definitions
and docstrings, including the underlying homogeneous submodule and primary
submodule definitions, were read. No missing dependency module or new node
is needed.

Source checked: Altman--Kleiman, Proposition 20.24, printed p.122, PDF page 130,
in the authors' PDF <https://web.mit.edu/18.705/www/13Ed.pdf>. Specializing its
regular module to R identifies its quotient nilradical with the ideal radical.
The node's six-step expansion argument is included in the theorem docstring,
retaining the power k throughout the subtraction and least-degree argument.

Edge cases checked before writing:

- The zero ring has no proper ideal; its exclusion follows from the stated
  properness assumption, with no added `Nontrivial` assumption.
- The unit ideal is excluded exactly by `J ≠ ⊤`.
- Zero elements are homogeneous. If v=0, exponent 1 works. If u=0, the premise
  u outside J is impossible. No nonzero homogeneous-factor restriction is added.
- A grading concentrated in degree zero is allowed and reduces to the usual
  primary ideal condition. No generation-in-degree-one or field hypothesis occurs.
- Arbitrary zero graded pieces and a decomposition with empty support are
  permitted. The proof's empty sums use exponent 1. Degree zero and the zero
  ideal remain within scope.
- Positive exponents are required explicitly in the test; the equivalence for
  the conclusion uses properness to exclude exponent zero.
- No restriction on characteristic or on the universe of R is imposed.

Searches for existing statements (2026-10-24 UTC):

- `msearch.py`, LeanFinder: "A proper homogeneous ideal in a Noetherian
  nonnegatively graded commutative ring is primary if the primary condition
  holds on homogeneous elements". Eight results, led by
  `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem`,
  `Ideal.IsHomogeneous.isPrime_iff`, and `Ideal.IsPrime.homogeneousCore`.
  These test primality, not primaryness, and do not state this lemma.
- `msearch.py`, Loogle: `"IsHomogeneous", "IsPrimary"`. Zero results.
- `msearch.py`, grep: `IsPrimary|isPrimary` in
  `RingTheory/GradedAlgebra`. Zero results.
- `msearch.py`, LeanSearch: "A homogeneous ideal is primary if products of
  homogeneous elements satisfy the primary ideal criterion". Eight results,
  including the two homogeneous prime criteria, `Ideal.IsPrime.isPrimary`,
  `Ideal.IsPrimary`, and `Ideal.isPrimary_iff`. Read the primary definitions
  and criterion: the latter still tests all ring elements, so it is not the
  homogeneous test being stated.
- Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `homogeneous.*[Pp]rimary|[Pp]rimary.*homogeneous` found only the related
  `Sheaf.RingTheory.HomogeneousPrimaryDecomposition`; reading its full
  declaration showed a polynomial-ring decomposition theorem, not this test.
  Direct search for the item id in `lean/WeilConjectures` found nothing.
- Direct `rg` for the proposed theorem name in Mathlib, project RingTheory,
  upstream RingTheory, and `dag/lean_names_upstream.json` found no collision.

No statement correction, disputed statement, or other node fault was found.

## Second reading by Q156

Written by the maintainer's independent reviewer, because the delivered section only stated
that no second reading took place. The node statement, listed clause by clause, with the Lean
that renders it and the verdict for each:

1. Commutative ring R graded by ℕ: a unique finite decomposition into additive subgroups R_d,
   with 1 ∈ R_0 and R_a R_b ⊆ R_{a+b}. In Lean: `{R : Type u} [CommRing R]`,
   `(𝒜 : ℕ → AddSubgroup R) [GradedRing 𝒜]`. `GradedRing` extends
   `SetLike.GradedMonoid` (one_mem, mul_mem) and `DirectSum.Decomposition` (a two-sided
   inverse of the canonical sum, so the decomposition is unique). Exact. The universe u is free.
2. Noetherian [def-weil-pbc-noetherian-ring]. In Lean: `[IsNoetherianRing R]`, which is the
   dependency's recorded Mathlib declaration (`IsNoetherian R R`). Exact. The proof does not use
   it, but the node assumes it, so keeping it is correct.
3. J ⊊ R is homogeneous. In Lean: `hJ : J.IsHomogeneous 𝒜` (which is
   `∀ i, ∀ r ∈ J, decompose 𝒜 r i ∈ J`) and `hJ_ne_top : J ≠ ⊤`. Exact.
4. Test on homogeneous a, b: if ab ∈ J and a ∉ J, then b^h ∈ J for some h ≥ 1. In Lean:
   `∀ {a b}, IsHomogeneousElem 𝒜 a → IsHomogeneousElem 𝒜 b → a * b ∈ J → a ∉ J →
   ∃ h : ℕ, 1 ≤ h ∧ b ^ h ∈ J`. The roles of a and b, the positivity of h and the meaning of
   homogeneous (membership in some 𝒜 d, so 0 counts) all match. Exact.
5. Conclusion: J is primary, i.e. for all u, v, if uv ∈ J and u ∉ J, then v^n ∈ J for some
   n ≥ 1. In Lean: `J.IsPrimary`, the Mathlib abbreviation of `Submodule.IsPrimary`. By
   `Ideal.isPrimary_iff`, it says `J ≠ ⊤ ∧ ∀ {x y}, x*y ∈ J → x ∈ J ∨ y ∈ J.radical`. With
   properness, a radical witness n = 0 would put 1 in J, so n ≥ 1. The only extra clause is
   J ≠ ⊤, which is hypothesis 3. Exact, with the same quantifier order.

Edge cases: the zero ring is excluded by J ≠ ⊤; v = 0 and u = 0 behave as the node says;
a grading concentrated in degree 0 reduces to the ordinary primary condition; there is no
nontriviality, field or universe restriction. The mathematics is Altman–Kleiman Prop. 20.24
with M = R, and the six-step proof in the docstring is correct: the components c^k u_t of
degree ks+t, then the hypothesis applied to (u_t, c^k).

One definition per notion: there is no `IsHomogeneous`/`IsPrimary` combination in Mathlib or in
lean/Sheaf and lean/WeilConjectures, and no other DAG node or module for this statement.
`HomogeneousPrimaryDecomposition` states a different theorem.

Records: the only change to the node is its `lean` field; `lean.statement` is verbatim the
signature in the file; stmt_deps = [def-weil-pbc-noetherian-ring], which is used. The docstrings
carry the source place and `(blueprint: lem-sfb-homogeneous-primary-test)`. There is no
definition, and the proof is `sorry`. No mismatch was found, and nothing in the Lean was changed.
