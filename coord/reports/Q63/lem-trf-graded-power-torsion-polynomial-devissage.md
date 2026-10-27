## Worker report

The module `Sheaf.RingTheory.GradedPowerTorsionPolynomialDevissage` states
`GradedAlgebra.IsStandard.power_torsion_polynomial_devissage` with one `sorry`.
No definitions, helper theorems, dependency repairs or statement corrections are needed.
The original statement, statement dependencies and proof remain unchanged.

Source read: `literature/stacks-project/algebra.tex`, lemma-graded-module-fg (00K0)
and proposition-graded-hilbert-polynomial (00K1), especially its two middle
paragraphs. The explicit finite-generation and homogeneous-component arguments in
the node supply the details omitted in that source. The Noetherian-submodule
Mathlib leaf gives the 00IK input.

Every hypothesis and clause is rendered as follows:

- The field is `{k : Type u} [Field k]`; the commutative k-algebra is
  `{S : Type v} [CommRing S] [Algebra k S]`. The universes are independent.
- The nonnegative algebra grading is `𝒜 : ℕ → Submodule k S` with
  `[GradedAlgebra 𝒜]`. The dependency's exact `[IsStandard 𝒜]` supplies finite
  generation by degree one and the degree-zero image of k. Noetherianity is
  `[IsNoetherianRing S]`.
- The fixed homogeneous degree-one element is `(x : S) (hx : x ∈ 𝒜 1)`.
- Each graded module L or M has its actual additive group, S-module and
  k-module structures and `[IsScalarTower k S L]` (or M). This last condition
  expresses the restriction of scalars implicit in a graded module over a
  k-algebra; it is not an extra mathematical restriction.
- Its k-subspaces are `ℒ : ℕ → Submodule k L` or `ℳ : ℕ → Submodule k M`.
  `[DirectSum.Decomposition ℒ]` is precisely a direct-sum decomposition and
  `[SetLike.GradedSMul 𝒜 ℒ]` says `S_i L_j ⊆ L_(i+j)`. Finiteness is
  `[Module.Finite S L]`. These conditions occur in the base hypothesis and
  both universally quantified conclusions. All modules range over `Type w`,
  with w arbitrary and independent of u and v; their submodules and quotients
  remain in w.
- `hbase` universally quantifies such finite graded L and assumes
  `(∀ l : L, x • l = 0)`. Its conclusion is
  `∃ P : Polynomial ℚ, ∃ d : ℕ, ∀ n : ℕ, d ≤ n →
  (Module.finrank k (ℒ n) : ℚ) = P.eval (n : ℚ)`.
  The polynomial and threshold may depend on L and its grading.
- The first conclusion universally quantifies the same data and replaces the
  annihilation hypothesis by `∃ r : ℕ, 1 ≤ r ∧ ∀ l : L, x ^ r • l = 0`.
  Positive integers are represented by naturals at least one. Its polynomial
  conclusion is verbatim the one in `hbase`. Homogeneous pieces are genuinely
  finite-dimensional by the node's monomial argument, so finrank represents
  their dimensions, rather than an arbitrary dimension convention.
- The second conclusion universally quantifies every finite graded M and
  asserts `∃ T : Submodule S M` with
  `∀ m : M, m ∈ T ↔ ∃ r : ℕ, 1 ≤ r ∧ x ^ r • m = 0`.
  Thus T is exactly the stated subset, and its submodule structure is asserted,
  not assumed. This membership equivalence determines T uniquely. No private
  power-torsion definition or arbitrary choice of a submodule is introduced.
- `Module.Finite S T` is finite generation of T. `T.IsHomogeneous ℳ` is
  Mathlib's closure under all homogeneous projections.
- `fun n : ℕ => (ℳ n).comap (T.subtype.restrictScalars k)` is the intersection
  grading `T_n = T ∩ M_n`, regarded as subspaces of T. `DirectSum.IsInternal`
  asserts that the canonical direct-sum map to T is bijective and
  `SetLike.GradedSMul 𝒜` asserts the degree rule for that grading.
- `∃ r : ℕ, 1 ≤ r ∧ ∀ t : T, x ^ r • t = 0` gives one uniform exponent,
  with the existential outside the quantifier over t.
- The next `∃ P : Polynomial ℚ, ∃ d : ℕ` gives the eventual polynomial for
  the finrank of these precise intersection subspaces.
- `M ⧸ T` is the actual quotient, and `Module.Finite S (M ⧸ T)` is its
  finite generation. `fun n : ℕ => (ℳ n).map (T.mkQ.restrictScalars k)` is
  exactly the image of M_n under the canonical quotient map. `IsInternal`
  and `GradedSMul` state that it is the asserted graded-module decomposition.
- `Function.Injective (fun q : M ⧸ T => x • q)` is injectivity of the actual
  quotient scalar action, with no unspecified map or extra hypothesis.
- There is no nonzero-module condition and no nonzero-polynomial condition.
  Both zero modules and the zero polynomial are allowed.

The structural assertions on the intersection and image families express the
node's words “with grading” and “graded by”; they are not additional restrictions.
The decomposition of an input module is uniquely determined by its family, as
`DirectSum.Decomposition` is a subsingleton. For output gradings the propositional
`DirectSum.IsInternal` avoids choosing decomposition data.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.GradedAlgebra.Standard`,
  `GradedAlgebra.IsStandard` (including `fg_one`, `adjoin_one`, and the
  `grade_zero_eq_one` and `finite_grade` signatures).
- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`, its underlying
  `IsNoetherian` class and `isNoetherianRing_iff_ideal_fg`.
- `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite` and its `fg_top` field.
- The proof-only dependency `lem-weil-pbc-noetherian-submodule-finite` is a
  Mathlib leaf naming `Submodule.FG.of_le` in
  `Mathlib.RingTheory.Noetherian.Basic`. Its full signature and docstring were
  read. That module is imported privately for the planned proof.
- Additional existing interfaces are `DirectSum.Decomposition`,
  `DirectSum.IsInternal`, `SetLike.GradedSMul`, `Submodule.IsHomogeneous`,
  `Submodule.comap`, `Submodule.map`, `Submodule.mkQ`,
  `LinearMap.restrictScalars`, `Module.finrank`, and `Polynomial.eval`.
  The quotient's inherited k-action and scalar tower are Mathlib's instances;
  no equality between coefficient, algebra or module universes was imposed.

Searches for an existing statement:

- `msearch.py ... leanfinder "Nilpotent devissage for eventual polynomial
  dimensions of finite graded modules and bounded homogeneous power torsion"`:
  eight hits, including `HomogeneousLocalization.Away.eventually_smul_mem`,
  `IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime`,
  `Ideal.exists_pow_inf_eq_pow_smul`, and adic/torsion-free results. None
  asserts the conditional polynomial devissage and its graded torsion quotient.
- `msearch.py ... loogle '"primaryComponent"'`: twelve hits on primary
  components of additive/commutative groups and monoids, not this theorem.
- `msearch.py ... grep 'primaryComponent|IsHomogeneous'
  RingTheory/GradedAlgebra`: twenty-one hits, including the homogeneous
  submodule interface used above, but no requested theorem.
- Read `Mathlib/Algebra/Module/Torsion/PrimaryComponent.lean`: the existing
  `Ideal.primaryComponent` constructs the ungraded ideal-primary component,
  and its membership lemma does not assert this graded polynomial devissage.
  The theorem instead states existence of the unique submodule with the
  exact prescribed membership predicate; no duplicate definition is written.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `polynomial_devissage`, `torsion.*[Hh]ilbert`, and `[Hh]ilbert.*torsion`:
  no exact declaration. A separate graded-module search found
  `Sheaf.RingTheory.StandardGradedHilbertFunction`, whose full statement was
  read: it is the general Hilbert-function theorem, not this conditional
  devissage and structural power-torsion assertion, so it is not imported.
- Read the exact Mathlib graded scalar, internal direct-sum and homogeneous
  submodule declarations. These existing notions eliminate any need for new
  definition nodes. The chosen theorem name has no upstream/project match.

Edge cases checked mathematically before writing:

- M=0: T=0, uniform exponent 1, polynomial zero, quotient zero; all direct
  sums and the quotient injectivity still hold.
- x=0 (including S=k with trivial positive grading): T=M and quotient zero.
  The base hypothesis already covers every module in this case.
- Exponent r=1 is exactly the base case; exponent zero is not required.
- S=k[t], L=S/(t^r) with its induced grading: T=L, killed by t^r, its
  eventual polynomial is zero. This checks the shift in the xL induction.
- M=k[t] ⊕ k[t]/(t^2), x=t: T is the second summand, and the quotient is
  k[t] with injective t-action. This checks the non-nilpotent mixed case.
- Empty homogeneous generating families and empty monomial families cause
  no restriction: the proof uses maximum with 1 and zero polynomials.
- n=0 is covered whenever d=0; a threshold greater than zero is permitted.

No node fault or statement dispute was found. All data and universe variables
are explicit (`set_option autoImplicit false`). Only the theorem proof is
postponed. `scompile.py Q63 lem-trf-graded-power-torsion-polynomial-devissage
<module>` compiled both the sandbox and library-module forms cleanly (2.3 s
and 1.6 s respectively).

## Second reading by Q63

A separate pass by this worker re-read the node and the complete final signature:
the outer conjunction retains both the universal nilpotent assertion and the
universal structural assertion for M. In particular the quantifiers for the
uniform exponent and the exact torsion membership are in different positions,
as required; the subspaces used for the torsion polynomial are the intersection
subspaces of T, and the quotient grading uses the canonical quotient map. The
positive exponent, arbitrary grading, finiteness of both T and the quotient,
homogeneity, and quotient injectivity are all present. No correction was needed.
This is a worker self-check, not a claim of an independent agent review; the
dispatcher forbids sub-agents and the maintainer supplies the independent review.
