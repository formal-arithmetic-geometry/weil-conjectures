## Worker report

The module `Sheaf.RingTheory.GradedPolynomialVertexRegularity` states
`MvPolynomial.exists_monic_linear_direction_of_vertex_ne_zero`, with `sorry` as its
only proof. It creates no definitions, helper theorems, new nodes or dependency repairs.
The item's only changed field is `lean`.

Hypotheses and clauses, compared with the node:

- The infinite field k is `{k : Type u} [Field k] [Infinite k]`. The commutative
  k-algebra B is `{B : Type v} [CommRing B] [Algebra k B]`; the independent
  universes do not constrain its size. `[Nontrivial B]` renders the node's
  inclusion `B_0 = k`: a nonzero field cannot be a subring of the zero ring.
  It does not add a domain or reducedness assumption on B.
- The grading is `𝒜 : ℕ → Submodule k B` with `[GradedAlgebra 𝒜]` and the
  recorded `[GradedAlgebra.IsStandard 𝒜]`. This is the dependency's existing
  finite-generation-in-degree-one definition; its `grade_zero_eq_one` identifies
  the zero component with the scalar image. In a nontrivial field algebra this
  scalar map is injective, so this is precisely the stated copy of k.
- Write the node's positive number of variables as `e + 1`, for arbitrary
  `e : ℕ`. All positive variable counts occur, with no additional restriction.
  The variables are `Fin (e + 1)`, and the node's T_1 is `X 0`.
- `n : ℕ` and `hn : 1 ≤ n` express the positive homogeneous degree.
  `f : MvPolynomial (Fin (e + 1)) B` is exactly P.
- `hf` expresses homogeneity for the combined grading, not homogeneity for
  variable degree with degree-zero coefficients. At each exponent d its first
  clause is `coeff d f ∈ 𝒜 (n - d.degree)`; its second clause forces that
  coefficient to vanish when `n < d.degree`. This explicitly handles truncated
  natural subtraction and gives exactly coefficient degree plus variable degree n.
- `H : MvPolynomial (Fin (e + 1)) k` names epsilon(f).
  `hH : map (algebraMap k B) H = map (GradedRing.projZeroRingHom 𝒜) f`
  is exactly the equation H = epsilon(f), expressed after the injective scalar
  embedding into B. The right side is the actual canonical coefficientwise
  degree-zero projection, not an arbitrary augmentation. Its kernel is the
  positive-degree ideal. Since `𝒜 0` is the scalar image, every projected
  coefficient has a unique preimage in k. Thus this binder/equation is merely
  naming the canonical H, with no extra hypothesis or choice of map.
  `hH0 : H ≠ 0` is the node's nonzero vertex-image hypothesis.
- The existential v is `Fin (e + 1) → k`; `v ≠ 0 ∧ eval v H ≠ 0` renders
  both nonzero-vector and nonzero-value requirements.
- `M : Matrix.GeneralLinearGroup (Fin (e + 1)) k` is GL, not merely an arbitrary
  matrix. The equation at every i, `M i 0 = v i`, is its first column.
- `σ : P ≃ₐ[B] P` is a B-algebra automorphism. Its generator equations are
  exactly `σ (X i) = ∑ j, C (algebraMap k B (M i j)) * X j`.
  `MvPolynomial.algHom_ext` identifies this with the specified canonical
  substitution, so no different automorphism can satisfy these equations.
- The universal equivalence on homogeneous coefficient conditions for every
  m and g says σ preserves the total grading in both directions. The same
  criterion as in `hf` is used, including vanishing above degree m.
- `finSuccEquiv B e` is the existing B-algebra equivalence P ≃ D[X 0], with
  `D = MvPolynomial (Fin e) B`. Its `X_zero` and `X_succ` formulas confirm that
  it collects powers of precisely T_1 while retaining every other variable.
- `(finSuccEquiv B e (σ f)).natDegree = n` is the exact degree assertion, and
  its `leadingCoeff = C (algebraMap k B (eval v H))` is the scalar H(v).
  The preceding nonzero evaluation and injective scalar maps ensure this
  leading coefficient is nonzero.
- `Monic` of `finSuccEquiv B e (C (algebraMap k B ((eval v H)⁻¹)) * σ f)`
  is exactly the monic rescaling in D[T_1]. The inverse is taken in k.
- `Function.Injective (fun g : P ↦ f * g)` is injectivity of multiplication by f
  on all of P, independent of the chosen direction.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.GradedAlgebra.Standard`:
  `GradedAlgebra.IsStandard` (its full class and docstring were read), with
  `GradedAlgebra.IsStandard.grade_zero_eq_one` explaining B_0 = k.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial` and `algHom_ext`;
  `Mathlib.Algebra.MvPolynomial.Eval`: `aeval`, its generator formula and
  uniqueness. These implement the recorded polynomial-ring dependency.
- `Mathlib.Algebra.MvPolynomial.Equiv`: `finSuccEquiv`, with its full signature
  and formulas on the zero and successor variables read.
- `Mathlib.RingTheory.GradedAlgebra.Basic`: `GradedRing.projZeroRingHom` is the
  actual degree-zero projection ring homomorphism used by `hH`.
- The stated proof dependencies are imported without `public`:
  `Mathlib.Algebra.MvPolynomial.Funext`, `MvPolynomial.funext_set` for the
  infinite-field direction; `Mathlib.Algebra.Polynomial.RingDivision`,
  `Polynomial.Monic.mem_nonZeroDivisors` for monic regularity. Both signatures
  and surrounding source were read; these are the nodes' Mathlib matches.

Sources read: the assigned node and every statement dependency and proof
prerequisite; `literature/stacks-project/algebra.tex`, lemma-colimit-syntomic,
including its monic regular-sequence paragraph; the current latest blueprint's
standard-graded-algebra definition and `sk-i-curve-zero/_section.md`.
Tag 07BV supports monic regularity only. The full graded linear-substitution
argument remains attributed to the agent-written refinement, as in the node.
The latest unit concerns Frobenius local vanishing; this delivery does not alter
its statement or the historical provenance of this algebraic descendant.

Edge cases checked:

- The node's one-variable case is `e = 0`. D then has no variables and
  `finSuccEquiv` is still defined. For k[T] the change is a nonzero scalar
  rescaling of T; no other coordinate is required.
- Positive n is retained. Zero f or H is excluded only by `hH0` and the
  canonical reduction equation; a form with zero vertex image is not claimed
  regular. The all-zero vector is explicitly excluded.
- B may have nilpotents or zero divisors. For example, in
  B = k[u]/(u^2), with deg u = 1, f = T^2 + uT has vertex image T^2 and is
  already monic. No domain hypothesis has been introduced.
- For B = k and f = T_1*T_2, v = (1,1) and matrix with columns (1,1),(0,1)
  give sigma(f) = T_1^2 + T_1*T_2 and scalar leading coefficient 1. This checks
  the row/substitution versus column/direction convention.
- The separate coefficient-vanishing clause matters for exponents of degree
  greater than n; allowing only membership in degree n - d.degree would be wrong.
- Arbitrary characteristics of infinite fields remain allowed; there is no
  characteristic-zero, finite-dimensional B or reducedness condition.

Searches for an existing statement (all run through the prescribed msearch.py):

- LeanFinder query: "homogeneous polynomial over a standard graded algebra with
  nonzero reduction modulo positive degree becomes monic after an invertible
  linear change of variables and multiplication by it is injective". Eight hits,
  including `Polynomial.MonicDegreeEq.freeMonic`, homogenization and
  `MvPolynomial.IsHomogeneous.of_map`; no graded coefficient direction theorem.
- Loogle query: `MvPolynomial.IsHomogeneous, Polynomial.Monic`. Zero hits.
- Grep query: `(homogeneous|IsHomogeneous).*(nonZeroDivisors|isRegular)|linear.*[Ss]ubstit|finSuccEquiv`
  in `Algebra/MvPolynomial`. Fourteen hits on finSuccEquiv and its use; these
  give the required polynomial equivalence, not the node's theorem.
- LeanSearch query: "A homogeneous polynomial over a standard graded algebra
  whose reduction modulo the positive-degree ideal is nonzero becomes monic
  after an invertible linear substitution". Eight hits on homogenization,
  monic polynomials and ordinary homogeneous polynomials; no exact match.
- Repository rg searches for `IsStandard`, `vertex`, `monic`,
  `graded-polynomial`, `projZeroRingHom`, and linear substitutions in both
  `lean/WeilConjectures` and `lean/Sheaf`. Found the existing standard-grading
  definition, canonical projection and the consumer
  `Sheaf.RingTheory.NormalConeDirectrixMinimalPrimes`; none states this lemma.
  Searching the exact item id in `lean/WeilConjectures` and `lean/Sheaf` found
  no existing declaration. The consumer uses the same homogeneous coefficient
  criterion, which validates compatibility with its intended application.

No statement correction, disputed statement, missing dependency or new notion
was needed. Server scompile.py compiled the delivered module in sandbox and
library mode cleanly (1.5 s and 1.4 s, respectively), with no errors or warnings.

## Second reading by Q53

I reread the complete node beside the completed Lean signature and the recorded
dependency declarations after the clean compile. This is a second pass by the
same dispatcher-started worker; no other agent was started, as instructed. The
maintainer supplies the independent delivery review.

The infinite field and standard grading are retained. Nontriviality is required
by the node's B_0 = k, rather than a hidden domain assumption. The `hH` equation
uses the canonical projection and names exactly H, not its top-degree part by
an unrelated construction. The two parts of `hf` describe the total grading,
including the high-variable-degree vanishing condition. Every positive variable
count is represented by e+1; e=0 here means one variable, not the node's excluded
zero-variable case. The matrix first-column equation agrees with the row-indexed
substitution formula. The automorphism fixes B by its algebra-equivalence type,
and the homogeneous iff clause records the grading. `finSuccEquiv` singles out
index zero, and both the exact degree and scalar leading coefficient are
present. The final two clauses give the exact inverse-scalar normalization and
injectivity, without dropping any case where B has zero divisors. No mismatch
was found and no correction of the node was necessary. The module has a single
named theorem with `sorry` and all five proof steps in its source docstring.
