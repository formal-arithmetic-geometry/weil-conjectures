## Worker report

Q43, stage 2. The delivery states
`Hironaka.projective_order_triangular_coordinates` in
`Sheaf.RingTheory.ProjectiveOrderTriangularCoordinates` with proof `sorry`.
Its docstring carries all seven steps of the accepted split. Three real helper
constructions name precisely the index sets and degree expression already in
the item: `OrderPivot`, `OrderFreeVariable`, and `orderExpansionWeight`. These
are labels and arithmetic for this statement, not independent mathematical
notions. Their data are explicit subtype definitions and finite sums.

The previous BLOCKED ending concerns an unchanged stage-1 delivery. The current
node has no Lean record, and `coord/queue.tsv` lists it for stage 2. The explicit
stage-handoff paragraph of `coord/brief-stage2.md` section 0 requires continuing
this stage-2 attachment while preserving the accepted split. No repair note
exists for this item, and neither Q43 nor Q63 has a current return entry naming
it. The accepted statement and proof are preserved.

Hypothesis and clause correspondence, read against the node:

- An arbitrary field k is `{k : Type u} [Field k]`; `r : ℕ` includes zero.
  `MvPolynomial (Fin (r + 1)) k` is B, with label 0 equal to X0.
- The prime p is `PrimeSpectrum (MvPolynomial {i : Fin (r + 1) // i ≠ 0} k)`.
  Its affine polynomial ring has exactly r labels. `InOrderSpace r p d`
  uses `Localization.AtPrime p.asIdeal`, the maximal ideal of that local ring,
  and `algebraMap _ _ (MvPolynomial.dehomogenizeX k 0 f)`. Thus L, N and delta
  are exactly the prescribed localization, extended prime ideal, and evaluation
  f(1,t)/1. Mathlib's `Localization.AtPrime.map_eq_maximalIdeal` identifies the
  extended prime with this maximal ideal. The node's ord_J notation introduces
  no additional assertion or object used by the conclusions; its membership
  condition is represented directly by the same powers N^d.
- The total-degree grading is Mathlib's `MvPolynomial.IsHomogeneous` and
  `MvPolynomial.homogeneousComponent`. A polynomial belongs to the internal
  direct sum U exactly when all its homogeneous components belong to the
  corresponding `InOrderSpace`. All polynomials have finitely many nonzero
  homogeneous components, by `MvPolynomial.sum_homogeneousComponent`.
- The permutation is `π : Equiv.Perm (Fin (r + 1))` with `π 0 = 0`. Its
  restriction to the nonzero labels is precisely a permutation of X1,...,Xr.
  Applying π inside the formulas writes the new coordinates in the original
  polynomial ring. Correspondingly ti is relabelled to t_(π i); p and U remain
  the same geometric objects in that original presentation. No rationality or
  separability assumption is imposed on p.
- `∃ e : ℕ, e ≤ r` gives 0≤e≤r. `OrderPivot r e` is exactly 1,...,e.
  `q` has that domain; `∀ i, 1 ≤ q i` gives positivity, and the next clause
  gives nondecreasing q in the original numeric order. `c` supplies coefficients
  in k, and `σ` supplies actual polynomials.
- The displayed formula for `σ i` has leading term `X (π i.val) ^ q i`.
  The filter `i.val.val < j.val ∨ j = 0` includes exactly positions i+1,...,r
  followed by the distinguished X0. Thus its j=0 term is the paper's r+1 term,
  and no coefficient of an earlier variable or the pivot is introduced.
- The `∀ f, (...) ↔ f ∈ Algebra.adjoin k (Set.range σ)` clause is U=k[σ].
  It asserts equality with the entire internal direct sum, not just that the
  displayed generators lie in U.
- `ringChar k = 0 → ∀ i, q i = 1` is the characteristic-zero assertion.
  `ringChar k ≠ 0 → ∀ i, ∃ a : ℕ, q i = ringChar k ^ a` is the
  positive-characteristic assertion, including exponent a=0.
- `AlgebraicIndependent k (Sum.elim σ ...)` uses the disjoint union of the
  pivot labels and `OrderFreeVariable r e`. The latter is exactly e+1,...,r,0.
  Hence this is algebraic independence of exactly the node's r+1 elements.
- The final universal clause takes every degree d and every homogeneous f.
  A is a function from the e pivot labels to ℕ; beta is the subtype of such
  functions satisfying `∀ i, β i < q i`. This is exactly the node's Δ, with
  the nonnegativity already built into ℕ.
- `∃! F : (A-indices × Δ) →₀ MvPolynomial (OrderFreeVariable r e) k`
  specifies a unique finitely supported coefficient family, with its values in
  the polynomial ring on exactly the remaining variables. The homogeneity
  clause gives degree `d - orderExpansionWeight q A β`; that weight is
  `∑ i, q i * A i + ∑ i, β i`. A separate clause forces a coefficient to zero
  when the weight exceeds d, retaining the meaning of a negative degree rather
  than merely using truncated natural subtraction.
- `F.sum` embeds each coefficient by the canonical `MvPolynomial.aeval` at
  the remaining permuted variables, and multiplies it by `∏ i, σ i ^ A i`
  and `∏ i, X (π i.val) ^ β i`. This is exactly the stated finite expansion.
  Uniqueness is of all coefficients, not just an arbitrary chosen support.

Dependencies read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`, from def-weil-field.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`,
  `MvPolynomial.aeval`, `MvPolynomial.algHom_ext`, from
  def-weil-pbc-mv-polynomial-ring. Polynomial multiplication and evaluation
  supply the displayed monomials and canonical coefficient inclusion.
- `WeilConjectures.RingTheory.GradedAlgebra.Standard`:
  `GradedAlgebra.IsStandard`. This is the recorded standard-graded-algebra
  dependency, imported directly. The concrete polynomial grading is its usual
  Mathlib total-degree grading, so the theorem needs no extra grading choice
  or IsStandard hypothesis.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  the recorded localization dependency. Its maximal ideal and the structural
  map occur in the existing order-space definition.
- `Sheaf.RingTheory.PermissibleBasisChartData`: `Hironaka.InOrderSpace`,
  recorded by def-trf-permissible-basis-chart-data. That already landed node
  is added to stmt_deps under the rule permitting landed statement dependencies.
  No private order-space copy is introduced.
- `WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous`:
  `MvPolynomial.dehomogenizeX`, used by the existing order-space definition.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `AlgebraicIndependent`,
  the ordinary injectivity-of-aeval definition.

The two mathematical proof dependencies
lem-trf-projective-order-algebra-additive-generators and
lem-trf-additive-polynomial-monomial-classification currently have no Lean
record or Mathlib match. They are preserved in the proof and explicitly cited
in the theorem docstring; there is no module for either to import. Their
statements are not needed to type the item, so no dependency module is added.
The example CompactObject Sheaf file is withdrawn; I also read the recorded
upstream module for its public-module and docstring conventions.

Edge cases checked before and after drafting: r=0 gives only X0 and the prime
(0) in k; U=k, e=0, and the expansion is the original homogeneous polynomial
in X0. For arbitrary r, e=0 has singleton empty A and beta tuples, empty products
one, empty weight zero, and all original variables free. For e=r only X0 is
free. Degree d=0 leaves only the constant coefficient. Zero polynomials permit
all coefficients zero and have a unique such family. At a rational affine
point one obtains linear generators Xi-ai*X0. At p=(0), U=k, so no positive
pivot is needed. In characteristic p, q_i=1 is allowed as p^0; inseparable
prime ideals and larger characteristic powers are not excluded. The negative
coefficient-degree case is explicitly zero. No hollow hypothesis, statement
correction, or STATEMENT-DISPUTED issue was found.

Actual searches, all on this assignment through msearch.py (the wrapper keeps
its actual responses in searches.jsonl):

- leanfinder: "Triangular additive coordinates generate the projective order
  algebra and give a bounded monomial homogeneous polynomial basis". Eight
  hits, principally WeierstrassCurve.Affine.CoordinateRing.basis and
  Algebra.PreSubmersivePresentation.basis, with their signatures returned.
  They concern elliptic-curve rank-two bases or presentation modules, not U.
- loogle: `"MvPolynomial", "AlgebraicIndependent"`. Nine hits including
  `MvPolynomial.algebraicIndependent_X`,
  `AlgebraicIndependent.mvPolynomialOptionEquivPolynomialAdjoin` and its
  compatibility identities. They do not construct the order algebra or its
  triangular characteristic-power coordinates.
- grep: `triangular|projective.*order`, subdirectory RingTheory. Six hits:
  triangular matrices in Norm/Transitivity and a determinant in
  Polynomial/DegreeLT. None states the item.
- leansearch: "Triangular coordinates for the graded algebra of homogeneous
  forms whose order at a prime is at least their degree". Eight hits, including
  `MvPolynomial.gradedAlgebra`, `GradedAlgebra`, TensorAlgebra grading and
  HomogeneousLocalization.num_mem_deg. These supply generic gradings, not the
  projective order coordinates or unique bounded expansion.
- rg in lean/WeilConjectures and lean/Sheaf for projectiveOrder,
  projective_order, orderAlgebra, order algebra, order_algebra,
  triangular_coordinates and InOrderSpace found only the existing
  InOrderSpace, its homogeneous-approximation consumer, and unrelated uses of
  triangular matrices. The exact item-id search in lean/WeilConjectures has no
  match. Searches for each of the four proposed declaration names in Mathlib,
  WeilConjectures, Sheaf and dag/lean_names_upstream.json have no match.
- The DAG order-algebra search led to the existing chart-data node and the
  item's accepted proof dependencies; none already records this statement.
  Searching literature/blueprint/latest for triangular, Certain numerical,
  Lemma 18 and 13.2 found no separate current-blueprint statement of this
  historical Hironaka refinement, in agreement with its split_report.

Validation: scompile.py compiled this delivered file in both sandbox and
library module modes in 1.9 and 1.8 seconds respectively, with no diagnostics.
No direct compiler, global build, repository edit or Git command was used.

## Second reading by Q43

I performed a separate second pass with the node and complete Lean file open;
this is a self-rereading, since the dispatcher explicitly forbids starting
other agents and assigns independent delivery review to the maintainer.
I checked the actual finite sums and quantifiers, rather than just the intended
notation. In particular, the triangular filter includes X0 once and excludes
the pivot, the permutation fixes X0, the algebra equality uses every homogeneous
component of every polynomial, and the expansion's Finsupp domain is exactly
A times bounded beta. The remaining-coordinate aeval uses the same permutation
as the pivots. The homogeneity condition does not silently allow a nonzero
coefficient at a negative complementary degree, because the explicit zero
clause handles that case. The algebraic-independence index is a disjoint union,
not a set that could erase repeated elements. The e=0, r=0, e=r, d=0, zero-form,
and imperfect-field cases retain the node's meaning. There were no mismatches
requiring changes. Only lean and the permitted addition of the landed chart-data
node to stmt_deps differ from the live node.
