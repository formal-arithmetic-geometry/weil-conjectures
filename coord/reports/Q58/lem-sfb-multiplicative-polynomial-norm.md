## Worker report

States `Algebra.exists_characteristicPolynomial_of_multiplicative_homogeneous`
in `Sheaf.RingTheory.MultiplicativePolynomialNorm`. The only theorem proof is
`sorry`; there are no new definitions, helper theorems or dependency repairs.
The original node is unchanged except for its `lean` record.

This is a stage-2 delivery. The inherited ending concerned stage-1 delivery of
an already accepted split, not an existing Lean attachment: the current item
has no `lean` record and appears in the stage-2 queue. The stage-handoff paragraph
of coord/brief-stage2.md explicitly authorizes continuing in this case.
No repair note exists for this item.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Nonzero associative unital rational algebra E | `(E : Type u) [Ring E] [Algebra ℚ E] [Nontrivial E]`; no commutativity assumption on E |
| Finite dimensional | `[FiniteDimensional ℚ E]` |
| Positive integer degree d | `(d : ℕ) (hd : 0 < d)` |
| Rational-valued function | `(δ : E → ℚ)`; no additive or linear condition |
| Normalized at 1 | `h_one : δ 1 = 1` |
| Multiplicative | `h_mul : ∀ x y : E, δ (x * y) = δ x * δ y` |
| Polynomial in some rational basis | `h_poly` existentially quantifies n, `b : Module.Basis (Fin n) ℚ E`, and `D : MvPolynomial (Fin n) ℚ`; its evaluation clause is `∀ x, δ x = MvPolynomial.eval (b.repr x) D` |
| Every nonzero monomial has total degree d | `D.IsHomogeneous d`, Mathlib's existing predicate |
| Any element u | `(u : E)` with no extra hypotheses |
| Existence of rational polynomial | `∃ P : Polynomial ℚ` |
| Monic of degree d | `P.Monic ∧ P.natDegree = d`; monicity excludes the zero polynomial |
| Represents t ↦ δ(t1-u) | `∀ t : ℚ, P.eval t = δ (t • (1 : E) - u)` |
| Uniqueness of that polynomial | Every `Q : Polynomial ℚ` with the same evaluation clause satisfies `Q = P`. Over the infinite field ℚ, uniqueness holds even without imposing monicity or degree on Q; this expresses uniqueness of the representing polynomial itself. |
| Every splitting extension L/ℚ and all d roots counted with multiplicity | `∀ (L : Type v) [Field L] [Algebra ℚ L] (a : Fin d → L)` with `P.map (algebraMap ℚ L) = ∏ i : Fin d, (Polynomial.X - Polynomial.C (a i))`. This factorization is precisely a complete root enumeration for a monic degree-d polynomial, and includes repeated roots. It neither assumes L algebraically closed nor assumes distinct roots. |
| Every F ∈ ℚ[T] | `∀ F : Polynomial ℚ` including zero and constants |
| Equality δ(F(u)) = ∏ F(a_i) in L | `algebraMap ℚ L (δ (Polynomial.aeval u F)) = ∏ i : Fin d, Polynomial.aeval (a i) F` |
| If u is annihilated by monic integer polynomial | `(∃ H : Polynomial ℤ, H.Monic ∧ Polynomial.eval₂ (Int.castRingHom E) u H = 0) → ...`; integer coefficients are mapped by the canonical integer ring map and evaluation is valid for noncommutative E |
| Every coefficient of P is an integer rational | `∀ k : ℕ, ∃ z : ℤ, P.coeff k = (z : ℚ)` |

Both universes `u v` are explicit. The extension-field quantifier is universe
polymorphic; it is not restricted to the algebra's universe. Every variable and
instance is explicitly bound. The theorem uses no file-local notation or instance.

Dependency declarations read and used:

- def-weil-finite-dimensional-subspace: `FiniteDimensional`,
  Mathlib.LinearAlgebra.FiniteDimensional.Defs (abbreviation for `Module.Finite`).
- def-weil-pbc-mv-polynomial-ring: `MvPolynomial`,
  Mathlib.Algebra.MvPolynomial.Basic; the evaluation interface in
  Mathlib.Algebra.MvPolynomial.Eval was read, including `MvPolynomial.aeval` and
  `MvPolynomial.algHom_ext` in the recorded signature. Here evaluation at rational
  coordinates uses the same library's `MvPolynomial.eval`.
- def-weil-polynomial-ring: `Polynomial`, Mathlib.Algebra.Polynomial.Basic;
  degree and monicity use `Polynomial.natDegree` and `Polynomial.Monic`.
- Homogeneity is `MvPolynomial.IsHomogeneous`,
  Mathlib.RingTheory.MvPolynomial.Homogeneous: all supported monomials have degree d.
- Evaluating F at u or a root uses `Polynomial.aeval` from
  Mathlib.Algebra.Polynomial.AlgebraMap; this API accepts a noncommutative target
  algebra because its rational scalars are central.

Proof-only imports cover all already stated proof dependencies:
`Polynomial.eq_of_infinite_eval_eq` (Mathlib.Algebra.Polynomial.Roots),
`AlgebraicClosure` (Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure),
`Polynomial.Splits.eq_prod_roots` (Mathlib.Algebra.Polynomial.Splits),
`Polynomial.map_dvd_map'` (Mathlib.Algebra.Polynomial.FieldDivision), and
`IsIntegrallyClosed.eq_map_mul_C_of_dvd` (Mathlib.RingTheory.Polynomial.GaussLemma).
The remaining proof dependency lem-sfb-bounded-line-polynomial-interpolation has
neither Lean attachment nor Mathlib match in the read repository; it supplies
no object needed by this statement and has no recorded module to import. Its
role is retained in proof step 2 of the theorem docstring. No proof dependency
was removed from the node.

Read the local Milne PDF using pdftotext: Chapter I, Theorem 10.9 and Remark 10.11,
printed pp.46–47; the polynomial-function definition and Proposition 10.13,
printed pp.47–48; Lemma 10.22 and proof, printed p.51. Lemma 10.22 uses the
opposite sign convention and an unspecified sign. The accepted node's explicit
normalization and `t1-u` convention give the exact sign-free identity stated
here. The node's six-step argument, including its general integrality expansion,
is reproduced in the theorem docstring. No source-based correction was needed.

Edge cases checked mathematically before drafting:

- E need not be commutative or semisimple. `Ring E` leaves these cases available;
  the proof uses only polynomials in one element and central scalars.
- E = 0 is excluded exactly by the node's nonzero hypothesis. The existential
  basis index n is not separately required to be positive; a zero-dimensional
  basis cannot exist in a nontrivial rational algebra.
- The zero representing D cannot satisfy normalization at 1. Positive d rules
  out δ identically 1 and ensures δ(0) = 0.
- u = 0 is allowed, with P = X^d and the root formula δ(F(0)) = F(0)^d.
- F = 0 is allowed and gives two zero sides because d > 0. Nonzero constant F
  gives the expected d-th power. Repeated roots and a root 0 are allowed.
- A nonintegral u gets no unconditional integral-coefficient assertion.
  H may have arbitrary degree and repeated roots. H = 1 cannot annihilate u
  in nontrivial E. No assertion that P itself annihilates u is included.
- Coefficients above degree d are included in the integral-coefficient assertion;
  they are zero and are integer rationals.

Searches made for an existing statement (2026-10-23):

- msearch.py leanfinder: “A homogeneous multiplicative polynomial function on a
  finite dimensional rational algebra has a characteristic polynomial with a
  root product formula and integral coefficients for integral elements”. Eight
  hits included `Algebra.PowerBasis.norm_gen_eq_prod_roots`,
  `Polynomial.isIntegral_coeff_of_factors`, and `minpoly`; these concern specific
  norms or integrality and do not state the theorem for arbitrary δ.
- msearch.py leansearch: “A normalized homogeneous multiplicative polynomial
  function on a rational algebra satisfies a root product formula”. Eight hits
  included `Polynomial.Splits.aeval_eq_prod_aroots_of_monic`, product-of-roots
  formulas, and `Polynomial.homogenize_mul`; none concern arbitrary multiplicative
  homogeneous δ on an algebra.
- msearch.py loogle: `"PolynomialLaw", "mul"`. Eleven hits concern scalar actions
  and scalar-extension evaluation of polynomial laws, not the theorem.
- msearch.py grep: `multiplicative.*polynomial|polynomial.*multiplicative|homogeneous.*norm`
  in RingTheory. Two hits in LaurentSeries and MvPolynomial/Homogeneous; no match.
- rg of lean/WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json with the
  same concept pattern found unrelated homogeneous constructions and one
  reciprocal-polynomial product proof; no arbitrary polynomial-norm statement.
  Searching the item id in the upstream Lean source gave no hit. An exact name
  search across Mathlib, upstream, Sheaf and the upstream-name index found no
  collision with the proposed declaration.

Validation: scompile.py compiled both the sandbox module and its intended library
module cleanly (8.3 s and 8.8 s), with no error or non-sorry warning. deliver2.py --no-push also passed the server preflight and compilation
(OK, provisional dry-run commit 52d6cd6419d); nothing was pushed by that dry run.

No STATEMENT-DISPUTED flag and no node fault remain.

## Second reading by Q58

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
