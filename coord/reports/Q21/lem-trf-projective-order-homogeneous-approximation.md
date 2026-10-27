## Worker report

The module `Sheaf.RingTheory.ProjectiveOrderHomogeneousApproximation` states
`Hironaka.projective_order_homogeneous_approximation` with one `sorry`, and no
new definitions or proofs. Its docstring includes all six accepted proof steps.
The node statement and accepted split are unchanged. The inherited stage-1
BLOCKED ending does not apply: brief-stage2 §0 explicitly permits the stage-2
statement of a reviewed split that has no Lean record. The queue records stage 2.
No released repair note for this item was found.

Source read: Hironaka, Certain numerical characters of singularities (1970),
Lemma 18, printed pp.174–175, via the online PDF named in the node. PDF text
lines 903–974 give the approximation and both particular consequences. The PDF
screenshot service failed, but its extracted text was accessible. This source
matches the node's formulation. The archival PDF is still wanted in the DAG;
no repository literature files were changed.

Hypothesis and clause correspondence:

- The field k is `{k : Type u} [Field k]`, with explicitly bound universe u.
- Nonnegative r and b are `r b : ℕ`; B is
  `MvPolynomial (Fin (r + 1)) k` with ordinary total-degree homogeneity.
- The affine ring uses `{i : Fin (r + 1) // i ≠ 0}` for its r variables. This
  is a relabelling of t_1,...,t_r, with no restriction on r.
- The prime is the bundled `p : PrimeSpectrum` of that affine ring; L is
  `Localization.AtPrime p.asIdeal`; N is its `IsLocalRing.maximalIdeal`.
  `Localization.AtPrime.map_eq_maximalIdeal` identifies this N with pL.
- The canonical delta map is the existing `MvPolynomial.dehomogenizeX k 0`
  followed by `algebraMap _ (Localization.AtPrime p.asIdeal)`. It sends the
  zeroth variable to one, every other variable to its affine coordinate, and
  then a polynomial to its fraction with denominator one.
- The node defines order and initial forms as explanatory context. Neither is
  an additional hypothesis nor appears in this theorem's conclusion; power
  membership expresses all the order conditions the statement actually uses.
- `hd : 1 ≤ d` and `ht : 1 ≤ t` render the positive d and t.
- The b forms are `φ : Fin b → MvPolynomial ... k`, with degrees `e : Fin b → ℕ`.
  `he` gives both 1 ≤ e_j and e_j ≤ d; `hφ_ne` gives nonzero forms; `hφ` uses
  the existing `Hironaka.InOrderSpace r p (e j) (φ j)`, which includes degree-e_j
  homogeneity and membership of delta(φ_j) in N^(e_j).
- `hψ : ψ.IsHomogeneous d` is ψ ∈ B_d, including ψ=0.
- `happrox` is exactly the existence of b localized coefficients a_j with
  delta(ψ) minus their sum of multiples lying in N^t.
- The conclusion supplies `C : Fin b → MvPolynomial ... k`. Its first conjunct
  states degree d-e_j homogeneity, with natural subtraction valid since he
  includes e_j ≤ d. Zero polynomials are homogeneous of any such degree.
- Its next conjunct is delta(ψ − Σ C_j φ_j) ∈ N^t.
- The implication at `t = d` asserts membership of that same corrected form
  in `InOrderSpace r p d`, hence both its homogeneity and the required order.
- The last implication at `d < t` is ψ ∈ `Ideal.span (Set.range φ)`, the ideal
  (φ_1,...,φ_b)B. This is precisely the node's second particular consequence.
- All sums are over `Fin b`, so b=0 gives the empty sum zero and empty ideal.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`, `Field` (mathlib_match of def-weil-field).
- `Mathlib.Algebra.MvPolynomial.Basic`, `MvPolynomial`, `MvPolynomial.algHom_ext`,
  and `Mathlib.Algebra.MvPolynomial.Eval`, `MvPolynomial.aeval`: the recorded
  polynomial notion and its evaluation interface. The canonical delta uses
  the existing specialized `aeval` construction below.
- `WeilConjectures.RingTheory.GradedAlgebra.Standard`, `GradedAlgebra.IsStandard`:
  the recorded standard grading notion. For the fixed polynomial ring its
  degree parts are Mathlib's `MvPolynomial.IsHomogeneous`, defined by unit
  weights, without an extra arbitrary-grading hypothesis.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime` and
  `Localization.AtPrime.map_eq_maximalIdeal`: the recorded localization.
- `WeilConjectures.RingTheory.AssociatedGradedRing`, `Ideal.associatedGradedPiece`
  and `Ideal.associatedGraded`: the context for the node's initial-form language;
  its module is imported as the recorded statement dependency.
- `Sheaf.RingTheory.PermissibleBasisChartData`, `Hironaka.InOrderSpace`: already
  defines exactly U_d on this coordinate labelling. Added its existing landed
  node `def-trf-permissible-basis-chart-data` to stmt_deps, as §5 permits. This
  avoids a second definition of U_d.
- `WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous`,
  `MvPolynomial.dehomogenizeX`: its full definition is aeval, sending X_0 to 1
  and X_i to X_i for i≠0. Available publicly through PermissibleBasisChartData.

The four proof dependencies have no Lean records in the read snapshot. No
private proof imports are available for them; their node names and exact roles
are preserved in the proof docstring for stage 3. They are not statement
prerequisites and no missing statement notion results from their absence.

Edge cases checked before drafting: b=0 yields no generator hypotheses and all
empty sums/ideals zero; r=0 leaves only X_0 and the affine coefficient field;
ψ=0 allows all coefficients zero; e_j=d permits constant (including zero)
coefficients; t=d and t>d are both explicit conclusion clauses; positive
characteristic and nonrational/inseparable primes are unrestricted. In the r=0
case no nonzero positive-degree form lies in U_e, so nonempty families cannot
satisfy hφ; this is the mathematics, not an added exclusion. The theorem keeps
an arbitrary field universe and only finite coordinate and family indices.

Searches for existing statements/notions:

- msearch.py leanfinder: "Homogeneous approximation at a projective point: local
  ideal membership modulo a prime power admits homogeneous coefficients of
  complementary degrees". Eight hits: Proj chart ideal-membership lemmas and
  `Ideal.mem_span_pow_iff_exists_isHomogeneous`; none states approximation in
  a localized prime power by maximal-order homogeneous forms.
- msearch.py loogle: `"MvPolynomial.IsHomogeneous", "Ideal"`: zero hits.
- msearch.py grep: `dehomogen|homogeneous.*approxim|Hironaka` in RingTheory:
  zero hits.
- msearch.py leansearch: "Homogeneous approximation modulo powers of a localized
  prime ideal with homogeneous coefficients of complementary degrees": ordinary
  homogeneous localization and Proj chart membership hits, no exact statement.
- rg in lean/WeilConjectures and lean/Sheaf for
  `projectiveOrder|projective_order|dehomogen|HomogeneousApproximation|homogeneousApproximation`:
  found canonical dehomogenization maps, PermissibleBasisChartData.InOrderSpace,
  and the downstream PermissibleStandardBasisOneStep theorem. No existing
  declaration states Lemma 18. Searched the exact node id in WeilConjectures:
  no hit. Read the existing order-space and dehomogenization definitions in full.
- Read every stmt_deps node's statement and lean or mathlib_match. The dependency
  records give usable definitions; no dependency repair or new node is needed.

No statement fault or STATEMENT-DISPUTED issue found.

## Second reading by Q21

I performed a separate clause-by-clause rereading of the node and final module;
no other agent was started, per the dispatcher's instructions. The maintainer's
independent delivery review remains the independent mathematical review.
Checked that he supplies both degree bounds, hφ_ne keeps nonzero generators,
hφ supplies both clauses of U_e, hψ keeps ψ homogeneous even when zero, and
happrox quantifies actual localized coefficients. Rechecked every conclusion:
C has degree d-e_j, the same corrected form has precision t, its t=d case is
in U_d, and the t>d case places ψ in the original polynomial ideal. Checked
that neither a rational-point assumption nor characteristic/separability
condition slipped in, and that b=0 and r=0 are representable. No mismatch was
found on this rereading. No claims of an additional independent reader are made.
