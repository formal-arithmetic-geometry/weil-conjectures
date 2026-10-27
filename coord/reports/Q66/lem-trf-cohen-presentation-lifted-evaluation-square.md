## Worker report

Item: lem-trf-cohen-presentation-lifted-evaluation-square, Q66, stage 2.

The module Sheaf.RingTheory.CohenPresentationLiftedEvaluationSquare states
MvPowerSeries.cohen_presentation_lifted_evaluation_square. Its only proof is `sorry`.
There are no new definitions, dependency repairs, statement corrections or new nodes.
Only `lean` changes in the copied node. Every variable and universe is explicit and
`autoImplicit` is false.

Source checked: literature/stacks-project/dpa.tex, lemma-ci-well-defined, Tag 09PZ,
first and third proof paragraphs. The third paragraph supplies the continuous lift
and the enlarged square. This item stops before that paragraph's surjectivity claim.
The current blueprint's lem-trf-local-term-locality.proof.md was also read: the
retained descendant is an algebraic tool, not a new claim about that unit's trace
statement. There is no released repair note for this item. The requested example
CompactObject.lean currently contains only a withdrawal notice; its node records
Mathlib's CategoryTheory.IsCompactObject. The module follows the current module-mode
header and the other live statement modules instead.

Hypotheses, individually:

- A, R and Λ have independent universes u, v, w and `CommRing` instances.
- The Noetherian hypotheses on A and R are `[IsNoetherianRing A]` and
  `[IsNoetherianRing R]`.
- Their local-ring hypotheses are `[IsLocalRing A]` and `[IsLocalRing R]`.
- Their maximal-ideal completeness hypotheses are the two `IsAdicComplete`
  binders. This definition includes separatedness; it is not mere precompleteness.
- The map r is `R →+* A`; `[IsLocalHom r]` renders locality and `hr` renders
  surjectivity. For local commutative rings, reflecting units is equivalent to
  sending the maximal ideal into the target maximal ideal: the maximal ideal
  consists of nonunits, and every ring hom sends units to units.
- The nonnegative residue characteristic is `p : ℕ`, with
  `[CharP (IsLocalRing.ResidueField A) p]`. No assumption p>0 excludes characteristic zero.
- The two allowed coefficient-ring cases are exactly `hΛ`:
  `(p = 0 ∧ IsField Λ ∧ CharZero Λ) ∨ (0 < p ∧ IsCohenRing p Λ)`.
  The first is a characteristic-zero field, the second a Cohen ring with the
  specified residue characteristic. No residue-field isomorphism is assumed.
- `n : ℕ` includes zero, and T₀ is the actual Mathlib ring
  `MvPowerSeries (Fin n) Λ` throughout, rather than a free ring parameter.
- `c₀ : MvPowerSeries (Fin n) Λ →+* A`, `[IsLocalHom c₀]` and `hc₀`
  give the fixed local surjection in the statement.
- The universal finite tuple is `s : ℕ`, `b : Fin s → R` and
  `hb : Ideal.span (Set.range b) = RingHom.ker r`. Thus it is precisely a generating
  tuple for the kernel, with no minimality or nonzero-generator assumption.

Conclusions, individually:

- T is exactly `MvPowerSeries (Fin s) (MvPowerSeries (Fin n) Λ)`.
- The existential ring equivalence e identifies the flat ring on variables
  `Fin n ⊕ Fin s` with T. Its equation
  `coeff α (coeff ν (e G)) = coeff (Finsupp.sumElim α ν) G` specifies regrouping
  coefficients, rather than an arbitrary isomorphism. The two summands label the
  x and y blocks in order, equivalently n+s variables. The existential e is theorem
  data asserting the stated identification, not a definition selected from `sorry`.
- The existential `IsLocalRing Λ` exposes the locality already implied by hΛ;
  it adds no hypothesis. The two existential `IsRegularLocalRing` instances give
  precisely Noetherian regular locality of T₀ and T, before referring to their
  maximal ideals. Their proof instances are propositions, so no arbitrary data
  construction is being postulated.
- The two `IsAdicComplete` conjuncts give maximal-ideal completeness of T₀ and T.
- The first maximal-ideal equation is `(maximalIdeal Λ).map C ⊔ span (range X)`.
- The second is the image of `maximalIdeal Λ` under the composite constant-series
  inclusions, joined with the ideal spanned by the union of `C (X i)` for all
  x variables and `X j` for all y variables. Thus it is exactly
  m_Λ T + (x₁,...,xₙ,y₁,...,yₛ).
- π is the concrete Mathlib `constantCoeff` ring hom on the outer y-series ring.
  Its two conjuncts assert `Function.Surjective` and `IsLocalHom`.
- Existential ring homs f and h have the specified domains and target R.
  `IsLocalHom f ∧ IsLocalHom h` gives both locality clauses.
- `r.comp f = c₀` is rf=c₀.
- `h.comp C = f` is restriction to the constant-y coefficient ring.
- `∀ j : Fin s, h (X j) = b j` is the prescribed image of each y variable.
- `r.comp h = c₀.comp constantCoeff` is the displayed commuting square.
- For every F, N and `1 ≤ N`, equality of the two images under
  `Ideal.Quotient.mk (maximalIdeal R ^ N)` is congruence modulo m_R^N.
  `MvPolynomial.eval₂ f b (F.truncTotal N)` is exactly the finite sum
  of f(a_ν) b^ν over |ν|<N: truncTotal retains precisely those monomials and
  eval₂ evaluates their coefficients by f and variables by b. This is the
  project's recorded POWER SERIES convention, not a rectangular truncation.
- There is no claim that h is surjective, nor an additional continuity or
  uniqueness clause for h.

Dependency declarations read and used:

- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing` (every ideal finitely generated).
- Mathlib.RingTheory.AdicCompletion.Basic: `IsAdicComplete` (Hausdorff and precomplete),
  together with its completion-map interpretation in the dependency record.
- WeilConjectures.RingTheory.CohenRing: `IsCohenRing` (primality, domain, DVR,
  maximal ideal generated by p, completeness).
- Mathlib.RingTheory.MvPowerSeries.Basic: `MvPowerSeries`, `C`, `X`, `coeff`,
  `constantCoeff`; the dependency's actual coefficient-family ring.
- def-weil-regular-scheme: its unchanged ring-clause mathlib_match is
  `IsRegularLocalRing`, Mathlib.RingTheory.RegularLocalRing.Defs. This is the
  clause used here; the scheme declaration AlgebraicGeometry.IsRegularScheme in
  Sheaf.AlgebraicGeometry.IsRegularScheme was also read and its module imported
  as the recorded statement dependency requires. No scheme is introduced here.
- Mathlib.RingTheory.MvPowerSeries.Trunc: `truncTotal`; Mathlib's
  `MvPolynomial.eval₂` supplies the finite evaluated polynomial.
- The four stated non-elementary proof dependencies are imported without `public`:
  WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete,
  `MvPowerSeries.power_series_field_cohen_regular_complete`;
  WeilConjectures.RingTheory.FieldCohenPowerSeriesFormallySmooth,
  `MvPowerSeries.field_cohen_power_series_formally_smooth`;
  WeilConjectures.RingTheory.FormallySmoothAdicLiftIntoComplete,
  `Algebra.FormallySmoothAdic.exists_lift_into_complete`;
  WeilConjectures.RingTheory.PowerSeriesAdicEvaluation,
  `MvPowerSeries.exists_unique_adic_evaluation`.
  Their full signatures and proof docstrings were read. The main declaration's
  docstring supplies all six DAG proof steps, including closedness and the
  exponent-one lifting hypotheses.

Edge cases checked before writing and again after compilation:

- n=0: the inner series ring is canonically Λ; no x generators occur.
- s=0 and zero kernel: span of the empty range is zero, the only outer exponent
  is zero, h restricts to f and π is the constant-coefficient identity under the
  empty-variable equivalence. No positivity requirement is placed on s.
- s>0 with zero or redundant generators: allowed by hb, and evaluation gives zero
  or repeated variable images. No independence assumption was added.
- Characteristic zero and positive characteristic both appear in hΛ. A coefficient
  field has zero maximal ideal; its image term vanishes in each ideal formula.
- r=id: a tuple generating zero is allowed; the commuting relations remain valid.
- N=1: truncTotal keeps precisely the constant y term, giving the correct first
  congruence. N=0 is deliberately outside the asserted congruence clause.
- Zero rings are excluded exactly by the local-ring hypotheses already in the
  node; the coefficient choices are also nonzero. Universes are independent,
  and there is no quantification over a smaller test-ring universe.

Searches made (prescribed msearch wrapper and direct source searches):

- leanfinder, "Lift a fixed Cohen power series presentation through a complete local
  surjection and adjoin kernel variables with evaluation congruences": eight hits,
  including AdicCompletion.kerProj, Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete,
  and IsAdicComplete.liftAlgHom. None states this adic Cohen square and its congruence;
  the formal-smoothness hits assume algebraic formal smoothness instead.
- loogle, "MvPowerSeries, IsLocalHom": only MvPowerSeries.map.isLocalHom,
  which concerns coefficientwise maps with the same variable set, not this square.
- grep, `(Cohen|cohen).*(lift|presentation)|sum.*degree.*eval|eval.*trunc`, RingTheory:
  only PowerSeries.eval₂_trunc_eq_sum_range, for univariate truncation; no match.
- leansearch, "Regroup multivariate power series in two finite sets of variables
  into iterated multivariate power series": polynomial sumRingEquiv and sumAlgEquiv,
  plus the MvPowerSeries type and commute_X. No multivariate series regrouping theorem.
- rg over lean/WeilConjectures and lean/Sheaf for this node id and
  `Cohen.*(lift|square)|cohen.*(lift|square)`, plus the intended declaration name:
  coefficient-ring lifts, related presentation-independence proofs and unrelated
  geometric Cohen lifts; no existing statement of this item.
- Read Mathlib MvPowerSeries/Equiv.lean: only empty, option, successor-variable
  and completion equivalences, not the requested two-block regrouping statement.
  The regrouping identification is included in this theorem with its coefficient
  characterization; no new notion or duplicate definition is needed.
- Checked dag/lean_names_upstream.json for the new declaration name: no match.

Validation: scompile.py compiled this file separately in sandbox and final-library
module mode against the published live build, each in 2.0 s, with no errors or
unexpected warnings. Delivery dry-run results are recorded below after execution.

## Second reading by Q66

A separate rereading of the node and the completed file was performed by this same
worker; no other agent was started, as the dispatcher brief explicitly prohibits it.
The maintainer's independent review remains the independent reading. This section
records the actual self-check rather than attributing it to an invented second worker.

Compared every binder and conjunct with the mapping above. In particular, the
coefficient characteristic is tied to the residue characteristic of A, both f and h
are local, the fixed presentation c₀ is preserved, hb expresses generation rather
than merely membership, both maximal-ideal formulas include coefficient generators,
and the total-degree congruence is in R rather than in A. The regrouping equation
has x-index α inside y-index ν, and sumElim places α in the first summand and ν
in the second, matching the stated order. Confirmed no assertion of surjectivity
of h, no exclusion of empty tuples, no extra field/residue-field isomorphism,
and no definition containing sorry. No mismatch requiring a change was found.

Delivery validation: `deliver2.py Q66 lem-trf-cohen-presentation-lifted-evaluation-square
--no-push` returned OK: the delivery passes maintainer preflight and per-file compilation.
