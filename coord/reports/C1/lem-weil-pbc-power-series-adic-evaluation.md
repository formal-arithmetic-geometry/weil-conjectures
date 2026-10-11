## Worker report

Module `Sheaf.RingTheory.PowerSeriesAdicEvaluation` states
`MvPowerSeries.exists_unique_adic_evaluation`. Its only proof is `sorry`; it adds no
definitions, dependency modules, or nodes. The item's statement and dependencies are unchanged.

Hypotheses and objects, clause by clause:

- Commutative rings C and T: `{C : Type u} {T : Type v} [CommRing C] [CommRing T]`.
  The two universes are explicit and independent.
- Unital coefficient homomorphism: `(α : C →+* T)`.
- Ideal and I-adic completeness: `(I : Ideal T) [IsAdicComplete I T]`.
  This includes separatedness, by the recorded Mathlib definition.
- Number of variables n ≥ 0: `(n : ℕ)`; the variables are indexed by `Fin n`.
- Elements b_i in I: `(b : Fin n → T) (hb : ∀ i : Fin n, b i ∈ I)`.
- Power series ring: `MvPowerSeries (Fin n) C` from the dependency's Mathlib match.
- Existence of a unital ring map: `∃ E : MvPowerSeries (Fin n) C →+* T`.
- Restriction to α on constants: `∀ c : C, E (MvPowerSeries.C c) = α c`.
- Prescribed variables: `∀ i : Fin n, E (X i) = b i`.
- Continuity: `∀ N : ℕ, ∃ M : ℕ, ∀ F ∈ (Ideal.span (Set.range X)) ^ M,
  E F ∈ I ^ N`, with explicit types on X in the actual signature. This is exactly the
  ideal-power definition in the node, including N = 0.
- Uniqueness of the continuous ring map: every `E'` with the same constants, variables,
  and continuity satisfies `E' = E`. The explicit reduction formula is not imposed
  on E' as an additional hypothesis.
- Explicit value and uniqueness of its reductions: for each F and t, satisfying the
  displayed quotient equality for all N ≥ 1 is equivalent to `t = E F`.
  Taking t = E F gives every required reduction, and the converse gives uniqueness.
- The sum over |ν| < N is `MvPolynomial.eval₂ α b (F.truncTotal N)`.
  Mathlib `truncTotal` retains exactly those coefficients (`coeff_truncTotal_eq_ite`);
  `eval₂` is the sum of coefficient images times the products of variable powers
  (`MvPolynomial.eval₂_eq`). Finsupp degree is the sum of exponents. Its support product
  equals the full product over Fin n because omitted exponents are zero. Thus this
  notation gives precisely the finite sum in the node, not a box truncation.
- Reduction modulo I^N is equality after `Ideal.Quotient.mk (I ^ N)`.

Dependency declarations read and used:

- `def-weil-pbc-adically-complete-ring`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `IsAdicComplete`; read its class signature and the `IsHausdorff` and `IsPrecomplete`
  fields. It is the recorded complete and separated ring notion.
- `def-weil-pbc-multivariate-power-series`: `Mathlib.RingTheory.MvPowerSeries.Basic`,
  `MvPowerSeries`; read its definition `(σ →₀ ℕ) → R`, docstring, `C` and `X`.
  Imported transitively through `Mathlib.RingTheory.MvPowerSeries.Trunc`.
- Auxiliary existing operations: `MvPowerSeries.truncTotal` in the Trunc module,
  `MvPolynomial.eval₂` in `Mathlib.Algebra.MvPolynomial.Eval`, and
  `Ideal.Quotient.mk` available through the adic-completion module.

Edge cases checked mathematically before writing: n = 0 gives an empty variable family,
a zero variable ideal, and only the coefficient map; truncation below any positive N
retains the sole constant term. I = 0 gives ordinary constant-term evaluation with all
b_i zero. I = top and completeness force T to be the zero ring; no nontriviality
hypothesis excludes it. C or T may be the zero ring whenever the supplied unital map
exists. N = 0 in continuity has target ideal top and is harmless. No restriction on
characteristic, Noetherianity, or finite generation of I is imposed.

Searches (2026-10-11):

- `msearch.py ... leanfinder "finite variable formal power series evaluation into an
  I-adically complete ring unique continuous ring homomorphism"`: eight hits, including
  `MvPowerSeries.eval₂Hom`, `MvPowerSeries.eval₂_unique`, and univariate analogues.
  The multivariate candidates require uniform structures, CompleteSpace, T2Space,
  HasEval and linear topology, and do not state the algebraic reduction formula.
  Read their signatures and surrounding implementation; no exact match.
- `msearch.py ... loogle "MvPowerSeries.eval₂Hom, MvPowerSeries.eval₂_unique"`:
  successful query, zero hits.
- `msearch.py ... grep "eval₂Hom|eval₂_unique|trunc|totalDegree"
  RingTheory/MvPowerSeries`: successful query, 25 hits, including truncation API.
  Local rg and direct reads of Evaluation.lean confirm the candidates above.
- `rg` on the source's WeilConjectures and project's lean/Sheaf for
  `adic.*eval|eval.*adic|power-series-adic-evaluation|power-series-universal-property-complete`:
  no existing declaration of this statement; only mentions in proofs and unrelated
  p-adic module evaluation. Searching the exact item id in WeilConjectures gives no hit.
- Name collision search `adicEvaluation|exists.*adic.*eval|exists.*eval.*adic` in
  `dag/lean_names_upstream.json`, lean/Sheaf, and WeilConjectures gives no hit.

Source checked: the local Stacks source named in the node is absent on this machine.
Read the official [Tag 07NL](https://stacks.math.columbia.edu/tag/07NL) proof, which invokes
power-series universality, and [Tag 07NN](https://stacks.math.columbia.edu/tag/07NN), whose
proof uses the parameter substitution. The node explicitly provides the algebraic
universal property used in these proofs. The docstring reproduces its three proof
steps and the names of the proof dependencies; no mathematical correction is needed.
No STATEMENT-DISPUTED issue found.

Validation: server single-file compilation succeeded cleanly in 1.3 seconds.

## Second reading by C1

Independent verdict: the theorem says exactly the node's statement. No mismatch found;
no Lean, dependency, or node changes were necessary. This reading adds only this report.
The delivery has one module, no new definition nodes, no dependency modules, and no
statement_change; H12, H13 and the corrected-statement citer checks do not arise.

I opened the node and the Lean file together and made this object/hypothesis/conclusion
list before checking the implementation. Each item below passes:

- Objects C and T, arbitrary commutative rings: `{C : Type u} {T : Type v}` with
  `[CommRing C] [CommRing T]`. Neither is restricted to a field or a nonzero ring.
- Unital coefficient map alpha: `(α : C →+* T)` is precisely a ring homomorphism.
- Ideal I of T and complete separated I-adic target: `(I : Ideal T)` and
  `[IsAdicComplete I T]`. I read the recorded dependency
  def-weil-pbc-adically-complete-ring and Basic.lean's IsHausdorff, IsPrecomplete,
  IsAdicComplete signatures: this is completeness including separatedness, not merely
  existence of limits. No Noetherian, local-ring or finite-generation assumption occurs.
- Nonnegative integer n and n chosen elements of I: `(n : ℕ)`, `(b : Fin n → T)`,
  `(hb : ∀ i : Fin n, b i ∈ I)`. Fin n just relabels the n variables starting at zero.
- Source ring C[[X_1,...,X_n]]: `MvPowerSeries (Fin n) C`. I opened
  def-weil-pbc-multivariate-power-series and Basic.lean: the recorded definition is
  coefficient families `(Fin n →₀ ℕ) → C` with coefficientwise sums and Cauchy product.
  `MvPowerSeries.C` and `X` are its actual constants and variables, not private copies.
- Existence of E: `∃ E : MvPowerSeries (Fin n) C →+* T`.
- Constants fixed by alpha: `(∀ c : C, E (MvPowerSeries.C c) = α c)`.
- Variables assigned to b: `(∀ i : Fin n, E (X i) = b i)`.
- Continuity: the third conjunct is `∀ N : ℕ, ∃ M : ℕ, ∀ F ∈ J ^ M,
  E F ∈ I ^ N`, with J literally `Ideal.span (Set.range X)` on this source ring.
  Thus the quantifier order and the ideal-power condition are exactly the node's.
- Uniqueness of the continuous map: the fourth conjunct quantifies every ring map E'
  with those same three conditions and concludes `E' = E`. It does not require the
  reduction formula as an extra hypothesis or assert uniqueness only of a chosen map.
- Explicit formula for each series and uniqueness of the element determined by it:
  the final conjunct is `∀ F t, (∀ N, 1 ≤ N → mk (I ^ N) t =
  mk (I ^ N) (MvPolynomial.eval₂ α b (F.truncTotal N))) ↔ t = E F`.
  Substituting t = E F gives every reduction, while the forward implication is exactly
  uniqueness of the element having all those reductions. The quantifiers match.
- The finite sum over multiindices of total degree less than N: I read truncTotal's
  definition and coeff_truncTotal_eq_ite (Trunc.lean:325,334), plus the eval₂ definition
  and eval₂_eq' (Eval.lean:69,76). The former retains exactly degree < N; degree is
  the sum of exponents. The latter multiplies over all Fin n, giving b^nu, and sums
  the coefficient images. Missing zero coefficients contribute zero, so the polynomial
  support sum is exactly the displayed finite sum. Quotient.mk equality means equality
  modulo I^N. Neither rectangular truncation nor a weaker convergence statement is used.

Source reading: literature/stacks-project/more-algebra.tex is absent locally. I fetched
and read the official raw more-algebra.tex from
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex,
including the complete statements and proofs at labels
lemma-power-series-ring-over-Cohen-fs (Tag 07NL) and
lemma-embed-map-Noetherian-complete-local-rings (Tag 07NN), and checked the official
https://stacks.math.columbia.edu/tag/07NL and
https://stacks.math.columbia.edu/tag/07NN pages. The former invokes power-series
universality, and the latter substitutes phi(x_i)+y_i while retaining the coefficient
map. The node is the explicitly identified general algebraic universal property used
there, not the entire local Noetherian presentation theorem. Consequently that enclosing
lemma's local/Noetherian hypotheses and residue-characteristic cases are not extra
hypotheses of this evaluation statement. The general statement is valid for arbitrary
commutative coefficient rings and complete separated target rings.

Edge cases: Fin 0 is empty, its variable ideal is zero, and the source has just constants;
positive truncations retain them and the theorem determines E = alpha on those constants.
For I = 0 all b_i vanish and constant-term evaluation satisfies the statement. For I = top,
separatedness forces T to be the zero ring, which the binders permit. Zero C or T is
allowed whenever the supplied unital alpha exists. N = 0 in continuity is harmless
because I^0 = top; the reduction formula correctly starts at N = 1. Both ring universes
are explicit and independent, with no test-object quantification or implicit extra
universe. There is no characteristic restriction. Schemes and zero category objects
are not objects of this node, so their edge cases are inapplicable.

Independent searches, with phrases different from the first worker:

- msearch.py leanfinder "formal multivariate series substitution determined by residues
  modulo powers of an ideal": eight hits, mainly Weierstrass division and HasSubst.
  Read the substitution module's scope and HasSubst signature: the target is itself a
  power-series ring and its constant coefficients must be nilpotent. This does not
  supply arbitrary I-adically complete target evaluation.
- msearch.py loogle "MvPowerSeries, IsAdicComplete": one hit,
  MvPowerSeries.instIsAdicCompleteSpanRangeXOfFinite, asserting completeness of the
  source ring, not the evaluation universal property.
- msearch.py grep "IsAdicComplete|truncTotal|subst" RingTheory/MvPowerSeries:
  25 hits in substitution, truncation, and equivalence modules; no exact statement.
- Independent rg on WeilConjectures/ and lean/Sheaf for
  `adic.*(substitut|evaluat)|((substitut|evaluat).*(complet|adic))|truncTotal`
  found only references to this node in presentation proof docstrings and unrelated
  evaluation material. The exact declaration name and combined IsAdicComplete /
  MvPowerSeries search in dag/lean_names_upstream.json, lean/Sheaf, and the source
  produced no duplicate of the theorem.
- I opened Evaluation.lean's eval₂Hom (line 230) and eval₂_unique (line 283), including
  their surrounding instance binders. They use uniform and topological structures,
  CompleteSpace, T2Space, IsLinearTopology, continuous alpha and HasEval b, and do not
  state the algebraic quotient formula. They are proof ingredients, not existing exact
  declarations for this node. The delivered theorem introduces no duplicate notion.

Conventions and proof audit: all variables and universes are bound; the namespace is
MvPowerSeries, with no Sheaf prefix. All imports serve the statement: adic completeness,
total-degree truncation, and polynomial evaluation. The module and theorem docstrings
name Tags 07NL/07NN and carry the correct blueprint id. The theorem docstring follows
the node's three steps: use the complete universal property; show low coefficients
vanish in powers of the variable ideal; deduce continuity, treating N = 0 separately.
There is one theorem with only `by sorry`, no definitions, no hidden proof, and no hollow
data. The node's lean.statement is verbatim the file signature. No disputed statement.

Validation: independent single-file server compilation succeeded in 1.3 seconds, exit
code 0, with no warnings. The signature comparison returned True and all Lean lines are
at most 100 characters. deliver2.py --no-push printed OK: preflight and compilation pass.
