## Worker report

The module `Sheaf.FieldTheory.HenselianSimpleRootStability` states
`AddValuation.exists_open_coefficients_simple_root`. Its only theorem has proof
`sorry`; there are no new definitions, helper theorems, or new nodes. The copied
item changes only in `lean`. No statement correction or dispute is needed.

Hypotheses and conclusion, clause by clause:

- The field is `(F : Type u) [Field F]`. The additive valuation is
  `(v : AddValuation F Γ)` with `(Γ : Type v)
  [LinearOrderedAddCommGroupWithTop Γ]`. Here the ordered additive group is the
  finite part of `Γ`, with the usual extra `⊤` value at zero. Any ordered abelian
  group is represented by adjoining `⊤`; no rank or Archimedean restriction is
  imposed. Mathlib's `AddValuation.toValuation` is an equivalence given by the
  same data, using `Multiplicative Γᵒᵈ` for multiplicative notation.
- Nontriviality is `[v.toValuation.IsNontrivial]`: there is an element whose
  multiplicative value is neither zero nor one, equivalently whose additive
  value is neither infinity nor zero.
- The valuation ring is Mathlib's canonical `v.toValuation.valuationSubring`.
  Its membership condition is multiplicative value at most one, equivalently
  additive value at least zero. Henselianity is
  `[HenselianLocalRing v.toValuation.valuationSubring]`. This is the recorded
  local-ring notion of `def-weil-pbc-henselian-terminology`. In particular this
  hypothesis is on the valuation ring, not the ambient field (fields themselves
  are automatically henselian as local rings).
- `[TopologicalSpace F]` and `hvaltop` state exactly the specified valuation
  topology: for each `x`, `(𝓝 x).HasBasis (fun γ : Γ ↦ γ ≠ ⊤)
  (fun γ ↦ {y : F | γ < v (y - x)})`. The radii are all finite elements of the
  ambient ordered group. This preserves the discrete topology when the actual
  value group is bounded in that ambient group. Mathlib's `Valued` uses the
  actual value group for its basis, so its topology would silently exclude
  that expressly admitted case. No extra compatibility, continuity, or
  nondiscreteness assumption is used.
- `n : ℕ`, `hn : 1 ≤ n`, and `c : Fin n → F` are respectively the degree,
  positive-degree condition, and coefficient vector. The polynomial is written
  literally `X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)` throughout.
  Every exponent in the sum is below `n`, so it is the specified monic degree-n
  polynomial; an additional monicity hypothesis is unnecessary.
- `(a : F)`, `ha : (...).IsRoot a`, and `hda : (...).derivative.eval a ≠ 0`
  are the root, vanishing condition, and formal-derivative nonvanishing condition.
- `∀ U : Set F, IsOpen U → a ∈ U →` is every open neighbourhood of `a`.
- `∃ V : Set (Fin n → F), IsOpen V ∧ c ∈ V ∧ ...` is an open neighbourhood
  of the coefficient vector. The inferred topology on the function type
  `Fin n → F` is Mathlib's product topology.
- `∀ d : Fin n → F, d ∈ V → ∃ b : F, ...` quantifies over every perturbed
  coefficient vector, and supplies a root in the same field. Its three
  conjuncts are `b ∈ U`, vanishing of the explicitly written perturbed monic
  polynomial (`IsRoot b`), and nonvanishing of its derivative at `b`.
- No completeness, rank-one, discrete valuation, characteristic, or normed-field
  hypothesis occurs. Field and value-group universes are explicitly declared
  and independent; every variable is explicitly bound.

Dependencies read and used:

- `def-trf-valuation-ring`: Mathlib's `ValuationRing` and
  `ValuationRing.TFAE`, read in
  `Mathlib/RingTheory/Valuation/ValuationRing.lean:62-64,407-416`.
  The actual canonical valuation subring uses the existing
  `Valuation.valuationSubring` from
  `Mathlib.RingTheory.Valuation.ValuationSubring:439-447`, including its
  existing valuation-ring/local-ring instances. It is publicly imported.
- `def-weil-pbc-henselian-terminology`: public import
  `WeilConjectures.Mathlib.RingTheory.Henselian`; its module docstring records
  `HenselianRing`/`HenselianLocalRing` as the pair/local notions, and the recorded
  `IsStrictlyHenselianLocalRing` class at lines 121ff extends the latter. The
  complete `HenselianLocalRing` signature/docstring and `TFAE` were read in
  `Mathlib/RingTheory/Henselian.lean:102-153`. Strict henselianity is not asked
  for and is not assumed.
- `def-weil-polynomial-ring`: `Polynomial` and its docstring in
  `Mathlib/Algebra/Polynomial/Basic.lean:65-78`; also its degree/leading
  coefficient interface in `Degree/Defs.lean`. The public import
  `Mathlib.Algebra.Polynomial.Derivative` provides this existing polynomial
  type, `X`, `C`, evaluation, `IsRoot`, and formal derivative. The derivative
  definition at line 46 is coefficient multiplication by the exponent, not
  an analytic derivative.
- Proof dependency `lem-weil-pbc-henselian-local-root-lifting`: plain import
  `WeilConjectures.RingTheory.HenselianLocalRootLifting`. Its full signature
  and docstring were read: `IsLocalRing.idempotent_lifting_iff_monic_simple_root_lifting`
  compares unique finite-algebra idempotent lifting with monic simple residue
  root lifting. Its monic clause is precisely the input for the normalized
  reciprocal polynomial in proof step 4. No stronger nonmonic lifting interface
  is presumed. This is a proof import, not a second statement hypothesis.
- `Mathlib.Topology.Constructions` supplies the existing product topology and
  neighbourhood/basis infrastructure; no replacement topology is defined.

Sources and plan: read ILO XX 4.4 in the local PDF, PDF pages 379-380,
printed pages 373-374, including the dense henselian valued-field/Krasner
paragraph, and Stacks `algebra.tex`, `lemma-characterize-henselian` (Tag 04GG),
including its distinction between arbitrary-polynomial lifting (2) and the
monic definition. The current latest blueprint ancestor and its proof were
read. The module docstring identifies the sources; the theorem docstring gives
all five current DAG proof steps: finite valuation bounds, coefficient-error
estimates, integrality of the normalized polynomial, the monic reciprocal
polynomial and existing root lifting, then root location and derivative
nonvanishing. This is the currently reviewed reconstruction, not a recovered
historical theorem. The resolved stage-1 repair note and Q112 admission boundary
were read; no withdrawn comparison or discarded route is imported.

Edge cases checked before writing: n=1 gives `X + C(c 0)` and a derivative of
one; the normalization plan sets the top-degree error `E_n` to zero. n=0 is
excluded exactly by the node's n≥1 assumption. The zero coefficient vector and
a=0 are allowed; no divisions enter the theorem statement. All characteristics
are allowed: derivative nonvanishing is the simple-root condition even when
some integer coefficients vanish. Discrete ambient-value topology is retained
by `hvaltop`; for it a singleton coefficient neighbourhood suffices. Arbitrary
rank and noncomplete fields remain covered. No uniqueness or continuous choice
of the nearby root is asserted. There are no hollow data or hypotheses.

Searches actually run for this delivery:

- `msearch.py` LeanFinder: “A simple root over an arbitrary rank henselian
  valued field persists under small perturbations of the monic polynomial
  coefficients”. Eight hits: `HenselianLocalRing.is_henselian`, `hensels_lemma`,
  `HenselianRing.is_henselian`, `HenselianLocalRing.TFAE`, `Field.henselian`,
  `FirstOrder.Field.realize_genericMonicPolyHasRoot`,
  `WittVector.RecursionMain.root_exists`, `HenselianLocalRing`. None states
  arbitrary-rank coefficient stability: they give residue/approximate-root
  lifting, a p-adic special case, or existence of unrelated roots.
- `msearch.py` Loogle: `HenselianLocalRing, Polynomial.eval` returned
  `HenselianLocalRing.is_henselian` and `HenselianLocalRing.mk`; these expose
  the henselian local lifting condition, not topological coefficient stability.
- `msearch.py` grep: `simple.root|Krasner|HenselianLocalRing` in
  `RingTheory/Henselian.lean` returned five lines (23, 34, 92, 108, 114),
  concerning the simple-root terminology and henselian classes/field instance.
  The actual full class and TFAE definitions were read.
- Local `rg` of Mathlib for
  `simple.?root.*(stabil|perturb)|coefficient.*simple.?root|exists_open_coefficients_simple_root`
  found no matching theorem. Searches for `AddValuation`, `Valued`,
  `valuationSubring`, `IsNontrivial`, and their topology and henselian interfaces
  located the definitions discussed above.
- Local `rg -n -i` for
  `simple.?root.*(stabil|perturb)|coefficient.*simple.?root|exists_open_coefficients_simple_root|lem-per-henselian-simple-root-stability`
  across both `lean/WeilConjectures` and `lean/Sheaf` returned only two unrelated
  etale-residue-triple comments; no existing match. The required separate
  `grep -rn 'lem-per-henselian-simple-root-stability' lean/WeilConjectures`
  returned no match, and the name also has no upstream-name-index match.
- `scompile.py --source Sheaf.FieldTheory.HenselianSimpleRootStability`
  reported that the historical module is unavailable, consistent with
  `lean_removed`. Its old declaration was not reused.

Validation: `scompile.py Q04 lem-per-henselian-simple-root-stability` compiled
the final signature cleanly as both a sandbox module and its library module.
A first draft was revised before delivery to make valuation parameters explicit
and to retain the ambient-value topology case. All lines are at most 100
characters. The required dry-run and delivery wrapper recompile the delivered
file against the current published server build.

Required dry run completed successfully: the wrapper printed
`OK (dry run): commit 543c8751cd4 passes the preflight and compiles; nothing pushed`.
The packet has exactly the item module, its node record, and this report.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
