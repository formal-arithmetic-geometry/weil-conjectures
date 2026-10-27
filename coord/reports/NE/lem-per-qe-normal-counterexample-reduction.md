## Worker report

The module `Sheaf.RingTheory.QuasiExcellentNormalCounterexample` states
`exists_normal_counterexample_to_quasiExcellent_lifting` with one `sorry` and no
new definitions. The item statement and dependency lists are unchanged.

Source read: [Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings
(after Gabber)](https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf), Theorem
5.1, Step 1 (1-1)–(1-4), printed pp.7–8; Step 2 through (5.3), printed p.9;
Step 3. Step 1 supplies the principal counterexample, maximal bad quotient,
normalization, and universal catenarity. Step 2 supplies finite normalizations
and their completed local normal domains. The rational-algebra hypothesis is
the item's characteristic-zero specialization. The theorem docstring carries
all eight accepted DAG proof steps and their dependency ids without proving
any of them. No statement correction or disputed statement was needed.

Hypothesis and clause matching (the table uses B for `integralClosure R L`,
only as report shorthand; there is no file-local notation or definition):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A commutative ring | `(A : Type u) [CommRing A]` |
| A rational algebra | `[Algebra ℚ A]` |
| A Noetherian | `[IsNoetherianRing A]` |
| I an ideal and A complete for I | `(I : Ideal A) [IsAdicComplete I A]` |
| A/I quasi-excellent | `hquot : IsQuasiExcellent (A ⧸ I)` |
| A not quasi-excellent | `hA : ¬ IsQuasiExcellent A` |
| There exist a commutative Noetherian rational domain R and x | `∃ (R : Type u) (_ : CommRing R) (_ : Algebra ℚ R) (_ : IsNoetherianRing R) (_ : IsDomain R) (x : R), ...` |
| x nonzero and a nonunit | `x ≠ 0 ∧ ¬ IsUnit x` |
| R normal | `IsIntegrallyClosed R` together with the existential `IsDomain R` |
| R Nagata | `IsNagataRing R` |
| R complete for (x) | `IsAdicComplete (Ideal.span {x}) R` |
| R universally catenary | `IsUniversallyCatenary R` |
| R not quasi-excellent | `¬ IsQuasiExcellent R` |
| Every nonzero ideal quotient is quasi-excellent | `∀ K : Ideal R, K ≠ ⊥ → IsQuasiExcellent (R ⧸ K)` |
| Every finite field extension L/Frac(R) | `∀ (L : Type u) [Field L] [Algebra (FractionRing R) L] [Algebra R L] [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L], ...` |
| B is its integral closure | The actual canonical subalgebra `integralClosure R L` throughout |
| B finite as an R-module | `Module.Finite R (integralClosure R L)` |
| B normal | `∀ (p : Ideal B) [p.IsPrime], IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)` |
| B Nagata and universally catenary | `IsNagataRing B ∧ IsUniversallyCatenary B` |
| B complete for xB | `IsAdicComplete (Ideal.span {x}) B` as an R-module |
| B/xB quasi-excellent | `IsQuasiExcellent (B ⧸ Ideal.span {algebraMap R B x})` |
| Every maximal ideal n of B | `∀ (n : Ideal B) [n.IsMaximal], ...` |
| Maximal-ideal completion of B_n | `AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime n)) (Localization.AtPrime n)` |
| That completion a normal local domain | `IsDomain ... ∧ IsIntegrallyClosed ... ∧ IsLocalRing ...` |

The R-module completion in the B clause is exactly xB-adic completeness:
`(Ideal.span {x})^m • ⊤` in B consists of the multiples of x^m, hence agrees
with the powers of the extended principal ideal. The quotient explicitly uses
the image of x under the canonical `algebraMap R B`. The two algebra structures
on L and `IsScalarTower` require the R-action to be the composite through its
fraction field; these express the given field extension, not extra hypotheses.

Dependency declarations read and used:

- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`,
  `IsQuasiExcellent` and `IsUniversallyCatenary` (also read `IsExcellent`,
  `IsPrimeChain`, `IsSaturatedPrimeChain`, and `IsCatenaryRing`).
- `def-weil-pbc-adic-completion` and
  `def-weil-pbc-adically-complete-ring`:
  `Mathlib.RingTheory.AdicCompletion.Basic`, `AdicCompletion` and
  `IsAdicComplete`; ring operations supplied by the public import
  `Mathlib.RingTheory.AdicCompletion.Algebra`.
- `def-weil-pbc-integral-closure`:
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `integralClosure`.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
- `def-weil-pbc-nagata-ring`: `WeilConjectures.RingTheory.NagataRing`,
  `IsNagataRing`; read its N-2 dependency in
  `WeilConjectures.RingTheory.JapaneseDomain` as well.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`.
- `def-weil-pbc-normal-ring`:
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`, with `IsDomain` and the recorded prime-local inline
  form for a general normal ring. No duplicate normal-ring predicate.

All stated proof-dependency modules are plain imports. The proof dependencies
`lem-per-adic-nagata-lifting`, `lem-per-adic-normal-completion-lifting`,
`lem-per-qe-finite-surjective-descent`, `lem-per-qe-jacobson-g-ring-criterion`,
`lem-per-quasi-excellent-finite-type-stability`, and
`lem-per-ratliff-formal-catenarity` currently have no recorded declarations and
therefore no module to import. Their accepted proof steps remain in the
docstring. All eight statement-dependency modules are public imports.

Edge cases checked before writing:

- I = 0 makes the quotient premise incompatible with the negative premise;
  neither this case nor the zero ring is excluded by an added hypothesis.
- I = A forces the complete ring to be zero, so cannot supply a counterexample.
- K ranges over all nonzero ideals, including the unit ideal. There is no
  unintended `K ≠ ⊤` restriction and no demand on the zero ideal quotient.
- x = 0 and units are explicitly excluded as the node requires. No assumption
  that R is local or semilocal is imposed.
- L = Frac(R), the degree-one extension, is allowed; there is no properness,
  separability, or algebraic-closedness restriction.
- Every maximal ideal of B is covered, with no chosen maximal ideal or imposed
  contraction. `n.IsMaximal` supplies primeness for `Localization.AtPrime n`.
- Universes are explicitly bound. R and its quotient/normalization constructions
  fit in the universe of A; finite extensions have same-universe models, as in
  the recorded `IsN2` interface. This avoids an independently smaller test
  universe. All properties are invariant under algebra isomorphism.

Searches made on 2026-10-24, before writing:

1. `msearch.py ... leanfinder` query: "A counterexample to lifting quasi
   excellence reduces to a principal adically complete normal Nagata
   universally catenary domain with all nonzero quotients quasi excellent".
   Eight hits: Henselian rings, adic completeness, quasi-finiteness, and
   Dedekind completion results; none is this reduction.
2. `msearch.py ... loogle` query: `"IsQuasiExcellent", "IsNagataRing"`.
   Zero hits.
3. `msearch.py ... grep` query:
   `quasi.?excellent|normal.counterexample|counterexample.reduction`.
   Zero Mathlib hits.
4. `msearch.py ... leansearch` query: "A complete Noetherian rational algebra
   which is not quasi excellent but whose quotient is quasi excellent reduces
   to a normal Nagata domain". Eight hits about Noetherian quotients,
   Noether normalization, and integral closure; none matches.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
   `normal.counterexample|counterexample.reduction|lem-per-qe-normal-counterexample-reduction`:
   only the downstream proof docstring in `QuasiExcellentCompletePair.lean`
   mentions the node; no declaration states it. A separate name search for
   `normalCounterexample|normal_counterexample|exists_normal.*counterexample|exists_normal.*quasiExcellent`
   in both libraries and Mathlib returned no matches. Searching
   `IsQuasiExcellent|IsUniversallyCatenary` found the recorded definitions and
   other unrelated consumers, which were read rather than redefined.

Validation: `scompile.py NE lem-per-qe-normal-counterexample-reduction` compiled
both sandbox and final library-module modes successfully (3.3 s and 2.2 s),
without errors or unexpected warnings. The final comment reflow is checked
again by the delivery dry run. No global build or direct Git operation was run.

## Second reading by NE

I reread the source, node, and generated declaration in a separate pass in this
session. This is an in-session second pass, not a claim of an independent
worker; the maintainer's independent delivery review remains to be done.
The table above was checked against the actual final signature. In particular,
R has an existential domain instance (so `IsIntegrallyClosed R` means normal
domain), B uses the dependency's full prime-local normal-ring form, xB in the
quotient is generated by the image of the same x, and the final completion
uses the maximal ideal of B_n rather than n as an ideal of B. The explicit
local-ring conjunct matches "local" in the node. Non-quasi-excellence and
all finite extensions are inside the same existential witness for R and x.
No hypothesis or clause was dropped or added. No correction, dependency
repair, helper definition, or new node was needed. Reflowed the proof docstring
to avoid splitting dependency ids across lines; no Lean signature changed.
