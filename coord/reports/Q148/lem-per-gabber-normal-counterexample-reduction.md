## Worker report

Item: `lem-per-gabber-normal-counterexample-reduction` (Q148, stage 2, 2026-10-24).
Module: `Sheaf.RingTheory.GabberNormalCounterexample`.
Declaration: `exists_gabber_normal_counterexample`.
The module states the node with one `sorry` theorem, no definitions and no additional
lemmas. The complete accepted eight-step proof, including its dependency identifiers,
is in the theorem docstring. Only the item's `lean` field changes.

Source read: [Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings
(after Gabber)](https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf), Theorem 5.1,
Step 1 (1-1)–(1-4), printed pp. 7–8, and the discussion of finite normalizations,
(5.3), printed p. 9, and Step 3. The theorem has no characteristic assumption.
The source's reductions give the node's principal bad normal Nagata domain;
the finite-normalization clauses use the same permanence results and normal
completion lifting, as detailed in the node's accepted proof.
WANTED: a maintained bibliographic copy of `kurano40.pdf` under project literature;
the source was read online, and the read-only literature tree was not modified.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| A commutative ring | `(A : Type u) [CommRing A]` |
| A Noetherian | `[IsNoetherianRing A]` |
| ideal I | `(I : Ideal A)` |
| A I-adically complete | `[IsAdicComplete I A]` (includes separatedness) |
| A/I quasi-excellent | `hquot : IsQuasiExcellent (A ⧸ I)` |
| A not quasi-excellent | `hA : ¬ IsQuasiExcellent A` |
| existence of a commutative ring R | `∃ (R : Type u) (_ : CommRing R), ...` |
| R a domain | existential `(_ : IsDomain R)` |
| R Noetherian | existential `(_ : IsNoetherianRing R)` |
| R normal domain | the domain binder together with `IsIntegrallyClosed R` |
| R Nagata | `IsNagataRing R` |
| x in R | `∃ x : R, ...` |
| x nonzero | `x ≠ 0` |
| x nonunit | `¬ IsUnit x` |
| R (x)-adically complete | `IsAdicComplete (Ideal.span {x}) R` |
| R universally catenary | `IsUniversallyCatenary R` |
| R not quasi-excellent | `¬ IsQuasiExcellent R` |
| every nonzero ideal K | `∀ K : Ideal R, K ≠ ⊥ → ...` |
| R/K quasi-excellent | `IsQuasiExcellent (R ⧸ K)` |
| every finite field extension L/Frac(R) | `∀ (L : Type (max u v)) [Field L] [Algebra (FractionRing R) L] ... [FiniteDimensional (FractionRing R) L], ...` |
| B_L the integral closure of R in L | the actual Mathlib subalgebra `integralClosure R L` throughout |
| B_L finite as R-module | `Module.Finite R (integralClosure R L)` |
| B_L normal | `IsIntegrallyClosed (integralClosure R L)`, with domain structure already provided as a subalgebra of a field |
| B_L Nagata | `IsNagataRing (integralClosure R L)` (also includes Noetherianity) |
| B_L universally catenary | `IsUniversallyCatenary (integralClosure R L)` |
| B_L (x)-adically complete | `IsAdicComplete ((Ideal.span {x}).map (algebraMap R (integralClosure R L))) (integralClosure R L)` |
| B_L/xB_L quasi-excellent | `IsQuasiExcellent ((integralClosure R L) ⧸ (Ideal.span {x}).map (algebraMap R (integralClosure R L)))` |
| every maximal ideal n of B_L | `∀ (n : Ideal (integralClosure R L)) [n.IsMaximal], ...` |
| localization (B_L)_n | `Localization.AtPrime n`; maximality supplies primality |
| completion at its maximal ideal | `AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime n)) (Localization.AtPrime n)` |
| that completion a normal local domain | three conjuncts `IsLocalRing`, `IsDomain`, `IsIntegrallyClosed` on that very completion |

The extension binder includes `[Algebra R L] [IsScalarTower R (FractionRing R) L]`:
this specifies exactly the canonical composite action, rather than an unrelated
R-algebra structure. Each such composite exists, and the scalar-tower condition
forces its algebra map to be the composite. It is not an additional mathematical
hypothesis on a field extension. The same R, x and integral closure are used in
every clause; no arbitrary replacement ring or map is chosen.

Universes: `u v` are declared explicitly and `autoImplicit` is false. R can be in
`Type u`, because the source constructs it from quotients of A and normalization
inside their fraction fields. L ranges over `Type (max u v)`, so finite-extension
tests are never confined to an independent universe smaller than R. Taking v = 0
includes the identity extension `FractionRing R`; other v allow larger carriers.

Dependency declarations read and used (the sources and docstrings were opened):

- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`,
  `IsQuasiExcellent`, `IsUniversallyCatenary` (the module also defines `IsExcellent`).
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`; its ring structure is imported from
  `Mathlib.RingTheory.AdicCompletion.Algebra`.
- `def-weil-pbc-adically-complete-ring`: the same Basic module, `IsAdicComplete`.
- `def-weil-pbc-integral-closure`: `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`,
  `integralClosure` with carrier exactly the integral elements.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
  Its residue-field and fibre clauses are not needed in this statement.
- `def-weil-pbc-nagata-ring`: `WeilConjectures.RingTheory.NagataRing`, `IsNagataRing`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (Noetherian module over itself).
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`, with the standard `IsDomain` class. All rings whose normality
  is asserted here are domains: R by its existential binder, B_L as a field
  subalgebra, and the completion by the explicit `IsDomain` conjunct. Thus the
  normal-domain form of the recorded interface applies without a new predicate.

Proof dependencies with recorded project declarations are imported plainly:
`Sheaf.RingTheory.QuasiExcellentNagata` (`isNagataRing_of_isQuasiExcellent`),
`Sheaf.RingTheory.AdicCompleteSubideal` (`IsAdicComplete.of_fg_subideal`),
`Sheaf.AlgebraicGeometry.GRingAffineCover`
(`AlgebraicGeometry.isGRing_of_affine_open_cover`),
`Sheaf.AlgebraicGeometry.JTwoAffineCover` (`AlgebraicGeometry.j2_of_affine_open_cover`),
`WeilConjectures.RingTheory.CompletionDimension` (`RingTheory.completion_dimension`),
`WeilConjectures.RingTheory.FiniteModuleComplete`
(`finite_module_complete_over_complete_noetherian`),
`WeilConjectures.RingTheory.FiniteOverNagata` (`finite_over_nagata_is_nagata`),
`WeilConjectures.RingTheory.GRingPairsOfPrimes` (`isGRing_iff_pairsOfPrimes`),
and `WeilConjectures.RingTheory.NagataDomainN2` (`isN2_of_isNagataRing_domain`).
The Japanese-domain definition comes through the public Nagata import.
Mathlib proof dependencies are included by the imports of localization integral,
submodule and iterated-localization modules, Noetherian.Basic, and
AlgebraicGeometry.Noetherian; the other relevant Mathlib files are already public
statement imports (completion, integrally closed rings, and prime spectrum).

These six proof nodes currently have no recorded Lean declaration and therefore
supply no import: `lem-per-adic-nagata-lifting`,
`lem-per-adic-normal-completion-lifting`, `lem-per-qe-finite-surjective-descent`,
`lem-per-qe-jacobson-g-ring-criterion`,
`lem-per-quasi-excellent-finite-type-stability`, and
`lem-per-ratliff-formal-catenarity`. They are proof inputs only; none is needed to
form this statement. No statement prerequisite is missing or unusable.

Edge cases checked before writing:

- No Q-algebra, characteristic-zero or separability assumption occurs; positive
  characteristic and inseparable finite extensions remain included.
- I = 0 makes the two quasi-excellence hypotheses contradictory, without adding
  `I ≠ ⊥`. I = top and the zero ring are not excluded by new assumptions either.
- R is genuinely a nontrivial domain; the nonzero nonunit clauses on x are separate.
- K = top is included, so the conclusion includes the zero quotient. K = bottom
  alone is excluded, exactly as in the node.
- The identity extension L = Frac(R) is included (v = 0), and its integral closure
  is R by normality. No positive-degree or nontrivial-extension condition appears.
- The completion ideal is the maximal ideal of the localized ring, not x times
  the localization. There is no restriction to maximal ideals lying above a
  preselected maximal ideal of R.
- Completeness on B_L uses the extended principal ideal, precisely xB_L. B_L's
  normal-domain presentation is equivalent to normality because it is already a
  subring of a field. No separability, excellence, or regularity is added.

Searches made with the prescribed `batch2/msearch.py` wrapper:

1. `leanfinder`: “A counterexample to lifting quasi excellence from an
   ideal-adically complete Noetherian ring reduces to a normal Nagata universally
   catenary domain with finite normalizations”. Eight hits: Zariski's Main
   Property, DVR TFAE, quasi-finiteness, flatness of adic completion, quotient
   induction, etc.; none states the reduction.
2. `loogle`: `"IsAdicComplete", "IsNoetherianRing"`. Zero hits.
3. `grep`, Mathlib/RingTheory: `quasi.?excellent|counterexample|NagataRing`.
   Three unrelated comments in graded-algebra radical and polynomial Wronskian
   files; no match.
4. `leansearch`: “complete Noetherian ring quasi excellent quotient normal
   Nagata domain counterexample reduction”. Eight hits concerning Noetherian
   rings, quotients, module finiteness, normal field extensions and local
   Artinian quotients; no reduction theorem.
5. Direct `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the item identifier,
   `normalCounterexample|normal_counterexample|counterexampleReduction|
   counterexample_reduction`, and later the proposed declaration name: no
   existing declaration. The broader RingTheory quasi-excellence search finds
   the definitions and the characteristic-zero complete-pair theorem, which
   has a different statement; it is not imported or restated here.
   `grep -rn` for the exact item identifier in WeilConjectures also gives no hit.

No new nodes, dependency repairs, statement correction, or STATEMENT-DISPUTED
finding is needed. The record's signature is copied verbatim from the theorem.

Validation: the prescribed `scompile.py Q148
lem-per-gabber-normal-counterexample-reduction <module>` compiled the sandbox
and library-module forms cleanly (4.3 s and 5.5 s), with no unexpected warnings.
The dry run and delivery results are recorded below when completed.

## Second reading by Q148

This is the author's second pass, not a claim of independent review: the dispatch
forbids starting other agents and assigns independent delivery review to the
maintainer. I reopened the node and finished Lean module together. The table
above matches every hypothesis and conclusion; in particular I rechecked the
scope of x over every finite extension, the canonical scalar tower, all nonzero
ideals including top, and the maximal-ideal rather than x-adic local completion.
The original statement and dependency lists are unchanged. No mathematical
mismatch was found. The docstring wrapping was adjusted so dependency IDs are
not split at hyphens; no declaration or signature changed after clean compilation.

Dry run: `deliver2.py Q148 lem-per-gabber-normal-counterexample-reduction --no-push`
printed `OK (dry run): commit 8bab113f293 passes the preflight and compiles;
nothing pushed`. The exact staged set was the single module, item node, and
worker report. A final local record check confirms that `lean` is the only
changed node field, its signature matches the file verbatim, there is exactly
one sorry, and every Lean line is at most 100 characters.
