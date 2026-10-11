## Worker report

The module `lean/Sheaf/RingTheory/PowerSeriesN2.lean` states
`MvPowerSeries.noetherian_domain_isN2`, with its sole proof `sorry`.
No definitions, extra nodes, dependency modules, or statement corrections are needed.

Hypothesis and conclusion correspondence:
- A commutative ring R: `(R : Type u) [CommRing R]`.
- R is an integral domain: `[IsDomain R]`; in particular the zero ring is excluded,
  just as in the node and source.
- R is Noetherian: `[IsNoetherianRing R]`.
- R is N-2: `(hR : IsN2 R (FractionRing R))`. The fraction field is the canonical
  Mathlib fraction field, so this introduces no further mathematical hypothesis.
- The one-variable power series ring: `MvPowerSeries (Fin 1) R`, exactly the n=1
  specialization of the recorded multivariate-power-series dependency.
- That ring is Noetherian: the first conjunct
  `IsNoetherianRing (MvPowerSeries (Fin 1) R)`.
- That ring is an integral domain: the second conjunct
  `IsDomain (MvPowerSeries (Fin 1) R)`.
- That ring is N-2: the third conjunct
  `IsN2 (MvPowerSeries (Fin 1) R) (FractionRing (MvPowerSeries (Fin 1) R))`.
  Unfolding the recorded IsN2 definition quantifies over every field L algebra over
  this fraction field with `FiniteDimensional`, and every compatible R[[x]]-algebra
  structure (`IsScalarTower`), and concludes
  `Module.Finite (MvPowerSeries (Fin 1) R) (integralClosure (MvPowerSeries (Fin 1) R) L)`.
  Thus both the finite-extension clause and the integral-closure finiteness clause
  are present, including the required composite algebra map.

Dependency declarations read and used:
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.RingTheory.JapaneseDomain`: `IsN2`, including its complete definition.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries` (imported transitively
  through `Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors`).
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` (via JapaneseDomain).
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure` (via IsN2).
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite` (via IsN2).
The latter three notions are used inside the dependency's existing IsN2 definition,
so no independent restatement or duplicate definition is introduced.
`FractionRing` comes from `Mathlib.RingTheory.Localization.FractionRing`, imported
by JapaneseDomain. The existing theorem `NoZeroDivisors.to_isDomain` is registered
locally as an instance: combined with the multivariate no-zero-divisors instance
and its Nontrivial instance, this supplies the domain structure required to type IsN2.
This is an existing Mathlib conversion, not an additional theorem or hypothesis.

Edge cases: arbitrary characteristic, including positive characteristic and
inseparable finite extensions, is allowed; there is no normality assumption on R.
R may be a field. The identity field extension is included by IsN2, so N-1 is not
lost. The index type is exactly Fin 1: no accidental zero-variable case or arbitrary
number of variables is imposed. The coefficient ring has arbitrary explicitly bound
universe u. The canonical fraction field has the same universe; as in the recorded
IsN2 definition, all finite extensions have representatives in that universe.
The zero ring fails the domain hypothesis and is correctly outside the statement.

Source check: the local algebra.tex file is absent from this clone. Read the source
statement and proof at https://stacks.math.columbia.edu/tag/032Q (Lemma 10.161.17).
It states the same three assertions for the one-variable power series ring. The
module docstring includes all six DAG proof steps, their named dependencies, and
explains coefficientwise finiteness in step 3. No fault or disputed statement found.

Searches (2026-10-11):
- msearch LeanFinder, query “Formal power series over a Noetherian Japanese domain
  are Noetherian Japanese domains”: eight hits, including
  PowerSeries.instIsNoetherianRing, PowerSeries.instIsDomain and DVR results; none
  states Japanese/N-2 preservation.
- msearch Loogle, query `MvPowerSeries, IsN2`: zero hits; unknown identifier IsN2.
- msearch grep, query `IsN2|Japanese|japanese|integralClosure`, subdirectory
  RingTheory/MvPowerSeries: zero hits.
- msearch LeanSearch, query “The power series ring over a Noetherian Japanese
  integral domain is Japanese”: unavailable (Internal Server Error); no verdict
  inferred from service failure.
- rg of `IsN2|japanese|Japanese|power-series-n2` in source WeilConjectures and
  project lean/Sheaf: source has no match; project has the existing JapaneseDomain
  definition and sibling theorems, but no power-series N-2 theorem. The only item-id
  reference is a proof docstring in NagataOfCompleteLocal.
- rg of the exact item id in source WeilConjectures: no match.
- rg of `isN2.*owerSeries|powerSeries.*[nN]2` in dag/lean_names_upstream.json,
  source WeilConjectures, and lean/Sheaf: no match. The chosen full declaration
  name is absent from these sources.

Validation: server scompile succeeded with no errors or warnings after the local
registration of Mathlib's domain conversion. The theorem remains a stage-2 statement
with `sorry`, and all variables and universes are explicitly bound.

## Second reading by M1

Read the sandbox node and module independently, all six statement-dependency nodes,
JapaneseDomain.lean, and the recorded Mathlib declarations. The local Stacks .tex is
absent, so I opened the upstream algebra.tex directly at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex:
`lemma-power-series-over-N-2` (currently lines 41811–41827), `section-japanese`
and `definition-N` (41381–41398), and the chapter's Conventions (31–41).
The source assumes commutative unital rings; the Japanese section adds no standing
Noetherian, normality, characteristic, or separability assumption beyond those
explicit in the lemma. Tag 032Q agrees with the node without correction.

Object, hypothesis, and conclusion checklist (H3):

- Coefficient ring R: `(R : Type u) [CommRing R]`. Verdict: exact commutative
  unital ring, as the source's convention requires.
- R is an integral domain: `[IsDomain R]`. Verdict: exact, including nontriviality;
  neither a field nor normality is assumed.
- R is Noetherian: `[IsNoetherianRing R]`. Verdict: exact recorded declaration
  `IsNoetherian R R`, equivalent to every ideal being finitely generated.
- R is N-2: `(hR : IsN2 R (FractionRing R))`. Verdict: exact JapaneseDomain
  dependency, with the canonical fraction field; no choice of extra fraction
  field or additional mathematical hypothesis is imposed.
- One-variable formal power series ring R[[x]]: `MvPowerSeries (Fin 1) R`.
  Verdict: exact n=1 specialization of the recorded definition. Basic.lean defines
  `(σ →₀ ℕ) → R`; coefficients, coefficientwise addition and convolution
  multiplication give exactly the node's ring, with its canonical constant map.
- Conclusion: R[[x]] is Noetherian: first conjunct
  `IsNoetherianRing (MvPowerSeries (Fin 1) R)`. Verdict: exact.
- Conclusion: R[[x]] is an integral domain: second conjunct
  `IsDomain (MvPowerSeries (Fin 1) R)`. Verdict: exact.
- Conclusion: R[[x]] is N-2: third conjunct
  `IsN2 (MvPowerSeries (Fin 1) R) (FractionRing (MvPowerSeries (Fin 1) R))`.
  Verdict: exact. Reading the dependency body, this universally quantifies over
  `L`, `[Field L]`, `[Algebra K L]`, `[Algebra R[[x]] L]`,
  `[IsScalarTower R[[x]] K L]`, and `[FiniteDimensional K L]`, before concluding
  `Module.Finite R[[x]] (integralClosure R[[x]] L)`. Thus the finite field
  extension, the composite algebra map, the correct integral closure and its
  finite generation are all present, in the required order. Algebra.Defs,
  IntegralClosure.Algebra.Basic, Finiteness.Defs and FiniteDimensional.Defs were
  opened: these are the dependencies' notions, without a private substitute.

The local registration of `NoZeroDivisors.to_isDomain` supplies a structure
already available from Mathlib's power-series no-zero-divisors and nontriviality
instances. It is not a new assumption or a proof written for stage 2. There are
no new definition nodes, dependency modules, or statement changes to review.

Edge cases: the zero ring is excluded precisely by the source's domain
hypothesis; fields are permitted. Zero series are elements of the ring, with no
extra nonvanishing assumption. No empty index or n=0 case is claimed: this node
fixes one variable. No schemes occur. All characteristics and inseparable finite
extensions are included. The identity field extension is included. Universe u
is explicitly bound and arbitrary; Fin 1 does not constrain it, and FractionRing
and the power series ring remain in u. Finite-dimensional extensions in higher
universes admit models in the base field's universe (finite bases), so the
recorded IsN2 quantification does not lose a mathematical finite extension.

Independent duplicate searches, with wording different from the worker's:

- LeanFinder via msearch: “Japanese property survives adjoining a formal
  variable to a noetherian integral domain”: eight hits, including power-series
  Noetherianity, DVR and UFD results, but no Japanese preservation statement.
- Loogle via msearch: `integralClosure, MvPowerSeries`: zero hits.
- Grep via msearch in RingTheory/PowerSeries:
  `normalization|integralClosure|Japanese|Nagata`: three hits concerning
  normalization monoids, not integral-closure finiteness or N-2.
- LeanSearch via msearch: “Finiteness of normalization in finite fraction field
  extensions for a formal power series ring”: unavailable (Internal Server Error),
  recorded as a service failure, not evidence of absence.
- Direct rg in Mathlib/RingTheory/MvPowerSeries for
  `japanese|integralClosure|nagata|N-2`: no matches.
- Direct rg in source WeilConjectures for `isN2|japanese|032Q|noetherian_domain_isN2`:
  no matches. Direct rg in project lean/Sheaf and dag/lean_names_upstream.json for
  the chosen declaration, the item id, and combinations of IsN2 with PowerSeries
  or MvPowerSeries finds only the citer NagataOfCompleteLocal's proof docstring.
  No equivalent statement or colliding declaration was found.

H5–H9: no definitions are added, hence no hollow data. The only new theorem has
proof `by sorry`. The source and blueprint tag appear in module and declaration
docstrings; all six node proof steps and their dependencies are present, including
coefficientwise generation in step 3 and both quotient and completeness in step 5.
Imports, RingTheory placement, namespace, bound variables and line lengths are
correct. The node's lean.statement equals the file signature verbatim.

Mismatches found: none. Changed only this report by adding the independent second
reading; kept the correct Lean and node record. Compilation via scompile with the
absolute sandbox module path succeeded (exit 0, 1.3 seconds), without warnings.

## Reviewer fix (R-psn1306)

The node is the one-variable case, so the ring R[[x]] is stated with Mathlib's
one-variable `PowerSeries R` instead of `MvPowerSeries (Fin 1) R` (lead's instruction:
one variable uses `PowerSeries`). The declaration is renamed to
`PowerSeries.noetherian_domain_isN2`; the import is
`Mathlib.RingTheory.PowerSeries.NoZeroDivisors`, whose `IsDomain R⟦X⟧` instance types
`IsN2 (PowerSeries R) (FractionRing (PowerSeries R))`, so the local
`NoZeroDivisors.to_isDomain` instance is dropped. Hypotheses (`CommRing`, `IsDomain`,
`IsNoetherianRing`, `IsN2 R (FractionRing R)`) and the three conclusions are unchanged
and match the node and C1 a0a22304a's `isN2_polynomial` form.
