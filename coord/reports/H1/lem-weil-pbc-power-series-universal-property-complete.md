## Worker report

Module: `Sheaf.RingTheory.PowerSeriesUniversalPropertyComplete`.
Declaration: `MvPowerSeries.exists_ringHom_of_isAdicComplete`.
This states the whole node with one `sorry`; there are no definitions or auxiliary theorems.
The node copy changes only `lean`. No new nodes, dependency modules, or statement corrections
are needed. No statement dispute was found.

Hypotheses and clauses, matched individually:

- The commutative rings Λ and T are `{Λ : Type u} {T : Type v} [CommRing Λ] [CommRing T]`.
  The universes are explicitly declared and independent; neither ring is restricted to a field,
  a local ring, or a Noetherian ring.
- The ideal is `(a : Ideal T)`, and completeness is `[IsAdicComplete a T]`, including
  separatedness. This is exactly the recorded dependency, not mere precompleteness.
- The coefficient homomorphism is `(α : Λ →+* T)`.
- The nonnegative number of variables is `(n : ℕ)`; the prescribed elements are
  `(t : Fin n → T)` and their membership is `(ht : ∀ i : Fin n, t i ∈ a)`.
- Existence of a ring homomorphism is `∃ Φ : MvPowerSeries (Fin n) Λ →+* T`.
- Agreement on constants is `∀ r : Λ, Φ (C r) = α r`.
- The images of the variables are `∀ i : Fin n, Φ (X i) = t i`.
- For each series `F` and candidate value `y`, the congruences for every positive integer
  are `∀ m : ℕ, 1 ≤ m → y - (...) ∈ a ^ m`.
  The sum ranges over `E : Fin n → Fin m`, filtered by `∑ i, (E i : ℕ) < m`.
  Each exponent vector in ℕ^n of total degree less than m has all its coordinates less
  than m, so this indexing enumerates precisely the required terms once each.
  `Finsupp.equivFunOnFinite.symm (fun i ↦ (E i : ℕ))` is the exponent for `coeff ... F`;
  `α (coeff ... F)` is α(a_E); `∏ i : Fin n, t i ^ (E i : ℕ)` is t^E.
  No infinite sum, ordering of summation, or convergence structure is introduced.
- The characterization `(...) ↔ y = Φ F`, universally quantified over `F` and `y`, states
  both that Φ(F) satisfies every congruence and that it is the unique such element of T.
- Finally `∀ Ψ : MvPowerSeries (Fin n) Λ →+* T, (∀ r, Ψ (C r) = α r) →
  (∀ i, Ψ (X i) = t i) → Ψ = Φ` gives uniqueness among all ring homomorphisms with those
  values. There is no continuity assumption.

Dependency declarations read and used:

- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete` in
  `Mathlib.RingTheory.AdicCompletion.Basic`, including its docstring, the definitions of
  `IsHausdorff` and `IsPrecomplete`, and `AdicCompletion.of_bijective_iff` at line 647.
- `def-weil-pbc-multivariate-power-series`: its `mathlib_match` is `MvPowerSeries` in
  `Mathlib.RingTheory.MvPowerSeries.Basic`, specialized to `Fin n`. The full definitions
  and docstrings of `MvPowerSeries`, `coeff`, `C`, and `X` were read. This is a Mathlib leaf
  and needs no additional Lean record.
- `Finsupp.equivFunOnFinite` is Mathlib's existing equivalence between finitely supported
  functions on a finite set and ordinary functions, read in `Data/Finsupp/Defs.lean`.

Edge cases checked before writing:

- n = 0: there is one empty exponent function for each m ≥ 1; its degree is zero and its
  evaluated monomial is the empty product 1. The sum is α of the constant coefficient;
  the variable conditions are empty, so the result is the coefficient map.
- m = 1: only the zero exponent survives, giving the constant coefficient modulo a.
- m = 0 imposes no condition, just as the statement only requires m ≥ 1.
- a = 0: every t_i is zero, and the map is constant-coefficient evaluation followed by α.
- a = top: completeness forces T to be the zero ring by separatedness, and every clause
  then holds for its unique ring map. Zero rings are allowed; no Nontrivial binder is added.
- No finite generation of a is assumed or needed. Finiteness of the variables ensures the
  finite decomposition in step 5, which supports uniqueness without continuity.

Searches (2026-10-11):

- `msearch.py ... leanfinder "ring homomorphism from multivariate power series to an
  adically complete ring with prescribed variables and uniqueness"`: 8 hits, including
  `IsAdicComplete.liftRingHom`, `of_liftRingHom`, `StrictMono.liftRingHom`,
  `AdicCompletion.liftRingHom`, `liftAlgHom`, `IsAdicComplete.liftAlgHom`,
  `AdicCompletion.mkₐ`, `IsAdicComplete.algHom_ext`. These concern compatible quotient
  maps or adic-completion maps, not this universal property of a power series ring.
- `msearch.py ... loogle "MvPowerSeries, IsAdicComplete, RingHom"`: 0 hits.
- `msearch.py ... grep "eval₂Hom|eval₂_unique|IsAdicComplete" RingTheory/MvPowerSeries`:
  6 hits, chiefly `MvPowerSeries.eval₂Hom` at Evaluation.lean:230. Its full signature and
  the signature of `eval₂_unique` at line 283 were read: the former requires topological
  structures, Continuous α and HasEval t; the latter requires continuity of the competing
  map. They do not state this node. The stage-1 searches recorded on the node reach the
  same conclusion, including its LeanSearch query and result.
- `rg -n "MvPowerSeries|power-series-universal-property-complete"
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures lean/Sheaf`: source has only an unrelated
  analytic use; the project's modules include Cohen presentations, formal fibres and
  citers referring to this node in docstrings, but no declaration of its universal property.
- Name/concept check with `rg -n "universal_property.*adic|exists.*eval.*adic"` over
  `dag/lean_names_upstream.json`, Mathlib's MvPowerSeries directory, and `lean/Sheaf`:
  no matches. The proposed name is fresh.

Source reading: the local `literature/stacks-project/*.tex` files are absent on this machine.
The cited Stacks pages were opened directly:
[07NL](https://stacks.math.columbia.edu/tag/07NL) invokes the universal property in its proof;
[07NN](https://stacks.math.columbia.edu/tag/07NN) constructs the map with the prescribed
coefficient restriction and images x_i ↦ φ(x_i) + y_i;
[032A](https://stacks.math.columbia.edu/tag/032A) constructs the power series map to the
complete local ring. The node is an agent-formulated general lemma, as its source records.
The declaration docstring carries all six natural-language proof steps, including the
finite degree-m monomial decomposition needed for uniqueness of arbitrary ring maps.

Verification: `scompile.py H1 lem-weil-pbc-power-series-universal-property-complete
<module>` compiled on the server in 1.3 seconds, exit code 0, with no errors or warnings.
All variables and universes are explicitly bound.

## Second reading by H1

Independent reading of the node copy, the delivered module, both statement-dependency
nodes and their Mathlib declarations. No mismatch found; the Lean and node are retained.

Object/hypothesis/conclusion checklist, in the node's order:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Commutative coefficient ring Λ | `{Λ : Type u} [CommRing Λ]` | Exact; no field assumption. |
| Commutative target ring T | `{T : Type v} [CommRing T]` | Exact; no local or Noetherian assumption. |
| Ideal a in T | `(a : Ideal T)` | Exact; neither properness nor finite generation imposed. |
| T a-adically complete, including separatedness | `[IsAdicComplete a T]` | Exact recorded dependency. |
| Coefficient ring map α : Λ → T | `(α : Λ →+* T)` | Exact; unital ring map, no injectivity or continuity. |
| Nonnegative finite number n of variables | `(n : ℕ)` and `MvPowerSeries (Fin n) Λ` | Exact recorded power-series notion, including n = 0. |
| Prescribed t_i in a | `(t : Fin n → T) (ht : ∀ i : Fin n, t i ∈ a)` | Exact; Fin n reindexes 1,...,n. |
| Existence of Φ : Λ[[x]] → T | `∃ Φ : MvPowerSeries (Fin n) Λ →+* T` | Exact. |
| Φ agrees with α on constants | `∀ r : Λ, Φ (C r) = α r` | Exact; C is the dependency's constant inclusion. |
| Φ sends each variable to t_i | `∀ i : Fin n, Φ (X i) = t i` | Exact; X is the dependency's variable series. |
| F has coefficients a_E | `(F : MvPowerSeries (Fin n) Λ)` and `coeff ... F` | Exact coefficient family. |
| Total degree is sum of coordinates | `∑ i : Fin n, (E i : ℕ)` | Exact |E|. |
| Monomial t^E | `∏ i : Fin n, t i ^ (E i : ℕ)` | Exact, including empty product. |
| Sum over precisely |E| < m | `∑ E ∈ (Finset.univ : Finset (Fin n → Fin m)).filter (fun E ↦ (∑ i : Fin n, (E i : ℕ)) < m), ...` | Exact finite enumeration, each exponent once. |
| Coefficient evaluation α(a_E) | `α (coeff (Finsupp.equivFunOnFinite.symm (fun i ↦ (E i : ℕ))) F)` | Exact conversion of ordinary finite exponent functions to finitely supported functions. |
| Congruence modulo a^m for every m ≥ 1 | `∀ m : ℕ, 1 ≤ m → y - (...) ∈ a ^ m` | Exact quotient-ring congruence; orientation of subtraction immaterial. |
| Φ(F) is the unique value satisfying all congruences | `∀ F y, (∀ m, 1 ≤ m → ...) ↔ y = Φ F` | Both satisfaction and uniqueness, with F,y universally quantified after Φ. |
| Φ is the only ring map with the prescribed values | `∀ Ψ : MvPowerSeries (Fin n) Λ →+* T, (∀ r, Ψ (C r) = α r) → (∀ i, Ψ (X i) = t i) → Ψ = Φ` | Exact uniqueness among all ring maps; no continuity hypothesis. |

For the sum indexing, each natural exponent vector with degree less than positive m
has every coordinate less than m, so gives a unique `Fin n → Fin m`; conversely every
filtered function has that total degree. `Finsupp.equivFunOnFinite` (Defs.lean:203-215)
is the existing equivalence with inverse having exactly these coordinate values.
The parentheses place the entire family of congruences on the left of the iff.

Source check: local Stacks .tex files are absent. I independently opened
[07NL](https://stacks.math.columbia.edu/tag/07NL),
[07NN](https://stacks.math.columbia.edu/tag/07NN) and
[032A](https://stacks.math.columbia.edu/tag/032A), then fetched the upstream
`more-algebra.tex` and `algebra.tex` into the sandbox's `scratchpad/` and read the
named labels and surrounding text. The node explicitly records an agent-formulated
general lemma, not the entire theorem of any one of these tags. The source applications
use fields/Cohen rings and complete local rings (07NN additionally Noetherian);
these are hypotheses of those applications, not additional hypotheses of this general
universal property. Its six-step proof works for arbitrary commutative rings and
arbitrary ideals under the stated separated completeness assumption. In particular,
finite degree-m monomial decomposition forces every competing ring map to satisfy
all the congruences, without continuity. At n = 0 the remainder is zero and the
set of positive-degree monomials is empty, so that argument still works.

Dependencies: `IsAdicComplete` (AdicCompletion/Basic.lean:44-56) extends precisely
`IsHausdorff` and `IsPrecomplete`; `AdicCompletion.of_bijective_iff` (line 647)
identifies it with the node's bijective canonical completion map. Stacks
`definition-complete` at algebra.tex:22626 explicitly includes separatedness.
`MvPowerSeries` (Basic.lean:86) is `(σ →₀ ℕ) → R`; `coeff` (137), Cauchy
multiplication/`coeff_mul` (215-220), `C` (334) and `X` (374) give exactly the
second dependency's coefficient families, product, constants and variables.
Both dependencies are usable Mathlib notions; no private copies, missing definition
nodes, or dependency modules are needed. No `statement_change` exists or is required.

Edge cases: n = 0 has one empty exponent function for every positive m, degree 0,
product 1, and only the constant coefficient remains. At m = 1 only the zero exponent
survives. At m = 0 the implication imposes no condition, matching m ≥ 1. If a = 0,
all t_i vanish and Φ is constant-coefficient evaluation followed by α. If a = top,
separatedness forces T to be the zero ring. Zero coefficient/target rings are allowed
whenever α exists; no Nontrivial instance is requested. All characteristics are covered.
Independent explicit universes u and v cover coefficient and target rings of different
sizes; Fin n places no restriction on those universes. Scheme/empty-scheme cases do
not occur in this ring statement.

Independent searches, using words beyond the worker's queries:

- `msearch.py ... leanfinder "substitution of finitely many elements in an ideal into formal series of a separated complete commutative ring"`: eight hits, principally `HasSubst.ideal`, `hasSubstIdeal`, `hasEvalIdeal`, and their membership characterizations. None is the statement. I opened `Substitution.lean`'s `subst` and `substAlgHom` signatures: their target is another power-series ring, not arbitrary complete T.
- `msearch.py ... loogle "MvPowerSeries, Ideal, RingHom"`: eight hits, including `truncTotalAlgHom_apply`, `toAdicCompletion_apply_eq_mk_truncTotal` and ideal/map-coefficient lemmas. I opened `Equiv.lean`'s `toAdicCompletion`, inverse and `toAdicCompletionAlgEquiv`; these compare power series with the completion of polynomials, not the node's evaluation and uniqueness statement.
- `msearch.py ... grep "subst|eval.*unique|adic|universal" RingTheory/MvPowerSeries`: evaluation, substitution, and completion-comparison hits. I reread `Evaluation.lean:230` (`eval₂Hom`) and `:283` (`eval₂_unique`) with the enclosing topological instances: they require topology and continuity; the latter does not assert uniqueness among all ring maps as here.
- `msearch.py ... leansearch "A unique ring map evaluates formal power series at finitely many elements of an ideal when the target ring is complete and separated for powers of that ideal"`: service unavailable (Internal Server Error); no mathematical verdict inferred from this failed query. Successful LeanFinder, Loogle and local grep searches above supply the independent check; the node also retains its earlier LeanSearch record.
- `rg` for `MvPowerSeries`, `exists_ringHom_of_isAdicComplete` and `universal.*power.series` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`: the source has only an unrelated analytic use of MvPowerSeries, and the project's power-series modules state presentations, formal fibres and formal smoothness, not this universal property. The declaration name is fresh.

H5/H6/H8/H9: the module contains no definition and exactly one named theorem with
`by sorry`; no proof was added. Its module and declaration docstrings name the sources
and blueprint id. The declaration docstring carries each of the six proof steps,
including the finite decomposition for uniqueness. Both imports are used, every line
has at most 100 characters, the namespace is `MvPowerSeries`, and all variables and
universes are explicitly bound. The node's `lean.statement` was mechanically compared
with the actual signature before `:= by` and is verbatim equal.

Verification: independent `scompile.py H1 lem-weil-pbc-power-series-universal-property-complete`
on the delivered module compiled on the server in 1.2 s, exit code 0, no warnings.
Changes: appended this second-reading report only; Lean and node unchanged.

## Stage-2 review fix (R-pup1323)

The partial-sum clause wrote a second form of the node's finite sum (a filtered sum over
`Fin n → Fin m` through `Finsupp.equivFunOnFinite`, congruence as `y - … ∈ a ^ m`). It is
restated word for word in the form of the landed lem-weil-pbc-power-series-adic-evaluation
(C1 8275e16fa) and G1 690a901d9: `Ideal.Quotient.mk (a ^ m) y = Ideal.Quotient.mk (a ^ m)
(MvPolynomial.eval₂ α t (F.truncTotal m))` for every `m ≥ 1`; imports `MvPowerSeries.Trunc`
and `MvPolynomial.Eval`. Same content: `truncTotal m` keeps exactly the coefficients of
total degree `< m`. Not a restatement of C1: this node asserts uniqueness among all ring
maps without continuity (C1 asserts continuity and uniqueness among continuous maps, and
cites this node in its proof).
