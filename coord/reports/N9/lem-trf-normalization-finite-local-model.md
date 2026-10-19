## Worker report

The module `Sheaf.TraceFormula.NormalizationFiniteLocalModel` states
`exists_finiteType_intermediate_algebra_isolating_prime`. It uses Mathlib's
`integralClosure R K` for the normalization and a subalgebra
`C : Subalgebra R (integralClosure R K)` for the finite intermediate ring.

The hypotheses are rendered as follows: `R : Type u`, `K : Type v`, with
`[CommRing R]`, `[IsDomain R]`, `[Field K]`, `[Algebra R K]`, and
`[IsFractionRing R K]`; the selected normalization prime is
`Q : Ideal (integralClosure R K)` with `[Q.IsPrime]`. The existential witness
has `Algebra.FiniteType R C`, exactly finite generation as an R-algebra.

For the contraction, `p` is defined as
`Ideal.comap (algebraMap C (integralClosure R K)) Q`; `p.IsPrime` states that it
is prime. The uniqueness clause is the universally quantified implication
`Q'.IsPrime → Ideal.comap (algebraMap C (integralClosure R K)) Q' = p → Q' = Q`.
The local ring is `Localization.AtPrime p`, and its domain and Noetherian
properties are rendered by `IsDomain (Localization.AtPrime p)` and
`IsNoetherianRing (Localization.AtPrime p)`. The two dimension clauses are
`ringKrullDim (Localization.AtPrime p) = ringKrullDim (Localization.AtPrime Q)`
and `ringKrullDim (Localization.AtPrime Q) = (Q.height : WithBot ℕ∞)`;
`Ideal.height` is Mathlib's supremum of strict prime-chain lengths.

The final existential supplies ring maps `jC` and `jQ` into the common fraction
field `K`, with equations saying they extend the canonical maps from `C` and
`integralClosure R K`. With the corresponding `RingHom.toAlgebra` instances,
`IsIntegralClosure (Localization.AtPrime Q) (Localization.AtPrime p) K` states
that the localized normalization is the integral closure of the local model in
K. These maps make the ambient-field identification explicit while preserving
the source's canonical localization construction.

Dependency declarations used: `integralClosure`, `IsIntegral`, and the
integral-closure infrastructure from Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic;
`Localization.AtPrime` from Mathlib.RingTheory.Localization.AtPrime.Basic;
`IsNoetherianRing` and `Algebra.FiniteType` from Mathlib.RingTheory.FiniteType and
Mathlib.RingTheory.Noetherian.Defs; `ringKrullDim` from
Mathlib.RingTheory.KrullDimension.Basic; and `Ideal.height` from
Mathlib.RingTheory.Ideal.Height. The four DAG statement dependencies are all
Mathlib leaves, so no project dependency modules were needed.

Edge cases checked against the source statement: the zero prime `Q = ⊥` is
allowed; a single prime over the contraction requires no separation element;
field bases give zero-dimensional localizations; and the explicit coercion from
`ℕ∞` to `WithBot ℕ∞` records the dimension/height type distinction.

Searches made: `msearch.py ... leanfinder "finite type intermediate subalgebra unique prime localization integral closure"`
returned only auxiliary finite-localization, Zariski-main, and quasi-finite results;
`msearch.py ... loogle "Subalgebra, Ideal, IsIntegral, ringKrullDim"` returned no
match; `msearch.py ... grep "normalization|integralClosure" RingTheory/IntegralClosure`
found only generic Mathlib integral-closure/localization declarations. Repository
`rg` searches found no declaration for this blueprint id or theorem. Thus no
existing declaration has the full statement.

No `STATEMENT-DISPUTED` issue or node fault was found. The file compiles cleanly
with `scompile.py`; the only proof placeholder is the required `sorry`.

## Second reading by N9

An independent rereading of the node and module checked each conjunction in
order: finite type, prime contraction, uniqueness, local domain and Noetherian
properties, both dimension equalities, and the common-K integral-closure clause.
The Lean declaration preserves every source hypothesis and conclusion. No
mismatch was found.

## Maintainer review fix (cc reviewer, 2026-10-18)

The delivered signature omitted the node's hypothesis that $R$ is Noetherian
(Swanson–Huneke Lemma 4.8.4 assumes a Noetherian domain). Without it the
statement is false: for a non-Noetherian rank-one valuation domain $R$ (integrally
closed, so $N=R$) and $Q$ its maximal ideal, every intermediate $C$ equals $R$ and
$C_p=R$ is not Noetherian. The fix adds `[IsNoetherianRing R]` after
`[IsDomain R]` and mentions the Noetherian domain in the docstring's first line;
nothing else changed. The fixed file compiles with nt_compile.py (no error; only
the `sorry` warning, filtered by the tool).
