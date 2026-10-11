## Worker report

The module `lean/Sheaf/RingTheory/FiniteTypeZDomainNormalizationFinite.lean` states
`RingTheory.finiteTypeZDomain_integralClosure_finite`. It binds a commutative domain `A`,
a field `K` equipped with `Algebra A K` and `IsFractionRing A K`, and the finite-type
hypothesis `[Algebra.FiniteType ℤ A]`. Its conclusion is
`Module.Finite A (integralClosure A K)`, rendering the finite generation of the integral
closure of `A` in its fraction field as an `A`-module. The theorem proof is `sorry` as
required for stage 2.

The dependency declarations used are Mathlib's `Algebra.FiniteType` (the node
`def-weil-pbc-finite-type-algebra`), `integralClosure` (the node
`def-weil-pbc-integral-closure`), and `Module.Finite` (the node
`def-weil-finitely-generated-module`). The module imports
`Mathlib.RingTheory.FiniteType`, `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, and
`Mathlib.RingTheory.Localization.FractionRing` for these declarations and
`IsFractionRing`.

Each hypothesis is rendered explicitly: `A : Type u`, `K : Type v`, `[CommRing A]`,
`[IsDomain A]`, `[Algebra.FiniteType ℤ A]`, `[Field K]`, `[Algebra A K]`, and
`[IsFractionRing A K]`. The sole conclusion clause is rendered by
`Module.Finite A (integralClosure A K)`.

Edge cases checked include arbitrary universes `u` and `v`, the zero characteristic base
`ℤ`, and arbitrary fields of fractions represented by `IsFractionRing`; no nonzero,
Noetherian, or finite-extension hypothesis was added.

Searches made: `msearch.py E1 ... leanfinder` for finiteness of normalization of a finite
type `ℤ`-domain (returned only `IsIntegralClosure.finite`, which requires an integrally
closed Noetherian base); `msearch.py ... loogle` for `Module.Finite ?A (integralClosure ?A ?L)`
(returned none); `msearch.py ... grep` and direct `rg` over Mathlib RingTheory and
`WeilConjectures` (no Nagata/Japanese normalization theorem); and `rg` over
`lean/Sheaf` (no existing statement). The dependency declarations were checked in their
node records and corresponding Mathlib signatures.

## Earlier second reading (a previous round; superseded)

I reread the node and the Mathlib declarations. The node's hypotheses “integral domain”,
“finite type over `ℤ`”, and “field of fractions `K`” are exactly `[CommRing A]`,
`[IsDomain A]`, `[Algebra.FiniteType ℤ A]`, `[Field K]`, `[Algebra A K]`, and
`[IsFractionRing A K]`. Its definition of `A'` as the integral closure is exactly
Mathlib's `integralClosure A K`; its finite-module clause is exactly
`Module.Finite A (integralClosure A K)`. No clause or hypothesis was changed. The
server compiler accepted the module with only the expected `sorry` warning. The dry-run
preflight required the signature record to omit the parser's proof delimiter `:=`; that
record now matches the file.

## Second reading by E1

The node introduces the following objects and clauses, matched against
`RingTheory.finiteTypeZDomain_integralClosure_finite`:

1. `A` is a commutative integral domain: rendered by `(A : Type u) [CommRing A]
   [IsDomain A]`. Verdict: exact; no field, Noetherian, or nonzero assumption is added.
2. `A` is generated as a ring by finitely many elements over `ℤ`: rendered by
   `[Algebra.FiniteType ℤ A]`, using Mathlib's canonical `ℤ`-algebra on a commutative
   ring. Verdict: exact.
3. `K` is the field of fractions of `A`: rendered by `(K : Type v) [Field K]
   [Algebra A K] [IsFractionRing A K]`. Verdict: exact, with arbitrary independent
   universes as permitted by the node.
4. `A'` is the integral closure of `A` in `K`: rendered by the Mathlib object
   `integralClosure A K`, whose elements are integral over `A`. Verdict: exact.
5. `A'` is a finitely generated `A`-module: rendered by the sole conclusion
   `Module.Finite A (integralClosure A K)`. Verdict: exact; quantifier and conclusion
   strength are unchanged.

Edge cases were checked: arbitrary universe levels `u` and `v` are retained; the
finite-type base is exactly characteristic-zero `ℤ`; the zero-generator case is
included by `Algebra.FiniteType`; and `IsFractionRing` permits every field-of-fractions
realization without an extra finiteness or separability condition. No empty-index,
zero-object, or empty-scheme case is relevant to this ring statement.

I reran the three required searches. LeanFinder found only results requiring an
integrally closed Noetherian base (such as `IsIntegralClosure.finite`); Loogle found no
`Module.Finite` theorem for `integralClosure`; and the Mathlib grep found no Nagata,
Japanese, or finite-normalization result. Searches of the project source and `lean/Sheaf`
also found no existing declaration. The dependency declarations were checked directly:
`Algebra.FiniteType`, `integralClosure`, and `Module.Finite` are the recorded Mathlib
notions and are used directly by the module.

No mismatch was found, so no source, node, or Lean statement was changed in this second
reading.
