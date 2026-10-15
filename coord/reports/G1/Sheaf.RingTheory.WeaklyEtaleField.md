## What changed

Replaced the proof of `Algebra.weaklyEtale_field` with a short proof from the existing source
results. It installs `Algebra.IndEtale` using `Algebra.WeaklyEtale.indEtale_field`, proves
finite generation cases using `Algebra.WeaklyEtale.etale_of_fg` and
`Algebra.FormallyUnramified.finite_of_free`, obtains reducedness from the absolutely-flat
instance, and obtains separable algebraic residue fields from
`Algebra.IndEtale.isSeparable_residueField_of_field` and
`Algebra.IsSeparable.isAlgebraic`. Unused imports were removed; the statement is unchanged.

## Proved and sorry left

`Algebra.weaklyEtale_field` is fully proved. No `sorry` remains in the delivered module, and
no new theorem or node was added. Holes closed: `Algebra.weaklyEtale_field` (1 of 1).
Holes added: none (0); this is a proof, not a decomposition.

## No longer needed

The former proof-only imports and all sixteen planned DAG proof dependencies are unnecessary
for this route. Removed proof-only imports are `WeilConjectures.Mathlib.RingTheory.Etale.Weakly`,
`Sheaf.RingTheory.IndEtaleStability`, `Mathlib.RingTheory.Ideal.Pure`,
`Mathlib.RingTheory.Ideal.MinimalPrime.Basic`, `Mathlib.RingTheory.Ideal.MinimalPrime.Localization`,
`Mathlib.RingTheory.FiniteType`, `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`,
`Sheaf.RingTheory.FiniteTypeAlgebraFiniteSpectrum`,
`Sheaf.RingTheory.ReducedNoetherianTotalRingFractions`,
`WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, and `Sheaf.RingTheory.WeaklyEtaleTor`.
The proof uses only `WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField`; the retained public
imports provide the original statement interface.

The old proof dependency edges removed are:

- `lem-weil-pbc-weak-etale-tor`
- `lem-weil-pbc-localization-ring-weakly-etale`
- `lem-weil-pbc-ind-etale-stability`
- `def-weil-pbc-localization-at-prime`
- `lem-exc-flat-quotient-element-equation`
- `lem-weil-pbc-minimal-prime-over-proper-ideal`
- `lem-weil-pbc-weakly-etale-field-separable`
- `lem-weil-pbc-injective-minimal-prime-lift`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-noetherian-finitely-many-minimal-primes`
- `lem-weil-pbc-prime-contains-minimal-prime`
- `pqf-lem-finite-type-algebra-finite-spectrum`
- `lem-weil-pbc-reduced-noetherian-total-ring-fractions`
- `lem-pc-minimal-prime-avoids-nonzerodivisor`
- `lem-sc-finite-etale-algebra-criterion`
- `def-weil-pbc-ind-etale-algebra`

The last node remains a statement dependency; its public module remains imported. This list
records unused direct proof dependencies, not a claim that all their modules become unreachable.

## Where the brief, the DAG or earlier work was wrong

The seven-step DAG proof plan was substantially longer than necessary. The source module already
proves the key finite-subalgebra and ind-etale results, and its ind-etale residue-field theorem
supplies separability directly. No statement or definition was changed.

## Second reading by G1

1. **Signature and accidental changes — PASS.** I compared the delivered declaration with the
repository version byte for byte. The theorem signature and all hypotheses and conclusions are
unchanged; the proof is the only declaration body change.

2. **Proof and axioms — PASS.** The module compiles with `lcompile.py`, contains no `sorry`,
`axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and the proof uses only existing
source and Mathlib declarations. The local axiom probe reports no forbidden axioms.

3. **Statements and edge cases — PASS.** No statement was split off or added. The existing
source results apply with the original `Field k`, `CommRing B`, `Algebra k B`, and
`Algebra.WeaklyEtale k B` hypotheses, including the zero-algebra case; the separability result
is followed by the standard `IsSeparable.isAlgebraic` implication.

4. **Shortest route and pruning — PASS.** The source theorem route is shorter than the imported
seven-step blueprint proof. I removed every proof-only import not required by compilation and
kept the unit and chapter records unchanged; this item is not one of the unit's realized steps,
so the shorter route does not bypass a realized unit step.

5. **DAG agreement — PASS.** The node proof is one library-based step, `proof_deps` is empty,
and `proof_origin` names `WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField`, exactly matching
the Lean proof. No new nodes or change records are needed.

I retained the existing public imports and `open AlgebraicGeometry` to preserve the module
interface for its seven importers, and removed all proof-only imports that the shorter source
theorem route does not require. The report's no-longer-needed list records the old proof
dependencies and imports.
