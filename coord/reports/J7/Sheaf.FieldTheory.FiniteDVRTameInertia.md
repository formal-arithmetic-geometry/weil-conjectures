## What changed

Completed `IsDiscreteValuationRing.finite_normalization_tame_inertia` in
`Sheaf.FieldTheory.FiniteDVRTameInertia`, preserving its signature and all public imports.
Private proved helpers construct the stabilizer action on the localization, construct the
uniformizer character with independence and normality, prove the wild kernel has prime-power
order by telescoping and Cauchy, and compare finite cardinalities to obtain the tame quotient.
The construction uses actual localization maps and units; no data comes from an arbitrary
unproved existence theorem. The existing inertia-order theorem is used only for its numerical
proposition. The node records the direct Mathlib normalization route.

## Proved and sorry left

Closed 1 of 1 holes: `IsDiscreteValuationRing.finite_normalization_tame_inertia`
(node `lem-exc-finite-dvr-tame-inertia`). Added 0 holes. No `sorry` remains in the delivered
module. All six private helpers are proved. The existing imported declaration
`IsDiscreteValuationRing.inertia_order_prime_part` remains an external proof dependency;
this delivery neither changes it nor adds its hole.

The uniformizer-character, wild-kernel, and finite-cardinality calculations were checked
individually before assembly. Final single-file compilation and the delivery tool's axiom
probe are the validation of the complete proof. The unchanged statement handles the trivial
extension, pure p-power ramification, tame ramification and inseparable residue extensions;
no perfect-residue or henselian hypothesis is introduced.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres` and
node dependency `lem-sc-integral-closure-dedekind-surjective-fibres`: direct Mathlib
`IsIntegralClosure.isDedekindDomain` gives Dedekindness, and quotient finiteness followed by
restriction of scalars gives residue finiteness. Removed `lem-sc-dvr-dimension-one` from the
proof dependencies: the PID Dedekind instance needs no separately stated dimension equality.
The explicit proof imports `Mathlib.RingTheory.DiscreteValuationRing.TFAE` and
`Mathlib.GroupTheory.Perm.Cycle.Type` are redundant through the required Dvr and PGroup
imports and were removed. All remaining declared proof dependencies are used. No unit-level
statement or step is bypassed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The general scheme-theoretic normalization/fibre lemma is unnecessary for this finite
separable DVR case. Its original declaration also puts A and L in the same universe,
whereas the item correctly allows independent universes; the direct Mathlib proof avoids
that interface mismatch. The source's telescoping argument is implemented by cancelling
the uniformizer power before taking residues, which avoids an auxiliary ideal-filtration
API and proves the same divisibility result. The arbitrary-residue inertia-order input is
retained: the false equality between inertia order and ramification index is never used.
No existing statement or definition has changed and no consumer adaptation is required.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
