## What changed
Added two strictly smaller intermediate theorem modules and used them to prove the target theorem by composition.

## Proved and sorry left
The target IsLocalRing.complete_local_domain_finite_over_regular is proved. The intermediate declarations complete_local_domain_finite_over_regular_core and complete_local_domain_finite_over_regular_residue remain sorry, each with a dedicated node.

## No longer needed
Removed the proof-only imports `Sheaf.Algebra.ChangeIdealCompletion`,
`Sheaf.RingTheory.ExistsCoefficientSubring`, `Sheaf.RingTheory.FiniteOverCompleteRing`,
`Sheaf.RingTheory.IntegralExtensionDimension`,
`Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete`, and
`Sheaf.RingTheory.PowerSeriesOntoCompletion`. The target now depends for its proof only on
`CompleteLocalDomainFiniteOverRegularCore` and `CompleteLocalDomainFiniteOverRegularResidue`.

## Where the brief, the DAG or earlier work was wrong
The full eight-step Cohen structure proof is too large for this delivery window; it was split into the core construction and the residue/model completion assertions.

## New nodes
split-complete-local-domain-finite-over-regular-core and split-complete-local-domain-finite-over-regular-residue.

## Second reading by Y3
1. Compared the delivered target module with the repository version. The theorem signature is unchanged byte for byte; only proof imports and the proof body differ. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py`. There are no errors, no forbidden declarations, and the only remaining `sorry`s are the two named split theorems, each documented and represented by a node. Verdict: pass.
3. Checked both split statements against the original Tag 032D target. The core theorem supplies only the regular complete finite subring, and the residue theorem supplies only the remaining residue and model properties, so each is strictly smaller than the target and has no weakened target statement. Verdict: pass.
4. Checked the proof route and imports. The target composes exactly the two split declarations; the old eight-step proof-only imports were removed, while Mathlib imports needed by the public signature remain. The unit route is represented by the original target node and its split nodes. Verdict: pass.
5. Checked the DAG nodes against the Lean declarations and report. The split node identifiers, declarations, and remaining holes agree with the files. Verdict: pass.

Changed the target module to make the two split imports proof-only and removed the unused old proof-route imports. No theorem statement or definition was changed.
