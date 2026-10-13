## What changed

Proved `Ideal.height_eq_one_of_mem_associatedPrimes_quotient_span` in
`Sheaf.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight` without changing its
signature or public imports. Serre's criterion supplies S2 from normal prime localizations;
the existing `Ideal.height_le_one_of_mem_associatedPrimes_regular_quotient` supplies the
upper bound. The proof then shows `a ∈ p`, rules out `p = ⊥`, and obtains the lower bound
using Mathlib's characterization of height zero in a domain. Updated the item's DAG proof
and dependencies to this route. Local single-file compilation passed without warnings.
No unit-level route changes.

## Proved and sorry left

Closed one hole: `Ideal.height_eq_one_of_mem_associatedPrimes_quotient_span`
(node `lem-weil-pbc-normal-domain-principal-quotient-associated-height`).
No sorry remains in the item's module. No holes added and no new modules or nodes.
This is a proof from existing declarations, not a decomposition into new holed statements.
The imported Serre criterion and S2 upper bound retain their existing downstream dependencies.

## No longer needed

Removed direct proof imports:
- `Sheaf.RingTheory.AssociatedPrimeLocalizeAtPrime`
- `Sheaf.RingTheory.Depth`
- `Sheaf.RingTheory.DepthInSES`
- `Sheaf.RingTheory.DepthLeDimAssociatedPrime`
- `Sheaf.RingTheory.SerreConditions`

Retained `Sheaf.RingTheory.SerreCriterionNormal` and added the proof import
`Sheaf.RingTheory.SerreS2RegularQuotientAssociatedHeight`.

The following old direct DAG dependencies are no longer needed by this module's proof:
- `def-weil-pbc-normal-ring`
- `def-weil-pbc-serre-conditions-rk-sk`
- `lem-weil-pbc-localization-module-exact`
- `def-weil-pbc-module-localization`
- `lem-weil-pbc-localization-noetherian`
- `def-weil-pbc-localization-at-prime`
- `lem-weil-pbc-depth-in-ses`
- `def-weil-pbc-depth`
- `lem-weil-pbc-associated-prime-localize-at-prime`
- `lem-weil-pbc-depth-le-dim-associated-prime`
- `def-weil-pbc-krull-dimension-ring`
- `lem-weil-pbc-localization-dimension-chains-below-prime`

These are direct-dependency removals, not claims that all corresponding modules leave the
whole targets' import closure. Depth and associated-prime ingredients remain used through
the existing S2 upper-bound theorem. `DepthInSES` and the annihilator-localization theorem
are not needed directly here; the upper-bound theorem uses Mathlib localization instead.
No Mathlib public imports were removed.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement found. The original six-step plan repeats the already proved
S2 regular quotient associated-height argument. Reusing it avoids constructing the
localized short exact sequence again. The unit's realized statements and steps are kept.
The unit case for a unit denominator is vacuous (the quotient has no associated primes);
the nonzero denominator is precisely what supplies regularity and excludes height zero.

## Second reading by V3

1. **Diff and interfaces.** The theorem signature is byte-for-byte unchanged from the
repository. The proof-only imports are plain imports; the public imports needed by the
signature are unchanged. Verdict: pass.
2. **Compilation and axioms.** The sandbox module compiles with `lcompile.py` without
errors or warnings, and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by`. The proof uses only the permitted library results. Verdict: pass.
3. **Statement and proof.** The associated-prime argument proves containment of `a`,
excludes the zero ideal, and combines the S2 regular-quotient upper bound with the
domain height-zero characterization. The statement is unchanged and no new statement
was added. Verdict: pass.
4. **Pruning.** The direct localization/depth imports are unused after packaging that
argument in the existing S2 theorem. I also removed the stale DAG dependency on the
localization-normal-domain node, which the Lean proof does not invoke. Verdict: pass.
5. **DAG and unit route.** The node proof and `proof_deps` now match the actual Lean
route, and the unit's realized route remains intact. Verdict: pass.

Changed the DAG proof metadata to remove the unused localization-normal-domain
dependency; no Lean declarations or theorem statements were changed.
