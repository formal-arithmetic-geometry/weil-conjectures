## What changed

Replaced the hole in
`AlgebraicGeometry.Scheme.Modules.moduleStrictTransform_shortExact_of_universallyShortExact`
by a complete assembly from the two existing stated dependencies
`universalExact_affine_power_reduction` and `principalSupportQuotient_exact`, and the
new affine-local supported-quotient comparison statement described below.
The existing theorem signature, strict-transform definitions, canonical map definition,
and both public imports remain unchanged.

Two private helpers are fully proved in the item module:
`exists_principal_affine_chart` constructs compatible affine spectra, their actual ring
map, and the equality of the centre complement with the principal open. It uses
principalization, the affine-open basis, the support/zero-locus formula and the naturality
of `fromSpec`. `quotSMulTop_map_injective_of_divisibility` proves injectivity on scalar
quotients by lifting a representative and applying the divisibility implication.
The main proof obtains that implication from the existing affine-power lemma, applies
the existing principal-support quotient theorem, and supplies the actual chart data to
the final geometric comparison. Its final identification with the original canonical
strict-transform maps is checked by Lean's definitional equality.

Added `Sheaf.AlgebraicGeometry.OpenSupportQuotientLocalExact`: explicit, canonical
kernel/cokernel quotient and map definitions, and one general affine-local comparison
and descent theorem. This avoids an import cycle with the item's map definition.
The theorem's source and full proof in words are in its docstring and new node.
Updated the item's DAG proof and dependencies to record this assembly.

## Proved and sorry left

Original holes: 1. The original theorem's hole is closed by its complete Lean assembly.
The item module now has 0 holes. Both private helpers have complete proofs.

Added holes: 1, the public theorem
`AlgebraicGeometry.Scheme.Modules.openSupportQuotient_shortExact_of_affine`
in `Sheaf.AlgebraicGeometry.OpenSupportQuotientLocalExact`, node
`lem-trf-open-support-quotient-affine-local-exact`.

This is a decomposition: one upper hole closed and one strictly smaller geometric hole
added, for net 0 holes. The new theorem contains neither a blowup nor a universal
base-change hypothesis; it only compares and descends already short exact principal
supported-section quotient sequences. All universal-exactness-to-powerwise-injectivity
and torsion-quotient arguments are supplied by the existing declared dependencies.
Their own holes are unchanged and are not claimed as closed here.

Edge cases checked mathematically for the new statement: empty Y (empty-cover sheaf
axiom); a=0 or nilpotent (the local quotient is zero); a a unit (the quotient is the
original module); zero rings, zero divisors, and arbitrary non-finite affine covers.
No finiteness, regular-element, or affine-morphism assumption is hidden in it.
All new data definitions are explicit categorical constructions, with no admitted
existence theorem used to choose an object.

Validation: `lcompile.py --all` compiled both modules successfully. The new comparison
module took 0.1 seconds using its unchanged cached compile, and the item took 19.3
seconds, below the 60-second per-file limit. There were no compiler warnings.

## No longer needed

Removed these direct proof imports from the item:

- `WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackQCoh`
- `Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `WeilConjectures.AlgebraicGeometry.TensorPullbackTilde`
- `WeilConjectures.Mathlib.Algebra.Module.Torsion`
- `Mathlib.Algebra.Module.LocalizedModule.Basic`
- `WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits`
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`

The item no longer directly proves the lower affine, tilde, localization or torsion
calculations; the two existing child statements already provide them. These imports
may still be needed transitively by those children; no global module withdrawal is
claimed. Every original direct DAG dependency is used and retained. Removed the
item's obsolete direct `tool_uses` approvals for
`lem-pc-ringed-space-tensor-pullback-qcoh` and
`lem-sc-tilde-preserves-finite-limits`: the assembly does not apply them directly.
Their mathematical content remains in the existing children's plans.

## Where the brief, the DAG or earlier work was wrong

The item's old Lean docstring presents the original seven-step proof, whereas its
current DAG has already factored most of those steps into two stated dependencies.
The Lean file had not imported either child. This delivery follows the current DAG
and uses both children rather than reproducing their arguments. The remaining
comparison of tensor restriction, principal support quotients and the global sheaf
sequence needs an explicit Lean statement; it is the new node.

No statement is disputed, no existing statement or definition is repaired, and no
other existing Lean module or node is edited. The unit route is preserved. The
printed final-variable typo in Stacks 080W was already corrected in the existing
principal-support child and does not require a new repair here.

## New nodes

`lem-trf-open-support-quotient-affine-local-exact` is the geometric comparison and
local-to-global step of Stacks 080D/080W, using sheaf exactness as in Modules 01AF/01AG.
It states that a cover of compatible principal affine charts, with invertible
natural tilde/Gamma counits and short exact principal support quotients, gives the
short exact global quotient sequence with its actual induced maps. The docstring
and node explain restriction of kernels/cokernels, counit naturality, identification
of the maps by cokernel cancellation, and descent of mono, middle exactness and epi.
The node inherits the chapter, unit and blueprint ancestry of the item. Searches
by LeanSearch, Loogle and Mathlib grep, plus a source-library and DAG-title search,
found no existing statement giving this complete map comparison and descent.
There are no change records because no existing interface changes.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
