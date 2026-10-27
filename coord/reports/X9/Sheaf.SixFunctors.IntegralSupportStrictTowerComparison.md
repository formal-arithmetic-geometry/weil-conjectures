## What changed

Replaced the sole hole in
`WeilConjectures.IntegralSystemRealization.integralSupportStrictTowerComparison`
by an assembly of whole-system natural isomorphisms. The already proved composition
calculation is factored as a private evaluation lemma so Lean elaborates it separately
from the chosen-tower cancellation. The native open and direct
comparisons are whiskered and composed. Naturality of the prescribed proper
finite evaluation identifies their composite with `supportEvaluation`.
The existing `qcqsCompactSupport_nativeTowerComparison`, specialized to the fixed
`calculus`, compares this native composite with the exact tower chosen by
`exists_compactSupportReductionTower`. Its inverse, together with completed
scalar restriction, gives the required tower isomorphism. Cancellation and
naturality of `coefficientRestrictedEvaluationIso` prove the requested evaluation
formula with the original chosen evaluations. No reconstruction hypothesis is
introduced and no equality is deduced from faithfulness of derived evaluations.

The two new primitive modules explicitly construct the ordinary direct-image
comparison, its exact derived inverse-image comparison, its right-adjoint
conjugate, and the open left-adjoint comparison. These constructions use the
existing normalized ring-map and adjunction APIs. Their remaining statements
are only the finite evaluation identities for these specified isomorphisms.
No new definition chooses data from an unproved existence theorem.

All existing declaration signatures, definitions and public imports are retained.
Only the item's proof, two new modules, and their DAG records are changed.

## Proved and sorry left

Closed the original textual hole in
`WeilConjectures.IntegralSystemRealization.integralSupportStrictTowerComparison`
(node `lem-sf-integral-support-strict-tower-comparison`) by a complete proof from
named statements. The item has zero remaining textual holes.

Added two holes, each the entire proof of one public named theorem:

- `WeilConjectures.IntegralSystemRealization.integralNativeDirectComparison`,
  node `lem-sf-integral-native-direct-comparison`.
- `WeilConjectures.IntegralSystemRealization.integralNativeOpenComparison`,
  node `lem-sf-integral-native-open-comparison`.

This is a decomposition: 1 upper hole closed, 2 primitive holes added, net +1
textual holes in this packet. It is not an unconditional proof of the original
geometric normalization. The existing native-tower comparison is reused with
its unchanged statement and existing hole, not restated or counted as a new hole.
The explicit ordinary, inverse-image, open and direct isomorphisms contain no holes.
The full item proof compiled remotely in 24.9 seconds with the default heartbeat
limit. Its final verification is performed by `deliver3.py` after removal of all
temporary profiling options and checkpoints. Both primitive files also compiled.
The private generic evaluation lemma avoids expensive concrete rewrites and the
native comparison is projected directly, avoiding expensive pattern elaboration.

## No longer needed

No original import was removed, no module was withdrawn, and no upstream
declaration was changed. The redundant explicit proof import of
`IntegralNativeDirectComparison` was removed: the open comparison module publicly
imports it because its definition uses the native inverse-image comparison. The two original public imports supply the statement.

The original direct dependency `def-sf-integral-system-canonical-bridge` /
`Sheaf.SixFunctors.IntegralSystemCanonicalBridge` is not needed: only its
ordinary/direct and open comparisons were relevant, and the new modules construct
these directly against `VaryingRing` using the ring-map normalization.
No compositor, proper/open pasting, tensor bridge or global realization model is
constructed or imported.

`lem-sf-compact-support-restriction-of-scalars` /
`Sheaf.Paper.SfCompactSupportRestrictionOfScalars` is no longer a direct proof step
of this item's assembly. The chosen-tower/native comparison already supplies the
whole restricted tower. The restriction-of-scalars theorem remains in the existing
native-tower dependencies, so this is not a claim of global pruning.
The existing coefficient calculus remains required for the fixed reduction and its
finite evaluations. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing `qcqsCompactSupport_nativeTowerComparison` already states precisely
the comparison with the chosen compact-support reduction tower, with its original
finite evaluations, for any specified coefficient calculus. The old plan did not
name this reusable declaration. Repeating its reduction and chosen-tower argument
would duplicate an existing obligation.

The remaining gap lies before integral reduction or compactification: normalization
of the explicit native direct/open presentation changes at finite evaluation.
Each new statement is strictly smaller than the item: it involves a single
geometric operation on arbitrary derived systems, has no compactification, no
input reduction, no chosen support tower or chosen evaluation family, no field of
definition for schemes, and no conclusion about a composite support tower.
Both specified isomorphisms are constructed outright; the holes only assert their
evaluation equations. `ordinaryOpenFiniteEvaluation` was also checked: it supplies
an ordinary counit equation for an existential finite left adjoint, rather than the
specific derived comparison and finite coordinate change asserted here. The ordinary ring-map, inverse-image localization, and
adjoint uniqueness constructions are not postponed.

Edge cases were checked in the formulation: n=0 is exponent 1; zero inputs use
zero morphisms; empty and identity opens use the same adjunction formulas.
There is no properness assumption in the primitive direct comparison, no
normalization condition on derived input, and no flatness assumption on quotient
maps. Neither primitive theorem packages the original statement under another name.

## New nodes

`lem-sf-integral-native-direct-comparison` in
`Sheaf.SixFunctors.IntegralNativeDirectComparison` records the finite evaluation
normalization of the explicitly constructed right-adjoint conjugate. Its ordinary
section comparison and exact inverse-image comparison are also explicit definitions
in that module.

`lem-sf-integral-native-open-comparison` in
`Sheaf.SixFunctors.IntegralNativeOpenComparison` records the finite evaluation
normalization of the explicit open left-adjoint uniqueness comparison.

Both nodes retain the item's chapter/unit and source ancestry, contain complete
proofs in words and recorded LeanSearch, LeanFinder, Loogle and Mathlib grep
searches, and attach their exact Lean theorem statements and their explicit helper
declarations. No existing interface
change requires a change record.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
