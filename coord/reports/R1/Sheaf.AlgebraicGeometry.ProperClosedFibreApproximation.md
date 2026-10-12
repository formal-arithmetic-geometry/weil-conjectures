## What changed

Replaced the saved attempt entirely. The signature of
`AlgebraicGeometry.Scheme.exists_proper_closedFibre_approximation` is unchanged.
Its complete assembly proof now applies `exists_proper_limit_noetherian`, uses its
actual affine-base clause, transports that approximation to rings, and applies a
quotient-fibre transfer theorem with explicit limit, colimit, affine-transition,
and commuting-square hypotheses. Compactness and quasi-separatedness are proved
using Mathlib on the composite of each stage isomorphism and proper pullback
projection. The final existential witnesses and all three compatibility equations
are assembled in Lean.

Added `Sheaf.AlgebraicGeometry.AffineApproximationRingPresentation`, whose theorem
is fully proved: its ring diagram is the global sections of the supplied affine
base diagram, the proper morphisms are transported through canonical affine
isomorphisms, and the ring cocone is transported through the global sections of
Spec A isomorphism. Added `Sheaf.AlgebraicGeometry.QuotientFibreLimitTransfer`
for the remaining quotient-diagram/pullback-limit construction. Updated the
original node's proof route and added accurate nodes for both new declarations.
No existing definition, statement, or public import changed. No forced adaptations
or change records are needed.

Validation: all three modules compiled in import order with `lcompile.py --all`,
without errors or warnings. Both cited Stacks source pages were read online:
https://stacks.math.columbia.edu/tag/0GS2 (General case), and
https://stacks.math.columbia.edu/tag/0A0P. Edge cases of the transfer statement
were checked mathematically: the unit ideal gives empty fibres, the zero ideal
recovers the original system, the zero ring gives empty spectra, and noninjective
stage maps still give injective maps on quotients by the inverse-image ideals.
The remaining lemma does not assume properness or finite type, so it is a genuine
part of the argument, independent of constructing proper integer models.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.exists_proper_closedFibre_approximation`
(node `lem-weil-pbc-proper-closed-fibre-approximation`). This is a decomposition,
not a proof free of sorry dependencies: one original hole closed, one hole added.

Fully proved the new theorem
`AlgebraicGeometry.Scheme.affine_approximation_ring_presentation`
(node `lem-weil-pbc-affine-approximation-ring-presentation`).

The only sorry in the delivery is
`AlgebraicGeometry.Scheme.quotient_fibre_limit_transfer`
(node `lem-weil-pbc-quotient-fibre-limit-transfer`). It is a public theorem in its
own module, with proof exactly `by sorry`, its source and complete proof in words
in the declaration docstring, and its exact signature in the node's lean record.
The existing dependency `exists_proper_limit_noetherian` remains responsible for
constructing the proper approximation; its proof dependencies are unchanged.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.LimitAffineTransition`
from the item's module. Its role in obtaining the proper approximation is already
encapsulated by `ProperLimitNoetherian`; its limiting-cone construction is not
called by the assembly. It remains transitively reachable, so no global module
pruning is claimed.

Pruned unused Mathlib imports from the new modules: `Pullbacks` from the ring
presentation, and `Proper` and `FiniteType` from the general transfer statement
(which imports `Morphisms.Affine` for its actual affine-transition hypothesis).

The original node's direct dependencies
`def-pc-fibre-product`, `def-weil-proper-morphism`,
`lem-weil-pbc-affine-morphism-permanence`,
`lem-weil-pbc-closed-immersion-base-change`,
`lem-weil-pbc-filtered-colimit-algebras-elementwise`,
`lem-weil-pbc-limit-affine-transition`,
`lem-weil-pbc-proper-base-change`, `lem-weil-pbc-qcqs-morphism-permanence`,
`lem-weil-pbc-spec-colimit-limit`, and `pqf-def-affine-morphism`
are replaced by the three direct proof dependencies recorded in the updated node.
The quotient construction dependencies are retained in the new transfer node;
proper base change and qcqs permanence in the final assembly use Mathlib directly,
so the separate Sheaf wrapper modules for those two facts are unnecessary here.
No unit statement or realized proof step is bypassed.

Discarded the saved attempt's Core, Properties, and Stages modules and nodes.
They were sandbox-only files, never delivered by this worker. None is imported or
needed by the replacement proof.

## Where the brief, the DAG or earlier work was wrong

The saved Properties and Stages theorems quantified over arbitrary diagrams and
cones, without a hypothesis connecting them to the chosen approximation. They
are false: a cone from an empty closed fibre can map to an arbitrary constant
scheme diagram, including a non-quasi-compact scheme; no finiteness or finite-type
model conclusion follows. The saved Core statement also did not carry the
approximation data needed to justify either later statement. These invalid
sandbox-only declarations were removed, rather than used as assumptions.

The saved metadata had placeholder natural-language statements and lean.statement
fields, inherited maintainer review fields, and module comments in place of
proper declaration docstrings. The replacement nodes are written afresh with
self-contained statements, full Lean signatures and numbered proof steps.
The saved report's second-reading section was removed: the independent reader
must write their own verdict on this replacement delivery.

## New nodes

`lem-weil-pbc-affine-approximation-ring-presentation`:
`lean/Sheaf/AlgebraicGeometry/AffineApproximationRingPresentation.lean`.
This proved categorical presentation lemma transports an already supplied affine
proper approximation through global sections and the affine-scheme isomorphisms.
It constructs no closed fibres and does not repeat the item's conclusion.

`lem-weil-pbc-quotient-fibre-limit-transfer`:
`lean/Sheaf/AlgebraicGeometry/QuotientFibreLimitTransfer.lean`.
This remaining lemma constructs closed fibres of an already supplied scheme limit
and ring colimit, with the canonical projection identities and affine transitions.
It needs neither properness nor finite-type rings. Its proof plan separates the
quotient-ring colimit, the pullback limiting property, and affine transitions.

## Second reading by R1

1. **Statements and interfaces.** Compared the delivered target module with the
repository version. The theorem signature is unchanged; only proof imports and the
proof body differ. The two added declarations have self-contained signatures, and
their DAG `lean.statement` fields match the source. Verdict: pass.

2. **Proof hygiene.** Compiled all three modules in import order with
`python3 /home/ubuntu/weil-launcher/lcompile.py --all`; compilation completed without
errors or warnings. The only remaining `sorry` is the named public theorem
`AlgebraicGeometry.Scheme.quotient_fibre_limit_transfer`; there are no axioms, unsafe
declarations, hollow definitions, or hidden `sorry`s. Verdict: pass.

3. **Truth and strength of split statements.** Checked the quotient-transfer edge cases
(`I = ⊤`, `I = 0`, zero rings, and noninjective stage maps) and the affine-factorization
argument for transitions. The transfer theorem is a genuine intermediate result,
strictly weaker than the proper approximation target, and its hypotheses are used by
the assembly. The affine presentation theorem is fully proved and transports exactly
the supplied approximation data. Verdict: pass.

4. **Shortest route and pruning.** The assembly uses the existing proper Noetherian
approximation, the proved affine ring presentation, and the one necessary split-off
quotient-transfer lemma. The former direct `LimitAffineTransition` import is unused and
removed; the updated target node records the three actual proof dependencies. No unit
statement or realized route is bypassed. Verdict: pass.

5. **DAG and documentation.** The target and both new node records agree with the Lean
declarations, include sources, proof steps, dependency lists, and exact signatures.
The split theorem has a complete natural-language proof in its docstring and is reported
as the sole added hole. Verdict: pass.

Changes made during second reading: none; the delivered files passed the checks above.
