## What changed

Restored lean/Sheaf/AlgebraicGeometry/CanonicalSingleBaseChangeComparison.lean
from its assigned quarantine archive. The archived theorem did not elaborate:
unqualified derivedPullback resolved to Scheme.Modules.derivedPullback after
the upstream sync, conflicting with the pinned comparisons on the shared derived
categories. Explicitly qualify AlgebraicGeometry.derivedPullback and specify the
existing u,w universes. The arbitrary commutative square, arbitrary module,
universes, hypotheses, canonical map definitions, and theorem name are retained.

Give the right-derived unit an explicit natural-transformation type when applying
naturality. Respect the existing functors' transparency boundaries during
elaboration; remove the initial dsimp of scheme aliases, which breaks the current
simplifier's implicit-transparency type check. The complete proof still applies derivedBaseChange_unit_compatibility
at M[0], transports it through the homotopy single-object comparison using the
two naturality squares, then cancels the tensor-to-ordinary pullback isomorphism.
The final identification with the public canonical maps is definitional (exact hf).
All four private category helpers are fully proved; the additional helper performs
reassociation in an arbitrary category before specializing to the scheme functors. No adopted source file is
changed and no further mathematical statement is split off.

The existing node is retained with all statement/proof dependencies and its Lean
attachment. Its Lean statement text records the qualified functor. Change record:
coord/changes/T2-canonical-single-base-change-restoration.md.

## Proved and sorry left

This is a restoration/repair with 0 original direct holes and 0 final direct holes.
The theorem AlgebraicGeometry.Scheme.Modules.canonicalSingleBaseChangeComparison
(node lem-sc-canonical-single-base-change-comparison) has a complete proof.
Holes closed: none (0 of 0). Holes added: none. Sorries left in the delivered
modules: none. Split-off theorems: none. This repair claims no net hole reduction.

Validation: the complete restored module compiles through lcompile.py in 50.0 s,
with no errors or warnings. The original archive was compiled first and failed
with the recorded universe mismatch; this is a concrete repair rather than a rebase.

## No longer needed

None. No imports, nodes, modules, declarations, parent dependency edges, or unit
steps are pruned. Both declared proof lemmas are used. The four public imports
provide the canonical maps and ordinary and derived exchange appearing in the
statement. The two quarantined parents CanonicalStructureMapBaseChange and
Picard.TensorSingleBaseChangeSquare remain obligations, with their dependencies
on this theorem preserved.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes proving holes, but this specific rework item
has zero direct holes in its preserved archive. Its assigned defect is restoration
against the changed upstream environment. The unqualified derivedPullback was
formerly the intended AlgebraicGeometry declaration; the newly imported namesake
in Scheme.Modules shadows it and produces the observed Type u / Type w error.
Qualifying the intended pinned functor repairs that error without changing the
mathematical statement or imposing w = u.

The node's existing naturality/cancellation argument is sufficient. Searches of
the current source and Sheaf trees, LeanFinder, Loogle, and the launcher grep
service found the existing derived-unit and homotopy-single comparisons, with
no shorter exact theorem replacing this item. Stacks cohomology.tex,
remark-base-change (Tag 08HY), gives the mate construction used by that argument.
The unit sk-prop-av-cube has no realized entries bypassed by this repair.

The source-only downstream.py query reports unknown module because the live
lean/ path is absent. Scanning lean/, quarantine/, and the DAG instead locates
exactly the two quarantined parents named above; neither requires a changed
mathematical interface. No parent is withdrawn or made empty.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
