## What changed

Retired Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor under
coord/retire-items.tsv row 1047 and the human's 2026-10-20 retirement hand-off.
The copy already has zero holes; its official WeilConjectures twin proves the
same factorization using exteriorPower and wedge. The copy is in deleted.txt.

Both direct consumers, DeterminantLiftWedgeKernel and
DeterminantWedgeMorphismLocalAt, replace the copy's private import by the official
twin and the existing ExteriorSheafPowerComparison module. A fully proved private
compatibility bridge conjugates the given q and psi by canonical comparison maps,
checks the upstream generator formulas, applies the official theorem and transports
the factorization back. Generator extensionality checks the final equation.
Their existing public signatures, definitions, attributes, docstrings and public
imports remain unchanged. No upstream or target file changes.

The factorization node now points to the official declaration with its signature
verbatim and records the official proof. Both parent nodes retain the factorization
step and record the private comparison transport. No unit or chapter route changes.
The change record is coord/changes/A5-retire-determinant-wedge-quotient-factor.md.

Validation: lcompile.py --all compiled both consumers without warnings in 17.1 and
18.6 seconds. A separate compile of an axiom-check module reports only propext,
Classical.choice and Quot.sound for the official determinant_wedge_quotient_factor
and both consumer public theorems. Byte-for-byte signature/public-import checks
passed, and all delivered Lean lines fit 100 columns. An overlay import scan finds
zero references to the retired copy and zero Sheaf/WeilConjectures twin pairs in
either adapted consumer's environment. The only DAG parents are the two adapted
nodes; both continue using the reattached factorization node. No quarantine/rework
entry refers to the item.

## Proved and sorry left

Zero holes closed of zero initial holes, zero holes added, zero split off and
zero holes left. This is a retirement repair, not a hole closure or decomposition.
The official AlgebraicGeometry.Scheme.Modules.determinant_wedge_quotient_factor
is fully proved and reused. The new private determinant_wedge_quotient_factor_compat
and exteriorSheafPowerIso_hom_wedge helpers in each consumer are fully proved.
AlgebraicGeometry.Scheme.Modules.determinant_liftWedge_kernel_exists and
AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_local_data_at remain
fully proved with unchanged statements.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor.
Both consumer proof imports now name its official twin. The retired copy's direct
use of ExteriorSheafTensorQuotientComparison and its private tensor/kernel
comparison argument is replaced by the official theorem. That comparison module
remains used by DeterminantWedgeMorphismGlue and is not withdrawn.

The factorization node's direct proof no longer needs
lem-sc-exterior-sheaf-tensor-quotient-comparison or
lem-sc-exterior-sheaf-power-comparison. The official proof uses
new-exterior-tensor-quotient and lem-sc-exterior-tensor-lift-hom-ext instead;
new-j1-exterior-sheaf-rank-wedge-zero and new-j1-exterior-tensor-kernel-relations
remain used. The power comparison is now recorded explicitly at both consumers.
No mathematical node, rank argument or unit step is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an unfinished split, but the current source
already proves this item and the queue marks it as retire. Merely compiling the
existing proof would not fulfill the retirement assignment. The official theorem
uses a different exterior-sheaf implementation, so replacing its import alone
fails at q's type; the explicit proved comparison bridge is necessary.

Initial cancellation attempts caused excessive elaboration of tensor isomorphism
maps. The final proof uses the existing local-generator extensionality API and
explicit section formulas, compiling comfortably within the file limit without
changing any definition or splitting the obligation. All degrees, including zero,
empty schemes and zero rings are covered without extra assumptions.

Logged searches through msearch.py (LeanFinder, Loogle and grep), together with
repository searches, identify the official factorization theorem and existing
comparison/extensionality APIs as the shortest route. Neither consumer is held by
another group, so no forced adaptation exception is needed. No new nodes, public
declarations, data constructions or proof holes are introduced.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
