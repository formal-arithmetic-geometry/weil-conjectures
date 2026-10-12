## What changed

The second reader rejected the first worker's component theorem: existence of a
natural transformation with invertible components is equivalent to existence of
the original natural isomorphism. Removed that module and node from the delivery.

Added `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffineQuotientCone` instead.
Its definition `AlgebraicGeometry.coherentFormalModules_affine_quotientCone`
constructs the cone using the actual tilde/global-sections unit and cokernel
quotient projections; its cone naturality is proved. The theorem
`AlgebraicGeometry.coherentFormalModules_affine_quotientCone_complete` states only
the limit and residue-scalar properties of that explicit cone, independently of
`L`, `p`, and their naturality and scalar hypotheses.

The original theorem now compares the two limiting cones over A, proves that the
comparison is linear over the completion by evaluating each scalar's residue,
proves naturality using the actual quotient maps and the assumed naturality of p,
and assembles the resulting linear equivalences in the full subcategory. Its
signature and public imports are unchanged. No existing definition was altered.
All new imports in the original module are proof-only. No change record is needed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.coherentFormalModules_affine_complete`
(node `lem-weil-pbc-coherent-formal-modules-affine-complete`). Its complete Lean
proof uses the strictly smaller canonical-cone theorem below.

Hole added and still open:
`AlgebraicGeometry.coherentFormalModules_affine_quotientCone_complete`
(node `lem-weil-pbc-coherent-formal-modules-affine-quotient-cone`). Its docstring
contains its source and full mathematical proof. There are no other delivered
sorries, including none in definitions or local helper proofs.

This is a decomposition: one original hole closed and one lower hole added,
net zero holes, not an unconditional proof of the module or a claim of ledger
progress. The canonical-cone construction and its transition compatibility,
the B-linearity of the comparison, and its naturality are proved in Lean.
The rejected `coherentFormalModules_affine_complete_components` is not delivered.

Both final modules compile locally with no errors or warnings. Explicit
`#print axioms` scratch copies showed `[propext, Classical.choice, Quot.sound]`
for the cone definition, and only those plus `sorryAx` for the two theorems.
The latter dependency is expected while the named canonical-cone theorem and
existing upstream statements remain open. No nonstandard axiom or unchecked
implementation feature was used. Scratch copies are not delivered.

## No longer needed

Removed the original module's direct proof imports:

- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
- `Sheaf.RingTheory.AdicCompletionNoetherian`
- `Sheaf.RingTheory.FiniteModuleComplete`
- `Mathlib.RingTheory.AdicCompletion.LocalRing`

They remain ingredients of the lower canonical-cone theorem and are imported
there. Consequently this delivery claims no modules pruned from target closure.

Every old proof dependency absent from the original node's new direct dependency
list is listed here:

- `lem-weil-pbc-module-completion-complete`
- `lem-weil-pbc-adic-completion-noetherian`
- `lem-weil-pbc-finite-module-complete-over-complete-noetherian`
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`

These are now used by the lower node, so none is globally obsolete. The original
quotient, affine tilde/Gamma, and completion-definition nodes remain direct uses.
The rejected component module/node was new in the first worker's sandbox and
never needed by the repaired argument; it is removed rather than landed and pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker changed only the categorical packaging of the conclusion and
left all mathematical and naturality work in an equivalent new sorry. That was
not a genuine reduction. Its claim that the component statement was strictly
intermediate was wrong, and its docstring did not give the required proof.
The second reader replaced it with the canonical quotient-cone property and
formalized the comparison, scalar compatibility, and functoriality arguments.
The existing DAG plan already described those arguments; no change in the unit
route is justified or made.

The literature files are not materialized in this local clone. The reader checked
the primary source pages directly: https://stacks.math.columbia.edu/tag/087W,
https://stacks.math.columbia.edu/tag/05GG, and
https://stacks.math.columbia.edu/tag/00MA. Tag 00MA (3) is the completion-tensor
formula; completeness of a finite module over a complete Noetherian ring follows
by identifying that tensor product with the module itself.

## New nodes

`def-weil-pbc-coherent-formal-modules-affine-quotient-cone` records the real
canonical cone construction and the proved cokernel transition compatibility.

`lem-weil-pbc-coherent-formal-modules-affine-quotient-cone` records the remaining
limit and residue-scalar properties of that explicit construction. It has no
candidate inverse functor or natural comparison in its statement. Its mathematical
proof follows completion modulo ideal powers, finite-module completeness, and the
affine ideal-product/cokernel comparison already named in the original plan.

Both nodes retain chapter `sec-proper-base-change` and unit `sk-thm-p1`, have
verbatim Lean signatures, provenance, sources, and three kinds of successful
search (Loogle, LeanFinder, grep), plus the recorded failed LeanSearch request.
Searches found general completion and limit-comparison APIs, not this assertion
about the project's formal sheaf quotient construction. There are no change records.

## Second reading by N4

1. Compared the original module against the repository using `diff` and checked
   the theorem signature byte for byte with an assertion. Verdict: unchanged
   statement, hypotheses, conclusion, visibility, and existing definitions.
   Public imports are unchanged. Only the proof and proof-only imports changed.
2. Compiled both final modules through `lcompile.py`, scanned for prohibited
   features and remaining sorries, and compiled explicit axiom-printing copies.
   Verdict: valid proofs, one documented new named sorry, no hollow definition,
   and only the permitted axioms plus the expected upstream `sorryAx`.
   The cone is a real construction. Choice selects only `IsLimit` proofs; the
   comparison is the unique map between the specified limiting cones.
3. Rejected the equivalent component restatement and removed it. Checked the new
   canonical-cone statement: for I = bottom the positive quotient tower is the
   constant N tower; for I = top the completion and all its modules are zero;
   for N = zero the statement is immediate. The scalar equation is exactly the
   kernel-of-evaluation formula transported through the affine quotient map.
   Verdict: true and strictly smaller; it contains neither L nor the comparison
   nor functoriality of that comparison. Searched with different queries using
   Loogle, LeanFinder, grep, and a LeanSearch request, and searched project Lean.
   No duplicate was found. Closing the sheaf/quotient identification and limit
   theorem is substantial further work, not a short missing tactic.
4. Used Mathlib's `IsLimit.conePointUniqueUpToIso`, `Concrete.isLimit_ext`, the
   affine unit, and `NatIso.ofComponents`. Removed the superseded proof imports
   from the original module and accounted for all displaced original direct
   dependencies above. Read `dag/units/sk-thm-p1.json`: its realized statement
   and steps are unchanged, and this reduction remains inside the original
   affine-completion argument. Verdict: route preserved; no global pruning claimed.
5. Read both new nodes and the updated original node against the Lean proof.
   The original node now records canonical-cone comparison, the scalar argument,
   and the proved naturality computation. The lower node records precisely the
   remaining affine-completion argument, with the original algebraic dependencies.
   Verdict: statements, proof steps, dependency unions, and provenance agree.

Changes made by the second reader: removed the equivalent component restatement;
constructed the canonical quotient cone; replaced the original proof with a real
cone-comparison, B-linearity, and naturality reduction; added the smaller theorem
and its full proof docstring; repaired nodes, imports, and progress accounting.
