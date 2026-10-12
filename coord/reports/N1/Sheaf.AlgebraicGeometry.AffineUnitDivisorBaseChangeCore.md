## What changed

Proved `AlgebraicGeometry.affine_unit_divisor_base_change_core` with its complete original
signature and public imports unchanged. Added one proof-only import,
`Mathlib.AlgebraicGeometry.AlgClosed.Basic`, for the rational closed-point construction.
Three fully proved private helpers construct germ-compatible restrictions, identify a
stalk-specified rational pullback with its generic-point map, and establish naturality
of restrictions through the open-immersion square. The main proof constructs the boundary
bijection explicitly and applies `Scheme.local_dvr_base_change` coefficient by coefficient.
Updated the node's proof and proof_origin to describe the actual argument; proof_deps stay
unchanged. No other library module or interface is changed.

LeanFinder, Loogle (`Finsupp.domCongr`) and source grep searches found the existing germ,
rational-point, and Finsupp ingredients, but no theorem giving this complete comparison.
The restriction argument was adapted from the already proved
`Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers`; the boundary construction was
adapted from `Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange`, without importing
either module or their Picard theory. The new naturality calculation is proved here.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.affine_unit_divisor_base_change_core`
(node `lem-sc-affine-unit-divisor-base-change-core`).
Added zero holes; no declaration in this delivery contains `sorry`. All three private
helpers are proved. This is a proof from existing library declarations, not a decomposition.
The single-file compiler passes without warnings. A separate `#print axioms` check shows
`propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`; the existing proof
closure is not yet axiom-complete. No axiom is added by this delivery.

## No longer needed

None of the original imports, nodes, or proof dependencies is removed. The temporary
proof import `Sheaf.AlgebraicGeometry.BaseChangeCurve` was removed: surjectivity of the
first projection already gives the nonemptiness needed for the second restriction map.
It is not claimed as a pruned baseline module, and remains used inside LocalDvrBaseChange.
The argument needs neither a finite enumeration of the boundary nor Picard classes;
BoundaryPointClassBaseChange and BoundaryDivisorKernelPowers are read for existing proved
constructions but are not imported. No new work on either is required by this proof.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The original plan overstates the need
for finiteness of the boundary: the first projection can be inverted directly after proving
bijectivity. Its closedness follows from dimension one and the nonempty open. The key
compatibility left implicit in the plan is now a complete Lean calculation using generic
points, stalk specialization, fraction-field uniqueness, and appLE composition.
The unit route is unchanged: this proves the forward boundary-divisor comparison in the
affine unit-quotient step, and does not bypass principal-divisor descent or other unit steps.

## Second reading by N1

1. Compared the complete delivered module and node with the repository versions. The
   existing theorem signature is byte for byte unchanged; no definition or public
   declaration was added or changed. Restored the original theorem docstring, removing
   an unnecessary documentation edit. The only added import is proof-only.
2. The module compiles without errors or warnings. Source inspection found no sorry or
   forbidden declaration mechanism. A scratch copy with explicit `#print axioms` checks
   shows only propext, Classical.choice and Quot.sound for all three private helpers;
   the main theorem additionally inherits sorryAx from the existing library closure.
   No arbitrary data is extracted from an unproved existence statement: the restrictions
   are constructed, the boundary equivalence inverts an explicit bijection, and the
   local rational pullback is uniquely specified on a stalk fraction field.
3. No statements were split off and no holes were added. Read all three private helper
   proofs: open-stalk injectivity gives restriction compatibility, fraction-field
   uniqueness gives rational pullback compatibility, and appLE composition gives
   naturality in the square. Checked the empty-boundary case, where extensionality is
   vacuous, and identity field extension, where fibre uniqueness forces the usual
   identification. Independent grep search for stalk specialization, germ pullback and
   function-field maps found the existing Mathlib naturality ingredients already used,
   rather than a replacement for the complete theorem.
4. Reviewed the proof from the target down, including the existing boundary and germ
   constructions in BoundaryPointClassBaseChange and BoundaryDivisorKernelPowers.
   Reusing their local arguments avoids importing their unrelated Picard or kernel
   results. Confirmed the added AlgClosed.Basic import is necessary by compiling a
   scratch copy without it: pointOfClosedPoint and its properties are unavailable.
   Both public imports are needed by the signature; LocalDvrBaseChange supplies the
   actual order comparison. All old proof dependencies remain used, so the pruning
   list is complete (none). Read the unit record: its affine unit-divisor route stays
   intact; neither the principal-divisor descent nor another unit step is bypassed.
5. Compared the node changes with the Lean argument. Only proof and proof_origin
   changed; proof_deps is exactly the union of the steps' uses and remains unchanged.
   The three steps describe the constructed restrictions, inverse boundary projection,
   and coefficientwise local-DVR argument. No new nodes or change records are needed.

Second reading changed only the unnecessary rewrite of the existing theorem docstring,
restoring its repository text, and added this review. The Lean proof needed no repair.
