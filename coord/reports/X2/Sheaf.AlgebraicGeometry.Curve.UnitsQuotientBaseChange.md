## What changed

Proved AlgebraicGeometry.units_quotient_base_change with its statement unchanged. The proof
uses the existing compactification, baseChange_curve, and affine_unit_divisor_base_change
declarations. A proved private group lemma constructs the map on nth-power quotients and
checks injectivity, surjectivity, and its equation on representatives.

Added Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers with the fully proved theorem
AlgebraicGeometry.boundary_divisor_kernel_powers. It identifies the function-field map using
germ compatibility, extends a zero-divisor unit across the boundary using existing proved
regularity lemmas, identifies it with a constant, and extracts its nth root.

Local compilation of both modules passes. The compactification route of the unit is retained.
The kernel lemma also covers n = 1, characteristic dividing n, and an empty boundary: in the
last case all units are constants. No characteristic restriction is used.

## Proved and sorry left

Proved AlgebraicGeometry.units_quotient_base_change (lem-sc-units-quotient-base-change),
AlgebraicGeometry.boundary_divisor_kernel_powers (lem-sc-boundary-divisor-kernel-powers), and
private quotient_powers_equiv. No sorry remains in either delivered module; none is added.
The proof still depends on the existing affine_unit_divisor_base_change statement, which is
left for its own stage-3 item. The kernel theorem also rests on sorry through the existing
GlobalSectionsBijective.of_isAlgClosed instance (lem-sc-global-functions). Neither geometric
theorem is yet axiom-closed; their proof bodies contain no sorry. This is a reduction from
the planned named dependencies.

## No longer needed

Removed direct proof imports:
- WeilConjectures.AlgebraicGeometry.Curve.DivisorSequence
- WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective (used transitively in the new kernel module)
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

The old direct proof edges removed are lem-sc-divisor-exact-sequence, def-sc-field-extension,
and lem-sc-global-functions (the last is retained indirectly via the new kernel theorem).
The new module also drops redundant imports of Curve.DivisorIdealSheaf and
GlobalSectionsBijective; both remain available through its required imports.
Its kernel argument uses the proved source-library regularity/gluing lemmas instead of the
sheaf divisor-sequence theorem. lem-sc-global-functions remains needed through the kernel
lemma; compactification, base-change-curve, and affine-unit-divisor-base-change remain needed.
These are removals of direct edges, not claims that the modules disappear from every target's
closure (the affine boundary-divisor dependency may still reach them transitively).

## Where the brief, the DAG or earlier work was wrong

No false statement or signature change was found. The existing Affine.finite_units_quotient
proof contains a usable kernel-to-constants argument, and DivisorIdealSheaf provides a proved
regularity lemma; the DAG's sheaf divisor-sequence route is unnecessary for this kernel step.
The full original source literature file is absent from this machine; the argument is taken
from the provided node's detailed proof and the read-only source-library proof it follows.

## New nodes

lem-sc-boundary-divisor-kernel-powers: the zero boundary-divisor kernel is contained in nth
powers, over one algebraically closed field, for any smooth connected curve with a smooth
proper connected compactification. This is strictly the kernel step, contains no base-change
assertion, and is fully proved. Its module is
lean/Sheaf/AlgebraicGeometry/Curve/BoundaryDivisorKernelPowers.lean. No change record is needed:
no existing statement, definition, or public import was changed.


## Second reading by X2

1. Compared both delivered modules with the repository. The new kernel module is absent
   there. The existing units_quotient_base_change signature is byte-for-byte identical;
   its public imports and all existing definitions and docstrings are unchanged. Pass.
2. Compiled both modules locally in dependency order, without errors or warnings. No sorry
   or forbidden declaration occurs in either file. Scratch-copy #print axioms checks show
   only propext, Classical.choice and Quot.sound for quotient_powers_equiv. The two geometric
   theorems additionally use sorryAx through existing open dependencies; specifically the
   kernel theorem uses GlobalSectionsBijective.of_isAlgClosed, whose finiteness prerequisites
   remain open. The regularity/gluing and nonzero-order-is-closed lemmas use only the three
   permitted axioms. Pass as a stage-3 reduction, not as an axiom-closed target.
3. No theorem is left sorry or split off as an open obligation. Read the new kernel theorem
   and its complete docstring proof: it proves exactly the kernel-divisibility step and
   contains no base-change assertion. Checked n = 1, characteristic dividing n, and empty
   boundary; positive n is essential for the root's nonvanishing argument. Independent
   LeanFinder, Loogle, Mathlib grep and library searches found the used components and the
   source Affine.finite_units_quotient argument, but no existing theorem with this statement.
   Pass.
4. The proof follows compactification, boundary-divisor compatibility and image equality,
   then kernel divisibility and quotient-map bijectivity. The unit's affine Kummer route is
   retained; its realized field currently has empty lists and is unchanged. No shorter
   existing route was found. The old direct proof dependencies removed are
   def-sc-field-extension, lem-sc-divisor-exact-sequence, and lem-sc-global-functions;
   the last remains an indirect dependency through the new kernel theorem. Pass.
5. Checked the existing node changes are restricted to proof, proof_deps and proof_origin,
   with its statement and Lean record unchanged. The new node's signature matches Lean,
   its metadata and source are present, and the proof-dependency unions match its steps.
   Its global-functions step is non-elementary. Pass after that metadata repair.

Changes made by the second reader: removed redundant proof imports of Curve.DivisorIdealSheaf
and GlobalSectionsBijective from BoundaryDivisorKernelPowers (both are exposed by its needed
imports); corrected the new node's global-functions step to elementary:false; clarified
inherited sorryAx and the complete list of removed direct DAG edges. The existing theorem's
historical docstring still describes the divisor-sequence route; its current replacement
kernel route is documented in the delivered DAG and this report.

The redundant imports removed from the new module are not claims that their modules can be
pruned from the target closure: both remain transitively needed.
