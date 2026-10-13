## What changed

Proved `AlgebraicGeometry.affine_perfect_koszul_principal_unit_iso` with its signature
unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.KoszulOpenConeComparison` and
`Sheaf.AlgebraicGeometry.KoszulRestrictionZeroBase`.
The proof identifies the existing tail augmentation with the shifted augmentation,
sheafifies the existing cone comparison, and restricts the distinguished cone triangle.
Positive powers preserve the basic-open union; the existing Koszul restriction theorem
makes the third object zero, so the first morphism is invertible.
Updated the existing node's proof, proof dependencies and proof origin to this route.
The scoped heartbeat allowance accommodates elaboration of the cone comparison;
single-file compilation remains within the 60-second limit.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.affine_perfect_koszul_principal_unit_iso`
(node `lem-sc-affine-perfect-koszul-principal-unit-iso`).
No holes remain in the item's module; no new holes or declarations were added.
This is a proof from existing library declarations, not a decomposition into new holes.
The basic-open exactness and open-cover exactness dependencies of the existing
restriction theorem remain whatever they are in the library.
The proof is uniform for r = 0, r = 1, zero generators, and the zero ring;
there is no assumption of regularity or a nonempty open union.

## No longer needed

None. The original public import `Sheaf.Paper.ShiftedKoszulAugmentation` is needed
by the statement. Both added proof-only imports are used. The full Koszul definition
remains needed through the cone comparison and restriction theorem.
No unit step is bypassed: `sk-thm-picard-duality` has no realized statement or
step listing this node. No previously required module or node is pruned.

## Where the brief, the DAG or earlier work was wrong

The node marked local contraction and open-cover detection as elementary and listed
only the Koszul definition as a proof dependency. Existing library theorems already
package these steps and the cone identification. The updated route names them,
so no duplicate contraction or sheaf-gluing statements are needed.
The two tail augmentations agree definitionally (including the differential signs
and degree-zero exterior-power identification), rather than requiring a new bridge.
No statement or definition was changed.

## Second reading by Y2

1. **Visible declarations and statements — pass.** Diffed the delivered module against the
   repository. The existing theorem signature is byte-for-byte unchanged. Only its proof,
   a scoped heartbeat allowance, and two proof-only imports were added. The node changes
   only `proof`, `proof_deps`, and `proof_origin`; no change record is needed.
2. **Proof and axioms — pass.** `lcompile.py` compiled the module without errors or warnings
   in 26.3 seconds. No local holes or forbidden declarations occur. A scratch-copy probe
   compiled in 23.8 seconds and printed only `propext`, `Classical.choice`, and `Quot.sound`
   for `affine_perfect_koszul_principal_unit_iso`, `koszulOpen_module_cone_comparison`,
   and `isZero_restrict_koszul_base`. In particular, the current compiled supporting
   results have no remaining `sorryAx` dependency.
3. **Split statements and edge cases — pass.** No new statement or split-off hole was added.
   Read the existing supporting statements and the augmentation definitions. The equality
   of augmentations is definitional, and the cone comparison has the correct full complex,
   exponent, and signs. For r=0 or all generators zero the open union is empty; for r=1 the
   restriction inverts multiplication by the positive power. The zero ring also causes no
   exception. No regularity assumption is introduced.
4. **Shortest route, imports, and unit — pass.** Searched the library for Koszul restriction,
   unit, augmentation, and isomorphism results. The surrounding principal-unit theorem uses
   this item, so cannot supply a shorter proof. Both proof-only imports are used; the public
   shifted-augmentation import is needed by the signature. The old Koszul-definition node
   remains used through the cone and restriction constructions, so none is pruned. Inspected
   `sk-thm-picard-duality.realized`: neither its statement nor its step lists this node, and
   no realized unit route is bypassed.
5. **Node agreement — pass.** The three proof steps match the Lean: identify and sheafify the
   cone, identify the powered open union and apply restriction-zero, then use the restricted
   distinguished triangle. The dependency union equals `proof_deps`, and all four named
   nodes exist with matching Lean declarations/modules. No new node needs review.

Second reading changed only this report, adding the review evidence and clarifying that the
compiled proof and its two direct supporting theorems have only the three allowed axioms.
No Lean or DAG repair was necessary. One original hole is closed and zero holes are added.
