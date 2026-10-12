## What changed

Replaced the sole `sorry` in
`Sheaf.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget` with a complete Lean proof
of `AlgebraicGeometry.isAffine_of_surjective_of_universallyClosed`. Its signature, visibility,
docstring, imports, and file-level commands are unchanged.

The proof implements the existing eight-step Stacks 05YU plan. Separatedness descends along
`f` using `isSeparated_of_surjective_universallyClosed` over the terminal scheme. The affine
source then makes `f` affine by `IsAffineHom.of_comp`, and universal closedness makes it
integral. The continuous surjective image of the compact source makes the target compact;
its separatedness supplies quasi-separatedness. The existing finite-presentation approximation
provides finite stages and affine transitions. Mathlib's
`Scheme.exists_isAffine_of_isLimit` selects an affine stage. The identity
`F.π.app i ≫ F.p i = f` gives surjectivity of `F.p i` by `Surjective.of_comp`, and
`isAffine_of_isFinite_surjective` concludes. No definitions or intermediate statements change.

LeanFinder, Loogle, the launcher grep search, and local searches of Mathlib and both library
roots found no theorem directly proving the conclusion. All three existing proof imports
are used. The proof preserves the unit route and the DAG plan, so no node edits are needed.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.isAffine_of_surjective_of_universallyClosed`
(node `lem-weil-pbc-surjective-universally-closed-affine-target`).

No `sorry` remains in the delivered module. No holes or declarations were added.
This is a proof from existing declarations, including the still-open separatedness descent
and finite-surjective affineness theorems; their holes are unchanged, not claimed closed here.
Local single-file compilation passes without warnings.

## No longer needed

None. All original imports and planned mathematical dependencies remain in use.
No modules or nodes are pruned. The finite-presentation clause of the approximation is
available but the conclusion needs only its finite stages, as in the existing plan.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The approximation uses a cofiltered category
rather than an explicitly directed ordered set; Mathlib's affine-stage theorem accepts that
interface directly, so no reindexing or auxiliary statements are necessary.

## Second reading by F2

1. Compared the delivered file with the repository using `diff -u`. PASS: the sole
   difference is the replacement of the theorem's `sorry` by its proof. The existing
   signature, visibility, definitions (none), docstring and imports are byte-for-byte
   unchanged; no change record or forced adaptation is required.
2. Compiled the delivered module through `lcompile.py` successfully without warnings.
   Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.isAffine_of_surjective_of_universallyClosed`: precisely `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. PASS: the last comes from existing
   open dependencies; there is no local `sorry`, forbidden declaration, or data definition.
   In particular, the approximation is eliminated inside a theorem proving a proposition,
   not used to define data from an unproved existence theorem.
3. PASS: no statement is split off and no hole is added. Read both open imported theorems
   and the finite-approximation interface. The finite-stage theorem really has finite
   structure maps, affine transitions and the stated limit cone; the stage-surjectivity
   argument uses the correct composite order. Empty schemes cause no exceptional case:
   surjectivity forces an empty target when the source is empty, and no nonemptiness
   assumption is introduced. Independent searches of both library roots and Mathlib,
   including launcher grep for `affine.*(closed|integral).*surject|surject.*integral.*affine`,
   found no shorter direct theorem.
4. PASS: the proof follows the eight-step route from the target downward, using Mathlib
   for affine-source separatedness, affine cancellation, integrality, compactness and
   the affine limit stage. All three proof imports supply declarations used explicitly;
   the public Integral import supplies the signature's universally closed interface.
   No import or old proof dependency becomes unused. Read `dag/units/sk-thm-p1.json`:
   its realized statement and steps are preserved; this lower-level proof bypasses none.
5. PASS: read the item's node, its eight proof steps, `proof_deps`, and `proof_origin`.
   They agree with the Lean proof, including the qcqs stage conditions discharged by
   instances and the finite-surjective final step. The existing source attribution is
   correct. No node edits are needed.

Changes by the second reader: appended this review only. The Lean proof and DAG were
already correct and are unchanged. One local hole is closed, zero holes are added, and
no module is pruned; the theorem is not claimed free of its existing dependencies' holes.
