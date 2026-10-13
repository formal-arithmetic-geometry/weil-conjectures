## What changed

Proved `AlgebraicGeometry.Scheme.picardTensorFrame_restriction` without changing its
signature or definitions. Its two intermediate modules are imported only for the proof.
The normalization theorem is now proved: a private unit-composition calculation applies
the mate unit equation and composite adjunction homEquiv, identifies the structure maps
sectionwise, and then cancels the source and target frames by naturality. Evaluating the
remaining pulled-back unit endomorphism at one applies the residue lift's appTop map.
The evaluation theorem factors the residue lift through the stalk lift and uses ΓSpecIso
naturality. Removed two unused private helpers from the item's module. Removed redundant
public imports from the two new modules; every retained public import supplies signature
objects or definitions.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Scheme.picardTensorFrame_restriction` (1 of 1).
New proved intermediate declarations:
`AlgebraicGeometry.Scheme.picardTensorFrame_restriction_normalized`
(node `lem-sc-picard-tensor-frame-restriction-normalized`) and
`AlgebraicGeometry.Scheme.picardResidueLift_appTop_eval`
(node `lem-sc-picard-tensor-frame-restriction-evaluation`).
The second reader closed the first worker's new normalization hole. No holes added or
left in any delivered module: this is one original hole closed, not a decomposition.
Axiom checks and compilation are recorded in the second reading below.

## No longer needed

No original module import was pruned: PicardTensorFrameCoordinates,
PicardOrdinaryModelCycles, and PicardDerivedModelSections all supply signature objects.
All six original proof dependencies are replaced as direct dependencies of the item by
the two intermediate nodes. None is eliminated from the transitive argument:
`def-sc-picard-derived-model-sections`, `def-sc-picard-ordinary-model-cycles`,
`def-weil-residue-field`, `lem-pc-module-pullback-adjunction`,
`lem-sc-picard-tensor-frame-map`, and
`lem-weil-pbc-module-pullback-structure-sheaf` remain needed through those intermediate
proofs and definitions. No module is claimed to leave the target import closure.
Removed redundant PicardTensorFrameCoordinates, PicardOrdinaryModelCycles, and Mathlib
ResidueField imports from the new evaluation module, and the redundant Mathlib
ResidueField import from the new normalization module.

## Where the brief, the DAG or earlier work was wrong

The first worker left normalization open and included unused duplicate private helpers.
The normalization calculation can be proved directly from the existing adjunctions;
no additional unproved statement is needed. Corrected the evaluation node's copied
statement dependencies and supplied its missing theorem docstring. The new source note
identifies the actual Mathlib stalk and evaluation identities; Stacks 0BF2 is the
surrounding application rather than an explicit statement of the residue ring formula.
An existing related theorem in PicardUnitComposition uses the unit isomorphism from
PicardCupProductMap, which has the same fully qualified name but a different definition
from PicardTensorFrameCoordinates. Importing it here would collide; the local proof
therefore works directly with the adjunction-pinned unit used by this item. No existing
definition was changed to resolve that separate library issue.

## New nodes

`lem-sc-picard-tensor-frame-restriction-normalized`: the appTop compatibility step before
ΓSpecIso and residue evaluation. Fully proved by unit compatibility, frame naturality,
and evaluation at one. Its Lean statement and proof dependency list match the code.

`lem-sc-picard-tensor-frame-restriction-evaluation`: the independent computation of the
ring map of a residue lift. Fully proved from stalk lifts, ΓSpecIso, and the definition
of evaluation. No change records are needed because existing signatures and definitions
are unchanged.

## Second reading by S4

1. PASS. Compared the sole existing delivered module with the repository by diff and
   compared its theorem signature byte for byte. Only its proof and proof-only imports
   change. No existing definition, statement, visibility, or docstring changes; both
   other modules are new.
2. PASS. Compiled the three modules in import order through lcompile.py. No errors or
   warnings, no sorry in the delivery, and no axiom, unsafe, opaque, implemented_by,
   extern, or hollow definition. Scratch #print axioms checks and deliver3's full probe
   show exactly propext, Classical.choice, and Quot.sound for the target and both
   intermediates. No sorryAx is reachable from these declarations; deliver3 also
   checks every declaration with its full probe.
3. PASS. Both new statements are true and are now proved, so no split-off hole remains.
   Checked identity/inclusion V=U, zero morphism and zero section, arbitrary changes of
   frame, and the vacuous empty-scheme case (there is no point w). No extra cycle,
   affineness, differential, or perfectness hypothesis is used. Independently searched
   with leanfinder, loogle, and grep (searches.jsonl), and read the relevant Mathlib and
   project declarations. Found ingredients and the incompatible related unit-composition
   theorem, not an importable duplicate of these residue-coordinate formulas.
4. PASS. The proof follows the existing plan's three calculations: composite units,
   normalized coordinate, residue evaluation. It no longer defers the whole coordinate
   calculation to a new hole. Removed unused helpers and redundant new imports. All
   original proof dependencies are accounted for above. Read sk-prop-av-cube.json;
   this node is below the unit level and its realized fields and chapter/unit route
   are unchanged. No original dependency module becomes unreachable in this delivery.
5. PASS. Read every delivered node alongside its Lean module. The item's proof and
   proof_deps name the two proved intermediates. Their proof descriptions match the
   mate/naturality and stalk-evaluation arguments; the normalization node includes the
   residue-lift definition dependency used by picardResidueLift_comp. New nodes have
   complete source, creation, search, blueprint, chapter/unit, and verbatim Lean records.

Second reading changed: proved the normalization hole; removed unused private helpers;
pruned redundant imports in the new modules; added the evaluation docstring; corrected
source/dependency metadata and the hole accounting. Existing signatures remain unchanged.
