## What changed

Added two proof-only decomposition modules and imported them into the target module. The target theorem is proved by composing the raw lift and completion compatibility theorems.

## Proved and sorry left

`torsionControlled_completion_hom_lift_exists` is proved by a real composition argument. The decomposition theorems `torsionControlled_completion_hom_lift_raw` and `torsionControlled_completion_hom_lift_completion` remain `sorry`, each with its own node and source.

## No longer needed

No imports were removed. The planned gluing declarations remain the conceptual source of the two decomposition statements.

## Where the brief, the DAG or earlier work was wrong

The DAG presents the entire affine localization, descent, and sheaf gluing argument as one step, but no directly usable declarations for those steps were available under the target's imports. The work therefore splits that step into the two strictly smaller interfaces above.

## New nodes

`lem-weil-pbc-torsion-controlled-completion-hom-lift-raw` and `lem-weil-pbc-torsion-controlled-completion-hom-lift-completion` are new nodes corresponding to the two named intermediate theorems.

## Earlier second reading (a previous round; superseded)

The target proof composes two strictly smaller interfaces. The new statements retain the
unit route's affine gluing argument and are exactly the needed parts of the target.

## Second reading by R1

1. **Repository comparison.** Compared the delivered target module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only two proof-only imports and the target proof body were added. The two new decomposition modules and node files are new delivery contents.

2. **Compilation and axioms.** Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds. The target's remaining `sorryAx` comes only through the two explicitly named split-off theorems. There are no `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definitions.

3. **Split statements.** Checked both new statements against the target: `torsionControlled_completion_hom_lift_raw` supplies exactly the underlying lift, while `torsionControlled_completion_hom_lift_completion` supplies exactly the completion equality for such a lift. Their docstrings give the affine gluing source and proof outline, and both have matching DAG nodes. Searches via `msearch.py` found no existing library or Mathlib declaration. Neither statement merely restates the target.

4. **Pruning and route.** The target proof uses both split declarations directly, and its imports are plain proof imports. The public `CoherentFormalModule` import remains required by the target signature. No removable import or old proof dependency was found. The unit route and unit `realized` record are unchanged; these nodes remain below the unit's existing affine-gluing route.

5. **DAG agreement.** The Lean declarations, node statements, proof dependencies, source, and split status agree. The raw node has no proof dependencies; the completion node records the raw interface it conceptually relies on. No statement or definition was changed.

I changed only the target composition proof and its two plain imports; no split-off hole could be closed safely within this reading.
