## What changed

Proved `AlgebraicGeometry.Scheme.tensorPullback_unit_open_localization` without changing its signature or visibility. Added only proof imports: Mathlib module pullback, preservation of limits on slice categories, and additive adjunctions. Constructed the restricted ring map and right-adjoint comparison, then used uniqueness of left adjoints. A proved private categorical helper constructs H from restriction and its right adjoint and proves the unit equation by naturality and the triangle identity. Updated the existing node's proof to this route. The static checker requested a command-only change record at `coord/changes/tensor-unit-open-localization-proof-commands.md`; it records the identical old/new theorem signatures and the downstream modules, with no adaptations.

The right-adjoint comparison is a scheme specialization of the existing private proof in `Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackPresentation`; that module is not imported. The argument applies to empty U, identity p, and arbitrary modules. No choice from an unproved existence theorem is introduced: the original canonical adjunction is already proved, and every new construction is explicit or determined by a proved universal property.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.tensorPullback_unit_open_localization` (lem-sc-tensor-unit-open-localization). No sorry remains in this module. Added 0 holes, split off 0 statements. This is a proof, not a decomposition. The local single-file compile passes without warnings; the delivery dry run checks the axioms.

## No longer needed

None: both original public imports remain required by the unchanged statement. Both original proof-dependency nodes remain used. No new Sheaf proof dependencies are imported. The cofinal-neighbourhood and sheafification-restriction calculations proposed in the original proof are replaced by proved Mathlib adjunction uniqueness and the explicit right-adjoint comparison; no separate nodes or modules for those calculations are needed. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement found. The original plan suggests a localized tensor composite and sectionwise comparison of its unit. The unchanged existential statement also permits H = S ⋙ P ⋙ Q ⋙ R, where S is the right adjoint of open restriction. This construction avoids comparing canonical unit section formulas: naturality works for the exact adjunction chosen in the original statement. The open restriction counit is proved invertible, and both pullback and pushforward restriction comparisons are proved before using this alternative H. The source tags were read online because the literature files are not present in this clone. The unit record sk-prop-av-cube has empty realized arrays and remains unchanged.

## Second reading by K2

1. Compared the delivered module with the repository version. The theorem signature and visibility are byte-for-byte unchanged; only proof code, proof-only imports, and scoped commands differ. The DAG node records the comparison-of-adjunctions route used by the proof.
2. Compiled the module with `lcompile.py`; it is clean with no warnings. The file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `debug.skipKernelTC`. Axioms for the target and private helper are exactly `propext`, `Classical.choice`, and `Quot.sound`.
3. Checked the construction on empty opens and identity maps conceptually from the definitions: the slice adjunction and all comparison isomorphisms remain valid, and no arbitrary witness is selected. The target statement is unchanged and no statement was split off.
4. Checked the shortest available route against the imported Mathlib adjunction and additive-functor declarations. The proof uses the existing tensor-pullback adjunction, explicit restricted ring map, and uniqueness of left adjoints; no unnecessary Sheaf module or node was added. All imports are used by the proof, and the unit `sk-prop-av-cube` and its realized fields are unchanged.
5. Checked the DAG proof steps and dependencies against the Lean proof. The two existing proof dependencies remain exactly the dependencies used, and the node's proof origin and route describe the implemented comparison and localization argument.

Changed only the proof implementation and proof-only imports/commands; no mathematical interface, target statement, definition, or downstream adaptation was changed.
