## What changed

Repair #1428: retire ModuleCat.projective_resolution_ext_degree and all imports of
Sheaf.RingTheory.ProjectiveResolutionExtDegree. Its module now exports nothing.
Retain the required, already proved bounded-resolution/dimension comparison as
ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE in
Sheaf.RingTheory.BoundedProjectiveResolutionDimension. The forward direction explicitly
uses Mathlib hasProjectiveDimensionLT_iff; the reverse constructs a bounded resolution.
Update only the proof import and bridge calls of the three direct callers, with their
signatures and visibility unchanged. Reattach the existing DAG node to this bridge.

Change record: coord/changes/retire-projective-resolution-ext-degree.md.

## Proved and sorry left

There were zero sorries in the assigned module. Zero holes closed, zero added, zero split
off; this is a duplicate-interface repair, not a new proof or decomposition.
ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE is fully proved and
retains the original constructive bridge. No sorry remains in any delivered Lean file.
All five modules compile locally without warnings; the delivery dry run checks axioms.

## No longer needed

Sheaf.RingTheory.ProjectiveResolutionExtDegree is removed from each of the three direct
callers' proof imports and only imports Mathlib.Init for command and linter support, so it is pruned from the target closure.
ModuleCat.projective_resolution_ext_degree is retired without an alias.
Its old module's public imports Sheaf.RingTheory.GlobalDimension and
Mathlib.CategoryTheory.Abelian.Projective.Dimension, and proof imports
Mathlib.CategoryTheory.Abelian.Projective.Ext and
Sheaf.RingTheory.ProjectiveResolutionSuccSplice, are removed there; all four remain
necessary in the actual bounded-resolution bridge module. No mathematical dependency
node is pruned: the existing bridge node retains its statement and constructive proof
route. In particular lem-weil-pbc-projective-resolution-succ-splice remains necessary.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt treated zero sorries as a reason to stop, but this is a repair item.
The historical review's Ext-criterion duplicate was already replaced by a genuine
bounded-resolution/dimension bridge in earlier landed work. The pinned Mathlib
hasProjectiveDimensionLT_iff states Ext vanishing, not existence of a bounded resolution;
its signature was read directly. Renaming and moving the bridge makes this distinction
explicit and retires the obsolete duplicate interface and all its callers. This changes
no mathematical statement and keeps the unit route. Neither the projectivity-at-zero
nor localization cluster members are direct dependencies of the retired interface;
no discretionary edits to their modules are included.

## Forced adaptations

All three adapted modules are unclaimed. Only their proof import and uses of the retired
bridge name change: Sheaf.RingTheory.ProjectiveResolutionExtAllDegrees lines 5, 30, 33;
Sheaf.RingTheory.ProjectiveResolutionExtCharacterization lines 11, 72, 75; and
Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise lines 13, 96. Against the empty retired module,
the originals fail at each bridge call with Unknown identifier; the adapted files compile
against the replacement bridge. Exact original compiler diagnostics are appended by the
delivery dry run. All existing signatures and visibility remain byte-for-byte unchanged.

## Second reading by B4

1. **Visible changes and signatures.** I diffed every delivered Lean file against the
repository version. The three adapted callers retain their declarations, statements,
visibility, and proof interfaces byte-for-byte; only their proof-only import and calls
to the retired bridge changed. The old item module intentionally has no declarations,
as recorded in the change record, and the replacement bridge has the same equivalence
statement under its descriptive name.

2. **Compilation and proof status.** I compiled all five sandbox modules with
`lcompile.py --all`; they compile without errors or warnings. There are no `sorry`,
`axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations in delivered
files. The bridge proof uses Mathlib's Ext dimension criterion in the forward direction
and the existing constructive successor splice in the reverse direction; no hollow
definition or arbitrary witness is introduced.

3. **Statements and split nodes.** The bridge node's statement is unchanged from the
repaired interface and is exactly the theorem proved in
`BoundedProjectiveResolutionDimension.lean`. No new split-off theorem or node is added,
and the retired name is not used as an alias. The three caller statements remain
unchanged, so no target is weakened or strengthened.

4. **Imports and pruning.** The replacement bridge keeps the imports needed by its
constructive proof. The retired module has only `Mathlib.Init`, while each adapted
caller imports the bridge privately. The old Ext-degree module and declaration are
therefore pruned from the target closure; the successor-splicing node remains a proof
dependency. The node's proof and proof-dependency metadata follow the bridge proof.

5. **Unit route and forced adaptations.** The unit route is preserved: the reverse
direction still goes through the kernel short exact sequence and
`hasProjectiveResolutionLE_of_shortExact_projective_middle`. The changed lines in the
three unclaimed caller modules are forced by the retired identifier (the originals fail
with `Unknown identifier`, while the adapted files compile), and no discretionary
changes were made. The delivery's CODEX review therefore consists of checking those
minimal adaptations and the bridge relocation.

I changed only the retirement/relocation interface, the three forced proof imports and
bridge calls, the corresponding node metadata, and this report.

## Forced adaptations

### Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise
Original against changed dependencies failed:
```
/tmp/forced-adaptation-9nbbfgkq/lean/Sheaf/AlgebraicGeometry/AffinePolynomialResolutionOfStalkwise.lean:96:21: error(lean.unknownIdentifier): Unknown constant `ModuleCat.projective_resolution_ext_degree`
/tmp/forced-adaptation-9nbbfgkq/lean/Sheaf/AlgebraicGeometry/AffinePolynomialResolutionOfStalkwise.lean:96:9: error: Tactic `rcases` failed: `x✝ : ?m.253` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-9nbbfgkq/.lbuild) [1.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.RingTheory.ProjectiveResolutionExtAllDegrees
Original against changed dependencies failed:
```
/tmp/forced-adaptation-9fhq3to_/lean/Sheaf/RingTheory/ProjectiveResolutionExtAllDegrees.lean:30:12: error(lean.unknownIdentifier): Unknown identifier `projective_resolution_ext_degree`
/tmp/forced-adaptation-9fhq3to_/lean/Sheaf/RingTheory/ProjectiveResolutionExtAllDegrees.lean:33:11: error(lean.unknownIdentifier): Unknown identifier `projective_resolution_ext_degree`
/tmp/forced-adaptation-9fhq3to_/lean/Sheaf/RingTheory/ProjectiveResolutionExtAllDegrees.lean:34:4: error: No goals to be solved

(with the modules compiled into /tmp/forced-adaptation-9fhq3to_/.lbuild) [1.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.RingTheory.ProjectiveResolutionExtCharacterization
Original against changed dependencies failed:
```
/tmp/forced-adaptation-2cob0x2z/lean/Sheaf/RingTheory/ProjectiveResolutionExtCharacterization.lean:72:12: error(lean.unknownIdentifier): Unknown identifier `projective_resolution_ext_degree`
/tmp/forced-adaptation-2cob0x2z/lean/Sheaf/RingTheory/ProjectiveResolutionExtCharacterization.lean:75:11: error(lean.unknownIdentifier): Unknown identifier `projective_resolution_ext_degree`

(with the modules compiled into /tmp/forced-adaptation-2cob0x2z/.lbuild) [1.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
