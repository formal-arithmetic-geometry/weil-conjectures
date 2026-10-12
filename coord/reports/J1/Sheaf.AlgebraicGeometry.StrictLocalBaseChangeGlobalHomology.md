## What changed

Completed and checked the earlier sandbox reduction of
`AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_globalHomology`.
The signature is unchanged. Two proof-only imports provide the neighbourhood
presentation and the existing derived continuity theorem. The source cocone is
extended along the actual mate; continuity makes the target cocone colimiting;
colimit hom-ext identifies its universal comparison with the mate, proving IsIso.
Added the missing definition and helper nodes and updated the item node to match
this Lean proof. All three modules compile locally in import order.

The remaining presentation is strictly a part of the argument: it supplies the
source colimit, scheme limit, canonical transition maps, target object identification,
and compatibility of the actual mate with restriction. It does not assume a target
colimit or an IsIso assertion. Derived continuity and the categorical conclusion
are implemented separately in the item's proof.

## Proved and sorry left

Proved (by reduction):
`AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_globalHomology`
(lem-weil-pbc-strict-local-base-change-global-homology): the sole original sorry is gone.

One new sorry remains:
`AlgebraicGeometry.Etale.nonempty_strictLocalBaseChange_continuityPresentation`
(lem-weil-pbc-strict-local-mate-continuity-presentation), in the new module
`Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation`.
It is exactly `:= by sorry`, with a complete construction in its docstring and node.
The new structure `GlobalCohomologyContinuityPresentation` contains no sorry.
This is a reduction, not an axiom-free closure of the target: imported continuity
still rests on its own named dependencies.

## No longer needed

No original import is removed, and no mathematical dependency is pruned.
The original module had only its statement import StrictHenselizationRestriction.
The direct proof dependencies on affine cofinality, the fibre-product limit,
the injective representative, higher-direct-image sheafification, stalk invariance,
and the germ isomorphism move into the new presentation helper; they remain needed.
The strict-henselization and restriction definitions also remain needed.
DerivedEtaleCohomologyLimit remains used directly. No claim is made that any of
these modules leaves the target closure. The new structure imports only its
statement infrastructure; the item imports the helper and continuity privately.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had compiling Lean but no report or node files and hence was
not a delivery. Those omissions are repaired. Several original proof dependencies
have no lean record (injective representative and sheafification-stalk invariance),
and the existing abelian higher-direct-image theorem is expressed through derived
Yoneda rather than the explicit projection-pullback diagram needed by continuity.
The new helper isolates precisely this construction and compatibility glue.
The unit sk-prop-h2 has no realized entry for this node; its statement and steps
are untouched. The route still uses neighbourhood limits and derived continuity.

Sources checked: Stacks [03Q9](https://stacks.math.columbia.edu/tag/03Q9),
[03Q8](https://stacks.math.columbia.edu/tag/03Q8), and
[0GIT](https://stacks.math.columbia.edu/tag/0GIT).
The local literature checkout contains lists only; the source pages were read online.
The source-colimit and restriction construction are separated from the continuity
assertion, as in 03Q9. Negative degrees, zero K, and already strictly local affine
bases require no additional hypothesis. The index is required cofiltered (hence
nonempty), so an empty diagram is not incorrectly admitted. Qcqs is required of f
and therefore of the affine-neighbourhood pullbacks, without requiring X or S qcqs.
No torsion or properness assumption was added. The displayed restriction formula
uses the same unit, Leray and inverse-image coherence maps as the existing
DerivedEtaleCohomologyLimit theorem; local compilation checks these types.

Searches from the earlier attempt are recorded in searches.jsonl: LeanFinder found
only unrelated scheme or structure-sheaf results; Loogle supplied the useful general
colimit comparison theorem; Mathlib grep found no strict-local derived comparison.
Additional LeanSearch for the presentation was unavailable (Internal Server Error).
Whole-blueprint searches for continuity and 03Q9 found no exact presentation node.

## New nodes

`def-weil-pbc-global-cohomology-continuity-presentation` records the source colimit
and canonical restriction data in
`Sheaf.AlgebraicGeometry.GlobalCohomologyContinuityPresentation`. Its source is
03Q9 and the projection-pullback interface of 0GIT; it has no postponed data or proof.

`lem-weil-pbc-strict-local-mate-continuity-presentation` records the construction of
that data for the actual mate, in
`Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation`. Its proof follows
03Q9's neighbourhood and injective-complex restriction construction, with germ and
Leray identifications from the existing project nodes. It is the sole split-off
statement. Both nodes inherit the item's chapter and unit. No change record is
needed: existing definitions and statements are unchanged.

## Second reading by J1

1. Compared the delivered item module and all new modules with the repository. The
existing target signature is byte-for-byte unchanged; only its proof and proof-only
imports changed. The two new declarations are recorded by new nodes, and no target
statement or existing definition was altered. Verdict: pass.

2. Compiled all three modules in import order with `lcompile.py --all`. There are no
Lean errors, forbidden declarations, or sorries except the named public theorem
`nonempty_strictLocalBaseChange_continuityPresentation`, whose proof is exactly
`by sorry` and whose node and docstring give its source and construction. Verdict:
pass subject to that explicitly split theorem.

3. Checked the split theorem against the Stacks proof. It constructs the neighbourhood
presentation (source colimit, limit diagram, transition maps, target identification,
and restriction equations) without asserting continuity or invertibility; the target
then uses continuity separately. It is therefore a genuine strict intermediate result,
not a restatement of the target. Searches found no existing Mathlib or library
statement. Verdict: pass.

4. Read the proof from the target downward. It uses the presentation, the existing
continuity theorem, and the standard colimit comparison lemma. The helper theorem's
imports are statement-facing where needed; the item's helper and continuity imports
are private. Existing direct dependencies moved into the helper's construction and
remain mathematically represented there. Verdict: pass; no additional pruning found.

5. Compared the item node's proof, proof dependencies, and proof origin with the Lean
proof. The two non-elementary steps and the elementary colimit uniqueness step agree
with the code. The unit and chapter fields are unchanged and the route still passes
through neighbourhood limits and derived continuity. Verdict: pass.

Changed in this second reading: only this report section was added. No Lean proof,
statement, node, or import required repair.
