## What changed

The sandbox retains the existing complete proof of
`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`,
with its last stalk-transport step shortened from `rw [hw] at hp; exact hp`
to `rwa [hw] at hp`. No statement, definition, visibility or import changed.
This is an audit of the listed upstream-review repair, not a new proof closure.

## Proved and sorry left

`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`
is proved and has no `sorry`. It was already proved in the repository version:
0 holes closed, 0 holes added, 0 split off. Its axiom check shows exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None. Both existing proof dependencies remain used:
`lem-weil-pbc-flat-algebra-faithfully-flat-descent` and
`lem-sbc-finite-flat-target-locus`. No module is pruned.

## Where the brief, the DAG or earlier work was wrong

The repair queue still describes the old false normalization-only statement.
The landed change record `coord/changes/stalk-normalization-depth-two-section-flat-core.md`
already replaced it by the true finite-morphism descent-and-openness statement.
The current theorem assumes pullback flatness explicitly; it does not claim
that depth two alone supplies it. The first report incorrectly presented the
already existing proof as new progress; the hole counts above correct this.

## Second reading by V2

1. PASS: Compared the entire delivered module with the repository by `diff`.
   The sole Lean change is the final `rwa` simplification. The existing signature
   is byte-for-byte identical, as are definitions, visibility and imports.
2. PASS: Compiled the delivered file locally with `lcompile.py`, with no errors
   or warnings. No `sorry`, forbidden declaration, or data construction from
   an unproved existence theorem occurs. A scratch copy with `#print axioms`
   reports only `propext`, `Classical.choice`, and `Quot.sound`.
3. PASS: No new statement or split-off hole exists. Checked the mathematical
   argument: each source point above x lifts using b, the projection's local
   flat stalk map is faithfully flat, and flatness descends from its composite.
   Empty fibres cause no issue: the universal stalk condition is vacuous there.
4. PASS: The proof already uses the source-library faithfully flat descent
   lemma and the finite flat target locus theorem. Read both dependencies and
   searched Mathlib's flat-morphism and faithfully-flat APIs; no shorter direct
   theorem replaces this assembly. Public imports supply the statement's
   Noetherian, finite and flat notions; the two proof imports are plain imports.
   Both old proof dependencies remain used, so the pruning list is complete.
   Read `dag/units/sk-prop-input-spreading.json`: its route and `realized` record
   are unchanged. This descent step retains the formal-test input boundary.
5. PASS: The existing node
   `lem-sbc-stalk-normalization-depth-two-section-flat-core` records exactly
   the stalk descent and target-locus steps, their two proof dependencies,
   and the repaired explicit flat-pullback hypothesis. Its Lean signature
   matches the file. No node update is needed for the tactic simplification.

Second reading changed only this report: clarified the already repaired queue
entry, recorded zero net hole progress, and documented the independent checks.
