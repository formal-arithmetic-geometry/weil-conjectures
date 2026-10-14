## What changed

Audited `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlatCore`
as the assigned repair-queue item. The starting module already contains a complete
proof of `AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`.
Removed its unnecessary local `classical` command. The edge-case observations
about non-surjective tests and empty fibres are recorded below; the existing
proof documentation is preserved. The signature, visibility, imports and
proof route are unchanged. No definition or consumer is adapted.

Read the core node, its two dependency nodes and Lean declarations, the unit
`sk-prop-input-spreading`, the landed E4 change record and the previous F2 report.
The argument still lifts each point of the fibre to the pullback, descends
flatness through the faithfully flat projection stalk map using
`Module.Flat.of_flat_of_faithfullyFlat`, and applies
`isOpen_setOf_finite_flat_stalks` and the restriction stalk criterion.
The node already describes this route exactly, so no node update is required.

## Proved and sorry left

`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`
(node `lem-sbc-stalk-normalization-depth-two-section-flat-core`) was already
proved in the starting module and remains proved after the simplification.
Starting holes: zero. Holes closed by this delivery: zero. Holes added: zero.
No `sorry` remains in the assigned module. No new modules or theorems are added.
This delivery is a repair audit, not new proof progress.
The original compiled without warnings in 3.2 seconds; the simplified module
also compiles. The delivery dry run checks all declarations for forbidden
transitive axioms.

## No longer needed

None. Both proof imports are used: `FiniteFlatTargetLocus` supplies openness,
and `WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` supplies
algebra flatness descent. The public Mathlib imports provide the statement's
scheme, Noetherian, finite and flat vocabulary. No node or module is pruned.

Loogle (`RingHom.Flat`), Lean Finder (flatness near a point descending along
a flat test), and local Mathlib/library searches found no shorter matching
descent-and-openness theorem. The available stalk criteria are already used;
the proved source-library algebra descent theorem is the direct match.

## Where the brief, the DAG or earlier work was wrong

The brief says this module still contains `sorry`, but the current module has
none and compiles. The repair queue still names upstream review #1428's
obsolete false normalization-only statement. The landed change record
`coord/changes/stalk-normalization-depth-two-section-flat-core.md` already
replaced it with the true general descent-and-openness statement.
The current theorem explicitly assumes `Flat (pullback.snd p t)`; depth two
alone is not claimed to imply this. The normalization caller explicitly
assumes the rational generic-section point `hZ` and passes it to
`GaloisCover.exists_stalk_normalization_split_formal_test` to establish
pullback flatness. The other caller establishes it through a finite etale
extension. No target or caller signature needs repair.

Checked the edge cases: an empty fibre gives vacuous membership in the target
flat locus; an empty test cannot supply the point b; non-surjectivity away
from x is harmless because only source points above x are lifted. This is
exactly the node's two-step argument and preserves the unit's route.

## Second reading by T4

1. **Interface: pass.** Compared every delivered module (one) against the
   repository with `diff -u`. The existing theorem signature is byte for byte
   unchanged, as are its visibility, imports, universe and namespace. There
   are no definitions, new declarations, node edits or change records in this
   delivery. The only remaining Lean diff removes the proof-local `classical`.
2. **Proof and axioms: pass.** Compiled the delivered file locally through
   `lcompile.py`, without errors or warnings. Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`:
   exactly `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   No sorry or forbidden declaration mechanism occurs in the delivered file.
   Read the pullback-point lift, flat composite stalk map, flat local projection
   and algebra descent, and the final restriction-stalk isomorphism application.
   They establish precisely the unchanged conclusion.
3. **Split statements: pass, none.** No statements are split off or introduced.
   Checked the argument on an empty source/fibre (flat-locus membership is
   vacuous), a non-surjective flat test (only the point b over x is needed), and
   an empty test (cannot satisfy the required b). No arbitrary data is chosen
   from an unproved existence theorem.
4. **Route and pruning: pass.** Searched locally and through `msearch.py grep`
   with faithful-flatness and flat-neighbourhood/openness terms. Mathlib's
   general fpqc descent requires global cover hypotheses absent here. The
   similar `flat_stalk_of_flat_test` in SmoothLocalDepthTwoClosedFiberFlat is
   private, so cannot shorten this proof through a public import. The existing
   proved algebra descent and finite flat target locus are the direct route.
   Both private proof imports are used, and all three public imports supply
   vocabulary in the signature. No old proof dependency is unused; pruning is
   none. Read `sk-prop-input-spreading.json`: its pre-existing `realized` arrays
   are empty, and this delivery neither edits them nor bypasses its depth-two
   completion, descent and openness route. The core performs only the last
   descent and openness part; the unchanged normalization caller supplies the
   flat test with the rational generic-section hypothesis.
5. **DAG: pass.** Read the core node and both dependency nodes and declarations.
   The core's two proof steps, `proof_deps` and `proof_origin` agree with the
   written proof. Its recorded Lean signature agrees verbatim. No new node is
   needed and no existing node field needs changing.

Second-reading change: restored the repository's existing theorem docstring,
keeping the edge-case discussion in this report. Retained the first worker's
removal of the unnecessary local `classical`. Updated What changed to describe
that final diff. This is a repair audit: zero starting holes, zero closed,
zero added, one already-proved declaration checked.
