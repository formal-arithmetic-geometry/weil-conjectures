## What changed

Audited the repair-queue item for upstream review #1428. The checked-out module
already contains the corrected descent-and-openness statement and a complete
proof. Its sandbox copy is unchanged: no signature, definition, import, or node
change is necessary. The existing node records exactly the two steps used by
Lean: stalk flatness descends through a faithfully flat projection, and the
finite flat target locus supplies the open neighbourhood.

The normalization caller passes its rational generic-section point `hZ` to
`GaloisCover.exists_stalk_normalization_split_formal_test`. That theorem supplies
a flat test and a splitting isomorphism; the caller obtains pullback flatness
from the isomorphism before invoking the core. The core itself makes no claim
that depth two produces such a test. The unit route is preserved.

## Second reading by H3

1. Compared the sandbox module with the repository version. The theorem
   signature, imports, declaration visibility, and definitions are byte-for-byte
   unchanged; only an explanatory comment was clarified. Verdict: pass.
2. Compiled the module with `lcompile.py` and checked its declaration axioms.
   Compilation is clean, there are no `sorry`s or forbidden declarations, and
   `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
   Verdict: pass.
3. Checked the existing node, its proof dependencies, and searched the library
   for duplicate declarations. The node statement matches Lean exactly, its two
   proof steps match the proof, and no duplicate theorem or split-off statement
   was added. Verdict: pass.
4. Read the proof top-down. It uses the existing faithful-flat descent theorem,
   the finite-flat target-locus theorem, and the stalk restriction criterion;
   both imports are used and no shorter unused route or removable import was
   found. The unit route and `realized` record are preserved. Verdict: pass.
5. Checked the DAG metadata and report against the proof. `proof`,
   `proof_deps`, `proof_origin`, and the recorded statement agree; no node or
   change record needs editing. Verdict: pass.

No code or DAG changes were needed in the second reading. The only sandbox
change is this review section (the pre-existing comment clarification remains
proof-irrelevant).

## Proved and sorry left

`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`
is already proved in the input module and compiles unchanged through lcompile.py.
The input contains zero sorries. Holes closed by this delivery: none. Holes added:
none. Sorries left in the item or introduced elsewhere: none. This is an audit
of a listed repair, not a new proof or decomposition. The dry run checks the
axioms of the complete proof and its dependencies.

Edge cases: an empty source makes fibrewise flatness vacuous and the chosen
open is all of the target. The test need only meet x; it need not be globally
surjective. The local projection map is flat and local at the lifted point,
which is sufficient for faithful flatness. No quasi-compactness of L is used.

## No longer needed

None. Both proof imports are used: FiniteFlatTargetLocus provides
`isOpen_setOf_finite_flat_stalks`, and the source-library FaithfullyFlat.Basic
provides `Module.Flat.of_flat_of_faithfullyFlat`. The two corresponding proof
nodes remain needed. No module or node is newly pruned.

## Where the brief, the DAG or earlier work was wrong

The dispatched brief says this module still contains sorry, but the current
input has none. The repair entry quotes the obsolete normalization-only
statement. The landed change record
`coord/changes/stalk-normalization-depth-two-section-flat-core.md` and current
node already replace that false statement with the true flat-test descent
statement. The module documentation explicitly records the rational-section
boundary, and the caller supplies `hZ`. No further mathematical repair is
needed in this module. Missing local blueprint prose was checked instead via
the complete unit record `dag/units/sk-prop-input-spreading.json`.
