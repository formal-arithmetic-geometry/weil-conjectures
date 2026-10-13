## What changed

The core proof now uses the existing proved source-library theorem
`Module.Flat.of_flat_of_faithfullyFlat` instead of repeating its tensor-injectivity
argument. Added its module as a plain proof-only import and removed the restoration
comment. All existing
signatures, visibility, definitions, docstrings and public imports are unchanged.
The core node's proof and dependencies now name the existing algebra descent node.
The two caller modules and the historical landed change record are unchanged.

## Proved and sorry left

`AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core` is proved
with only `propext`, `Classical.choice`, and `Quot.sound`. It was already proved
at the delivery base. Holes closed: none. Holes added: none. No split-off theorem
or new definition is introduced. No textual `sorry` remains in the three modules.
This is a listed repair and proof simplification, not net proof-hole progress.

## No longer needed

No old proof dependency or module is pruned. The dependency
`lem-sbc-finite-flat-target-locus` remains required. The inline tensor calculation
is replaced by `lem-weil-pbc-flat-algebra-faithfully-flat-descent`; no old import
is removed, and the new proof-only import is plain `import`.

## Where the brief, the DAG or earlier work was wrong

The repair entry citing upstream review #1428 describes the older normalization
statement, not the current finite-morphism flat-test statement. The current
statement needs no extra hypothesis: the point `b` and `hb` suffice to lift every
source point over `x`. The historical change record is already landed and is
not a new interface change in this delivery. The first reader missed the exact
proved source-library descent lemma, which avoids duplicating its proof.

## New nodes

None.

## Forced adaptations

None. Both caller modules are byte-for-byte unchanged.

## Second reading by Q4

1. Compared every sandbox Lean module, node and change record with the repository
   using `diff`. Only the core proof and its proof-only import,
   and owned DAG proof fields change. Existing declaration signatures remain
   byte-for-byte identical. No target statement or definition changes. Verdict: pass.
2. Compiled all three modules in import order with `lcompile.py`; no errors or
   warnings. Read the proof from point lifting through local faithful flatness,
   algebra descent and open target flat locus. There are no textual sorries,
   forbidden declarations or hollow definitions. A scratch `#print axioms` check
   of the core lists only the three permitted axioms; delivery also runs the
   declaration probes. Verdict: pass.
3. No statements are split off. Independent `msearch.py` grep and Loogle searches
   and `rg` in the project found the exact existing algebra descent lemma and its
   existing node. The theorem includes empty source fibres vacuously; existence
   of `b` ensures the target point is met by the flat test. No global surjectivity
   is assumed or needed. Verdict: pass.
4. Used the shortest already proved upstream route for algebra descent and kept
   the required finite flat target locus dependency. The new import serves only
   the proof and is private to this module. Checked `sk-prop-input-spreading`:
   its `realized` fields are unchanged (already empty at the base); this local
   proof simplification retains the depth-two/formal-test assembly route in the
   unchanged caller. No former dependency is omitted from the pruning report.
   Verdict: pass.
5. The node statement and Lean signature agree. Updated `proof`, `proof_deps` and
   `proof_origin` to describe the existing upstream descent result followed by
   the same finite flat target locus argument. No new nodes or statement changes.
   Verdict: pass.

Second reading changed the inline descent calculation to an application of the
existing proved theorem, removed the restoration comment, and corrected the report and DAG proof dependency records.

The first dry run treated removal of the namespace opening as an interface
change. Restored that opening; no such interface change is delivered.
