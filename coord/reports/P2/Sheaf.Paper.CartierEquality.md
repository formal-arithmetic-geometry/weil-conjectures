## What changed

Copied the already-proved `Sheaf.Paper.CartierEquality` module into the sandbox and verified it compiles. No source changes were needed.

## Proved and sorry left

`cartier_equality` is proved. No `sorry` remains in the module, and no new declarations were added.

## No longer needed

No imports or DAG nodes were removed; the existing proof uses its declared dependencies.

## Where the brief, the DAG or earlier work was wrong

The repository already contains the completed proof (landed previously), so this stage-3 invocation had no remaining hole to close.

## New nodes

None.

## Second reading by P2

1. **Visible changes:** Compared the delivered module with the repository version. The theorem
   statement and all existing declaration signatures are byte for byte unchanged; the only
   source difference is removal of an explanatory comment. No accidental definition or
   hypothesis change is present. Verdict: pass.
2. **Proof validity:** Compiled `Sheaf.Paper.CartierEquality` with `lcompile.py`; it compiles
   without errors or warnings and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`,
   or hollow definition. The proof uses the complete-intersection and cotangent-model
   declarations and the resulting rank-nullity calculation. Verdict: pass.
3. **Statements and nodes:** No statements were split off and no new nodes were added. The
   existing Cartier equality node's statement is exactly the theorem proved, and its recorded
   dependencies describe the complete-intersection model, cotangent comparison, rank-nullity,
   and transcendence-basis steps used by the proof. Verdict: pass.
4. **Pruning and imports:** All imports are used by declarations or the proof, and no import or
   proof dependency can be removed without changing elaboration. The route remains below the
   unit level while retaining the unit's complete-intersection and cotangent-model steps.
   Verdict: pass.
5. **Unit route:** The unit record's realized statement and proof steps remain respected; this
   delivery changes no route, definition, or target. Verdict: pass.

Changed during second reading: appended this review record and removed one stale explanatory
comment from the copied proof module. No mathematical or interface change was needed.
