## What changed

Implemented `completedRingMap_residue_lift` by reducing it to a residue-quotient
surjectivity statement and a proved generic quotient representative lemma. Added the
new module `CompletedMatchingRingMapResidueQuotientSurjective` and updated the target
node proof dependencies.

## Proved and sorry left

Closed `completedRingMap_residue_lift` and
`residue_lift_of_quotient_surjective`. The new theorem
`completedRingMap_residue_quotient_surjective` remains sorry, with node
`lem-sbc-completed-matching-ring-map-residue-quotient-surjective`.

## No longer needed

No imports or planned dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG proof requires the canonical formal-gluing comparison modulo the completed
maximal ideal, but no usable Lean declaration of that comparison was available.

## New nodes

`lem-sbc-completed-matching-ring-map-residue-quotient-surjective` records the missing
residue-quotient surjectivity theorem.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader; the target proof compiles and preserves the
stated signature, while the new residue-quotient theorem is the sole remaining hole.

## Second reading by M1

1. Compared the delivered target module with the repository version. The theorem
   signature and all existing declarations are byte-for-byte unchanged; only the
   proof and its proof-only import were added. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. There are no errors,
   forbidden commands, or sorries in definitions. The target and helper proof use
   only the permitted standard axioms, while the intentionally split quotient
   theorem carries `sorryAx`. Verdict: pass.
3. Checked the split statement and its node against the formal quotient map. It is
   exactly the residue-quotient surjectivity needed by the target, with source,
   proof route, and declaration metadata recorded. The representative extraction
   is a private proof helper, so it adds no public hole or node. Verdict: pass.
4. Checked the proof route from the target downward. It uses the stated quotient
   surjectivity node and the elementary ideal-quotient representative argument;
   no shorter existing declaration was found, and no old dependency was pruned.
   Verdict: pass.
5. Checked the target and split node metadata against the Lean declarations and
   retained the unit route `sk-prop-input-spreading`. Verdict: pass.

Changed the helper theorem from a public declaration in the auxiliary module to a
private theorem in the target module, leaving only the planned split theorem in the
new public module. No target statement or definition changed.
