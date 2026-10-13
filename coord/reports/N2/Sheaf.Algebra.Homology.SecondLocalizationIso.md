## What changed

Added the proof-only auxiliary import and reduced `exists_secondLocalization_iso` to the
existence and invertibility interfaces in `SecondLocalizationIsoAux`.

## Proved and sorry left

`exists_secondLocalization_iso` is proved from the two auxiliary interfaces. The new
interfaces retain `sorry`: `exists_secondLocalization_hom` and
`secondLocalization_hom_isIso`, with nodes `lem-pc-second-localization-iso-aux-hom` and
`lem-pc-second-localization-iso-aux-isIso`.

## No longer needed

No imports or planned dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG proof describes the full derived construction but does not expose the two
strict intermediate interfaces needed to state the reduction in Lean.

## New nodes

`lem-pc-second-localization-iso-aux-hom` and `lem-pc-second-localization-iso-aux-isIso`
are added in `SecondLocalizationIsoAux.lean`.

## Second reading by N2

1. Compared the delivered main module with the repository version. The target
   signature is byte-for-byte unchanged; only its proof and a proof-only import
   changed. The target DAG node now records the two auxiliary proof dependencies.
   Verdict: pass.
2. Compiled both sandbox modules with `lcompile.py --all`. There are no compile
   errors, warnings, axioms, or forbidden declarations; the only remaining
   `sorryAx` occurrences are the two named auxiliary split statements. Verdict:
   pass.
3. Checked the auxiliary statements against `IsSecondLocalizationMap`: existence
   of a morphism and invertibility of a characterized morphism are strictly
   simpler than the target and retain all hypotheses. Their source and proof
   descriptions are recorded in docstrings and matching DAG nodes. Verdict: pass.
4. The proof uses the shortest available reduction through those two interfaces;
   no unused import or old proof dependency was found. The unit route remains
   represented by the target node and its realized unit. Verdict: pass.
5. The target node's `proof`, `proof_deps`, and `proof_origin` now agree with the
   Lean proof, and the new nodes include chapter, unit, Lean declarations, and
   sources. Verdict: pass.

Changed the target proof to obtain the characterized map and install its `IsIso`
instance, added the proof-only auxiliary module and its two split statements, and
updated the corresponding DAG records. The proof-only import change is recorded
in `coord/changes/second-localization-iso-proof-import.md`.
