## What changed

Added `Sheaf.ConstructibleSheaf.MonoidalParts` with two strictly intermediate lemmas splitting the local constancy and finite-stalk components of tensor preservation. The main module now proves `IsFiniteLocallyConstantSheaf.tensorObj` by assembling these components.

## Proved and sorry left

Proved `IsFiniteLocallyConstantSheaf.tensorObj` by a complete constructor proof from the two component statements. Existing proofs remain as before. New intermediate sorries are `IsLocallyConstantSheaf.tensorObj_part` (node `lem-weil-pbc-flc-tensor-locally-constant-part`) and `IsFiniteSheaf.tensorObj_part` (node `lem-weil-pbc-flc-tensor-finite-part`). Existing sorries remain `IsConstructibleSheaf.isFiniteSheaf` and `IsFiniteLocallyConstantSheaf.ihom_unit`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

No discrepancy found.

## New nodes

`lem-weil-pbc-flc-tensor-locally-constant-part` and `lem-weil-pbc-flc-tensor-finite-part` record the two component results used by the assembled proof.

## Earlier second reading (a previous round; superseded)

The assembled constructor has the exact original target signature and uses each new node only for a distinct component; the unit route remains unchanged.

## Second reading by H2

1. Compared the delivered `Monoidal.lean` with the repository version. Existing declaration signatures and definitions are unchanged; the only existing proof change is `IsFiniteLocallyConstantSheaf.tensorObj`, and the added import is proof-only. Verdict: pass.

2. Compiled both delivered modules with `lcompile.py --all`. They compile without errors, and the only remaining `sorry`s are the two named split lemmas plus the two pre-existing open theorems listed above. No forbidden declarations or hollow definitions were introduced. Verdict: pass.

3. Checked the two split statements against the component obligations of the original constructor and searched the library for duplicate declarations. Each is a strictly smaller preservation claim, with a source, docstring, and matching DAG node; neither weakens the target. Verdict: pass.

4. The proof uses the component lemmas to build the original finite-locally-constant structure and retains the constructibility unit route. Imports needed for tensor notation and the sheaf monoidal instance remain public; no removable proof import was found. Verdict: pass.

5. The new node records match the declarations, proof dependencies, and proof origin. The unit record is unaffected because this item does not realize a recorded unit step. Verdict: pass.

Changed only this report and restored the necessary public imports in `MonoidalParts.lean`; no Lean proof or statement changes were needed during second reading.
