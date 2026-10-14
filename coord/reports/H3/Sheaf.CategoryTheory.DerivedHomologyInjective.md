## What changed

The target theorem now combines two named component theorems, one for injectivity and one for surjectivity. The two component modules are imported privately by the target module. Each component theorem is a strict logical part of the target and remains a documented `sorry` for a follow-up worker.

## Proved and sorry left

`CategoryTheory.derived_homology_injective_bijective` is proved by constructing its `Function.Injective` and `Function.Surjective` fields from the component declarations. The delivery leaves `CategoryTheory.derived_homology_injective_injective` and `CategoryTheory.derived_homology_injective_surjective` as named sorries, with nodes `new-stage3-derived-homology-injective-injective` and `new-stage3-derived-homology-injective-surjective`.

## No longer needed

None. The original Mathlib imports remain needed for the public signatures; the component modules use the same imports.

## Where the brief, the DAG or earlier work was wrong

The original node had a long proof plan but no available Lean declaration implementing either the chain-level comparison or the localization transport. The bijectivity claim was therefore split into its two strict logical halves so that each missing argument is independently actionable.

## New nodes

`new-stage3-derived-homology-injective-injective` and `new-stage3-derived-homology-injective-surjective` are new component theorem nodes, each with its own module and documented proof obligation.

## Earlier second reading (a previous round; superseded)

Pending the independent second reading of the two decomposed component obligations.

## Second reading by H3

1. **Visible changes:** Compared every delivered Lean module with the repository
   version. The target declaration's type is unchanged byte for byte; only its proof
   and two private imports were added. The two component declarations are new split
   obligations recorded by their corresponding DAG nodes.
2. **Compilation and axioms:** Compiled all three modules with `lcompile.py --all`.
   The target has no proof `sorry`; the two component declarations retain exactly the
   documented `sorry`s. Axiom inspection reports only the permitted axioms together
   with `sorryAx` arising from those open component obligations. No forbidden
   declarations or hollow definitions occur.
3. **Statements and nodes:** The injective and surjective statements are strict logical
   halves of the unchanged bijectivity target, with the same hypotheses and codomain.
   Their docstrings give the intended chain-level arguments, and the DAG node records
   match the Lean declarations and proofs. No duplicate library theorem was found in
   the imported sources.
4. **Pruning and route:** The target proof uses both component declarations, so both
   private imports are needed. The unit route is preserved: the bijectivity step is
   realized by the two stated comparison halves. No old proof dependency can be
   removed.
5. **Verdict:** The delivered target proof is valid and unchanged in statement; the
   remaining component holes are true, strictly simpler obligations suitable for
   follow-up work.

**Changes made during second reading:** none to Lean code or DAG nodes; this report
section records the audit.
