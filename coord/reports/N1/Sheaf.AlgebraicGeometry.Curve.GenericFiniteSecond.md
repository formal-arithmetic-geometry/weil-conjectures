## What changed
Added `GenericFiniteSecondReduction.lean` with the finite trace/filtration intermediate theorem and an elementary injective-map subsingleton lemma. The target module now imports it and combines the intermediate result with the elementary lemma.

## Proved and sorry left
The target theorem `subsingleton_sheafH_two_lowerStar_of_finite_stalk` is proved from the intermediate reduction. The new theorem `finite_stalk_second_cohomology_retraction` remains `sorry`, with node `lem-sc-affine-generic-finite-second-retraction`.

## No longer needed
None; the target follows through the stated reduction and all original proof imports remain available for that reduction.

## Where the brief, the DAG or earlier work was wrong
The full trace and filtration argument is too large to close in this worker session, so it is split as a strictly intermediate retraction statement.

## New nodes
`lem-sc-affine-generic-finite-second-retraction` records the finite primary, trace, normalization and filtration reduction used by the new module.

## Earlier second reading (a previous round; superseded)
The target proof is unchanged and uses the intermediate retraction exactly. The new intermediate statement is strictly weaker than the target: it supplies an injective map into a subsingleton type, and the target derives subsingletonness by an elementary argument.

## Second reading by N1

1. Compared the delivered target module byte for byte with the repository version. The target
   declaration signature is unchanged; the only change is its proof and the proof-only import of
   the reduction module. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`; they compile without errors. The only remaining
   `sorry` is the named `finite_stalk_second_cohomology_retraction`, and no forbidden declarations
   occur. Verdict: pass, with that split theorem explicitly recorded in its node.
3. The split theorem is a true intermediate consequence: it records the trace/filtration
   construction as an injection into a subsingleton model, while the target applies the elementary
   injective-map argument. Its hypotheses and conclusion match its node. Verdict: pass.
4. The proof follows the finite trace, normalization, and filtration route from the blueprint; the
   unit route is retained. No shorter proved route was found. Verdict: pass.
5. The node's Lean declaration, proof dependency list, proof origin, and split status agree with the
   delivered declarations. Verdict: pass.

Changed the two proof-only imports in `GenericFiniteSecondReduction.lean` from public imports to
plain imports. No proof dependencies were pruned.
