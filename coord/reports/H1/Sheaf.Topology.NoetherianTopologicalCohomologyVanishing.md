## What changed
Repair of reviewer X-d0295: made the dimension-induction assertion explicitly quantify over all sheaves and all degrees above the bound; replaced its circular invocation of the all-dimensions component theorem with a direct component-count induction at fixed d. Updated the corresponding DAG steps without changing the proof-dependency union, corrected the new-node classification relative to sheaf-dag, and revised Second reading point 4. Both Lean signatures and proof bodies are unchanged.

Repaired the two split theorem docstrings with numbered proofs. The irreducible theorem now records the stronger induction over all Noetherian spaces, the empty case, the dimension-zero constant-sheaf argument, all four 02UX hypotheses, and the exact cohomology segment. The component theorem now gives the component-count induction, including zero and one component cases, the construction of Z and Z', Noetherian and dimension inheritance, the open-closed sequence, closed-support and pushforward comparison, and the precise use of hIrred. Updated both node statements, statement dependencies, proof steps, proof dependencies, and blueprint ancestry to the nearest blueprint ancestor lem-sc-pic-proper-ntorsion with same_as [].

## Proved and sorry left
`TopCat.isZero_noetherian_topological_cohomology_of_dimension_bound` is proved by applying the two split declarations. `TopCat.noetherian_vanishing_irreducible` remains `sorry` (node `new-node-noetherian-irreducible`), and `TopCat.noetherian_vanishing_of_irreducible_components` remains `sorry` (node `new-node-noetherian-components`).

## No longer needed
No imports or nodes were removed. The recorded dependencies are exactly the facts cited by the repaired proof steps.

## Where the brief, the DAG or earlier work was wrong
The returned version used induction slogans and omitted the stronger all-Noetherian-spaces induction required when a closed complement is reducible. The split node statements also omitted the quantified dimension bounds, empty-space clause, dependency lists, and nearest blueprint ancestry. These are repaired here.

## Earlier second reading (a previous round; superseded)
1. The target signature is unchanged, and the target proof remains a genuine application of the two strictly smaller split declarations.
2. Both repaired theorem docstrings preserve the unit route through Proposition 02UZ and Lemma 02UX; no target statement or definition was changed.
3. The component hypothesis now quantifies over every irreducible Noetherian Y, every nonnegative e with dim Y <= e, every abelian sheaf G, and every r > e. The conclusion quantifies q > d and explicitly includes empty X. The irreducible node has the matching d, dimension, sheaf, and q quantifiers.
4. The repaired induction handles empty X and d=0, and uses the stronger all-Noetherian assertion so reducible closed complements are covered. The exact segment and the inequalities q-1 > d-1 >= dim Z are recorded.
5. Every recorded dependency is checked against a proof step: finite components, open-closed sequence, closed-immersion pushforward, topological cohomology, constant-sheaf acyclicity, and extension-by-zero reduction. The node proof_deps are the exact unions of step uses, and both blueprint records point to lem-sc-pic-proper-ntorsion with the imported via list and same_as [].

## New nodes
`new-node-noetherian-components` is new relative to sheaf-dag and records reduction from irreducible spaces to arbitrary Noetherian spaces.

`new-node-noetherian-irreducible` is new relative to sheaf-dag and records the irreducible vanishing result, proved by a stronger induction over all Noetherian spaces.

## Earlier second reading (a previous round; superseded)

1. Compared both delivered Lean modules with the repository version. The existing target
   declaration has the same signature byte for byte; the added module contains only the two
   named split declarations and the target proof. No accidental target or definition change was
   found.
2. Compiled both modules with `lcompile.py --all`. There are no errors or forbidden commands;
   the only remaining `sorry`s are the two named split theorems, each with a public docstring
   and matching DAG node. The target is a direct application of those strictly smaller
   declarations.
3. Checked both split statements against their node JSON and the source proposition. Their
   quantified dimension bounds, empty-space clause, sheaf and cohomological degree hypotheses
   agree exactly with the Lean signatures; neither statement duplicates an existing declaration.
4. Reread the corrected induction: its assertion quantifies over every Noetherian space
   of dimension at most d, every abelian sheaf, and every degree q > d. Thus the outer
   induction applies at degree q - 1 to reducible closed complements of dimension at most
   d - 1. At fixed d, first establish the irreducible case, then extend to all Noetherian
   spaces by component-count induction: zero components is empty, one uses that irreducible
   result, and otherwise Z and Zprime = closure(X \ Z) have fewer components. The support
   clause, closed-pushforward comparison, and long exact sequence kill the degree-q terms.
   This repeats the component argument directly without invoking the component theorem's
   unavailable hypothesis over all dimension bounds. The Lean signatures are unchanged,
   and the corrected DAG step uses have the same union as the existing `proof_deps`.
5. Imports are statement imports for the required topology, dimension, sheaf, and cohomology
   types; the proof-only link to the split module is a plain import. No obsolete imports or
   dependencies were found, so pruning is `none`.

This repair changes the irreducible theorem's proof docstring, its DAG proof steps, and
this report. Both Lean signatures and proof bodies are preserved.

## Second reading by H1

1. Compared the delivered target module with the repository version. The target theorem
   signature is byte-for-byte unchanged; the only target change is its proof, which applies
   the two strictly smaller split declarations.
2. Compiled both delivered modules with `lcompile.py --all`. Compilation succeeds. The only
   remaining `sorry`s are the two named split theorems, each public, documented, and matched
   by a DAG node; no forbidden declarations occur. The target proof has no independent axiom
   beyond those split obligations.
3. Compared both split declarations with their node JSON and the source proposition. Their
   dimension, Noetherian, sheaf, and degree quantifiers match exactly; the component theorem
   includes the empty-space case. Searches found no existing declaration duplicating either
   statement, and both statements are true and as strong as the reduction requires.
4. Reread the proof route and DAG steps. The irreducible proof records the all-Noetherian
   dimension induction, dimension-zero constant-sheaf case, and all 02UX hypotheses. The
   component proof uses finite-component induction, closed supports, pushforward comparison,
   and the open-closed sequence. The recorded proof dependencies equal the declarations used;
   no unused imports or nodes were found, so pruning is `none`.
5. The unit route through Proposition 02UZ and Lemma 02UX is preserved. Both new nodes point
   to the nearest blueprint ancestor and have complete source, proof, dependency, and Lean
   records. No target definition or statement changed.

Changed the report only to record this second reading and its passing verdicts.
