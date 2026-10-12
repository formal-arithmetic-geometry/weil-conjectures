## What changed
Replaced the parent theorem's proof by a complete proof from Mathlib. Polynomial formal smoothness kills H₁, so Jacobi–Zariski exactness makes mapBaseChange injective. The explicit sum of variable differentials splits the first fundamental sequence. Base change, product, transport and reindexing of bases prove the rank clause. All existing declaration signatures and visibility are unchanged; the original public imports are retained. The added imports are proof-only.

## Proved and sorry left
Closed the one original hole: KaehlerDifferential.exists_polynomial_extension_equiv (node lem-weil-pbc-kahler-differentials-polynomial-extension). No holes added; no sorry remains. Both clauses are fully proved, with only propext, Classical.choice and Quot.sound. Removed the proposed deferred declarations kahler_polynomial_extension_decomposition and kahler_polynomial_extension_basis and their proposed nodes/modules; neither had landed. Net holes closed: 1, holes added: 0.

## No longer needed
The old proof dependencies lem-weil-pbc-polynomial-scalar-extension and lem-weil-pbc-kahler-differentials-base-change are no longer used: polynomial H₁ vanishing and Jacobi–Zariski give injectivity directly. They were not imported by the original module; this delivery removes them from this node's proof_deps, without claiming they become globally unreachable.
Removed the proposed proof imports Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtensionDecomp and Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtensionBasis, both proposed modules, and both proposed nodes (lem-weil-pbc-kahler-differentials-polynomial-extension-decomposition and lem-weil-pbc-kahler-differentials-polynomial-extension-basis). All four other old proof dependencies remain used. No existing public import was removed.

## Where the brief, the DAG or earlier work was wrong
The first draft only paired two deferred conjuncts; its report called this a proof. Both new docstrings lacked natural-language proofs, and both DAG statements copied the full parent rather than matching their Lean statements. The original parent DAG was not updated to the draft's proof. These defects are resolved by closing the full theorem and removing the unnecessary split. The original six-step route can be shortened below the unit level by polynomial H₁ vanishing and Mathlib's Jacobi–Zariski sequence.

## Second reading by V2
1. Compared the delivered module against the repository version with diff and a byte comparison of the declaration signature: unchanged. No definition, hypothesis, conclusion, universe, or visibility was altered. No change record is needed.
2. Compiled the whole initial draft and the repaired final module using lcompile.py. The final module has no sorry, axiom, unsafe, opaque, implemented_by or extern declaration and no hollow definition. A scratch #print axioms check and deliver3's declaration probe verify the standard axioms only.
3. Reviewed both proposed component statements: they are true conjuncts, including for zero variables and zero rings, but their documentation and nodes were deficient. Searched independently with leanfinder, loogle and grep through msearch.py, and searched lean/ and Mathlib sources. Mathlib already supplies the exactness, polynomial H₁ vanishing, polynomial basis and basis operations needed; no split statements remain.
4. The proof explicitly constructs the map in the statement and proves its bijectivity, then transports bases. It uses Mathlib directly from the top downward and removes both proposed modules. Every unused old proof_deps node is listed above. The item is not a statement or step in dag/units/sk-thm-p1.json realized; its below-unit route may shorten, and the unit route and realized record remain intact.
5. Updated the existing node's proof, proof_deps and proof_origin to match the complete Lean proof, keeping every other field intact. The two proposed duplicate component nodes are removed. No new nodes or statements are delivered.

Changed on second reading: fully proved both conjuncts, eliminated both deferred components, repaired the parent DAG and report, and documented the shorter injection argument.
