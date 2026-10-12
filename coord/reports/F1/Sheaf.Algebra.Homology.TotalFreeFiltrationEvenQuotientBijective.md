## What changed

Closed `CochainComplex.TotalFreeFiltration.evenQuotientComponent_surjective` by lifting through the cokernel projection and decomposing the odd filtration term with `odd_le_even_sup`. The injectivity theorem and all existing signatures and definitions remain unchanged. Removed the unused proof-only import `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`. Updated the surjectivity node to describe this proof and the bijectivity node to name the two existing component theorems actually used.

## Proved and sorry left

Holes closed: `CochainComplex.TotalFreeFiltration.evenQuotientComponent_surjective` (node `lem-pc-derived-total-filtration-even-quotient-surjective`). One of the two original holes is closed; zero holes added and zero new statements split off. This is a proof, not a decomposition.

Sorry left: `CochainComplex.TotalFreeFiltration.evenQuotientComponent_injective` (node `lem-pc-derived-total-filtration-even-quotient-injective`). The existing `CochainComplex.TotalFreeFiltration.evenQuotientComponent_bijective` has no textual sorry but still depends on this open theorem.

The surjectivity theorem's axiom print lists only `propext`, `Classical.choice`, `Quot.sound`. The injectivity and bijectivity axiom prints additionally list `sorryAx` from the unchanged named injectivity hole.

## No longer needed

Removed the unused direct proof import `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`; no project module is pruned from the targets' import closure. Every old proof dependency of the surjectivity node remains used. The bijectivity node's old direct dependencies `lem-pc-derived-total-filtration-stable` and `lem-pc-derived-total-filtration-even-quotient-map` are replaced by the two component theorem nodes; both old dependencies remain transitively needed and their definitions stay imported.

## Where the brief, the DAG or earlier work was wrong

The first worker left an unused-variable warning for `h_exact`, which blocks a clean delivery. Surjectivity itself does not require short exactness, but its existing signature is preserved. The original bijectivity node described the entire geometric argument instead of its actual pairing of the two component theorems. The surjectivity node's generic proof description did not record the now completed cokernel calculation. Both proof records are corrected.

## New nodes

None. No change records or interface changes.

## Second reading by F1

1. Compared the complete delivered module with the repository version by `diff`. Every existing declaration signature, binder, namespace, universe, visibility, docstring and definition is byte for byte unchanged. Only the surjectivity proof and one proof-only import change. No other Lean module is delivered. Verdict: pass.

2. Compiled the file locally through `lcompile.py` and checked a scratch copy with `#print axioms` for all three public theorems. The completed surjectivity proof uses only the three permitted axioms; the unchanged injectivity hole accounts for `sorryAx` in injectivity and bijectivity. The only textual sorry is the existing named injectivity theorem. No forbidden declarations, hollow definitions or witness choices were added. The lift is eliminated inside a proposition and constructs no public data from an unproved existence theorem. Verdict: pass after warning repair.

3. No new statements were split off. Read the two pre-existing half-statements, their source/proof docstrings and their nodes. For injectivity, projection to column -j annihilates all earlier full and lower columns and retracts the new full-column inclusion; short exactness makes the lower-column arrow injective. Hence its range intersects the even term trivially. Surjectivity follows from the displayed odd-term decomposition. At j=0 the even term is bottom; the same arguments apply. Zero modules and the zero ring cause no exception. Fresh msearch queries with different wording found no direct replacement: Loogle `Function.Surjective, CategoryTheory.Limits.cokernel.π` returned no hits; LeanFinder for inclusion of one summand followed by quotient by the others found `DirectSum.of_injective` and related inclusion facts, not this quotient statement. Local `rg` of both library roots found only the existing component statements and their users. The cited [Stacks Tag 09KP](https://stacks.math.columbia.edu/tag/09KP) constructs the alternating filtration; the elementary summand calculation is faithful to it. Verdict: pass; injectivity remains an explicitly reported existing hole.

4. Read top downward from bijectivity to its two halves, then the map and filtration-term definitions. The surjectivity proof is the direct cokernel/supremum argument and has no unnecessary reduction or new lemmas. The public map import is needed by the signatures; the unused proof-only ModuleCat import was removed and compilation verified this. No old surjectivity proof dependency is pruned. Read `dag/units/sk-thm-picard-f-representable.json`: its realized statement and step lists are empty, this item is not a unit realization, and its route is unchanged. Verdict: pass.

5. Opened all three existing node records. The injectivity node remains unchanged. Updated surjectivity's `proof` and `proof_origin` to match the lift/decompose/kill-even calculation, retaining its two dependencies. Updated bijectivity's `proof`, `proof_deps`, and `proof_origin` to the exact pairing of injectivity and surjectivity. All statement/source/unit fields stay unchanged; no new nodes are present. Verdict: pass after metadata repair.

Changes in this reading: explicitly reference `h_exact j` in an anonymous proof binding to satisfy the unused-variable linter without altering the public signature; remove the unused proof import; correct the two proof records; expand this report with hole accounting and the independent review. The working surjectivity argument was otherwise preserved.
