# Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-opposite-homotopy-calculus.json`: statement node, split into seven proof steps; no new nodes and therefore no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every cited node in every step.

## Attachments

None. No finished declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this item.

## WANTED

- `https://www.math.ias.edu/~lurie/papers/HTT.pdf`, Section 1.2.1, for the general opposite construction and Joyal invariance; the proof is written directly from the definitions and existing DAG statements because this source is not archived under `literature/`.

## What was wrong or incomplete

The imported node was unsplit and had no proof steps. The seeded dependencies are sufficient after checking their statements: the subdivision node supplies weak-equivalence and Kan preservation, the relative-cone node supplies the quasicategory opposite fact, the cocone node supplies the internal-functor reversal, and the Joyal model node supplies the categorical-equivalence and fibration definitions. I did not add a supporting node because each remaining argument is a direct horn, 2-simplex relation, lifting-square, or degreewise-pullback calculation from those statements. The item itself had no statement correction.

## What I could not finish

No Lean implementation or compilation was authorized at this stage. The HTT source remains wanted as an archival citation, but the natural-language split is complete.

## Review by N1

I read the item node and its chapter and unit records, then checked each cited statement in full. Step 1 uses the enhanced-diagram definition of standard simplices and horns for the order-reversal calculation. Step 2 uses the existing subdivision/opposite node for weak homotopy equivalences and Kan complexes, and checks Kan-fibration lifting by the explicit reversed-horn bijection. Step 3 uses the same horn calculation for arbitrary inner fibrations and the relative-cone statement that opposites of quasicategories are quasicategories. Step 4 uses the existing internal-functor reversal statement, including its degreewise parameter reversal and naturality. Step 5 uses the Joyal definition of categorical equivalence and the internal-functor reversal to preserve the generated vertex-edge 2-simplex relations in `h`; no domain or codomain fibrancy is assumed. Step 6 uses the Joyal characterization of fibrations as right lifting against categorical-equivalence cofibrations and verifies that opposite preserves injections and lifting squares. Step 7 uses degreewise pullbacks, quasicategory fibrancy, and Step 6 to handle fibrant cospans with Joyal-fibration legs. I checked every citation quote against its source node and recorded the three Mathlib searches run for the item; none states the full Joyal reversal theorem. No duplicate node, hidden cycle, or unverified hypothesis was introduced.
