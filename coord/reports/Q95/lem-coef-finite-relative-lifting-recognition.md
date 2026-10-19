Files written:

- `dag/nodes/sec-six-functors/lem-coef-finite-relative-lifting-recognition.json` — statement split, no new nodes, no Mathlib leaves.
- `citations.json` — verbatim quotes for every cited node use.

Attachments: none.

WANTED: HTT.pdf, Proposition 3.1.3.5 and Proposition 3.1.3.7(1), because the source is online and not archived in `literature/`.

The item was unsplit and has no finished Lean declaration in the inspected source. Its statement is unchanged. I searched the whole DAG and blueprint for duplicates and found the existing point case `lem-coef-finite-marked-fibrancy-criterion`; it is strictly the constant-base specialization, while this item handles arbitrary bases and relative cartesian lifts, so it is cited rather than duplicated. The existing relative marked-anodyne calculus supplies the arbitrary-base definitions and pullback marking behavior, and the marked-anodyne calculus supplies the finite generators and detector.

## Review by Q95

I read the item, the chapter and unit records, the ancestor blueprint proposition, and the source statements of every cited node. Step 1 restricts each square to a constant vertex fiber and uses exactly the point finite criterion; the relative calculus statement verifies that the induced marking is the natural pullback marking. Step 2 checks the three finite generator families against the arbitrary-base horn definition: inner horns give the inner fibration, final horns give prescribed-target cartesian lifts, and the marked triangle generator enforces composition and inverse compatibility. Step 3 uses the finite detector together with the point criterion to identify the remaining cartesian edges with the marked edges. Step 4 verifies the converse diagonals directly from the cartesian-fibration and natural-marking clauses. Step 5 treats the constant-base detector as a fiber square and invokes the point criterion, with the relative pullback statement ensuring the diagonal lies over the required constant map. I checked the hypotheses (small base, no quasicategory assumption, finite generator set, and constant vertex labels) at each use. I reran the four mandated Mathlib searches for this item (LeanFinder, Loogle, grep, and LeanSearch); they returned only generic unmarked horn or ordinary category-theory declarations, so there is no exact Mathlib match. No statement, source, dependency, or route correction was needed.

What I could not finish: nothing; the stage-1 split is complete and no Lean or compiler work was attempted.

## Second reading by Q95

- Item statement: checked against HTT Proposition 3.1.3.7, proof part (1), pp. 158–160 (the displayed finite generators (1)–(3), the constant detectors A_s, and the arbitrary simplicial base); all hypotheses are retained, including no quasicategory assumption on S or X. Verdict: agrees.
- Node `lem-coef-finite-marked-fibrancy-criterion`: read its full statement and compared the constant-fiber restriction with the finite point criterion; the zero fiber and empty marked set cases are covered. Verdict: cited statement supplies exactly the fiber conclusion.
- Node `lem-coef-marked-anodyne-lifting-calculus`: read its full generator, A-quotient, and marked mapping statements; the item uses only the listed finite generators and detector. Verdict: cited statement supplies the generator and detector data.
- Node `lem-coef-relative-marked-anodyne-calculus`: read its full arbitrary-base horn, cartesian-fibration, pullback, and natural-marking clauses; the item applies these with S arbitrary and with constant maps at vertices. Verdict: cited statement supplies the relative conventions and hypotheses.
- Step 1: checked type (i) against inner-horn lifting and type (ii) at n=1 and n≥2 against the prescribed-target and final-horn clauses. Verdict: repaired to state the lifts and the resulting cartesian fibration explicitly.
- Step 2: checked the comparison of an arbitrary cartesian edge with a marked lift, the fiber equivalence, and the type-(iii) marking square against the detector proof on p. 159. Verdict: repaired; the former vague “transport” sentence now names the 2-simplex, its fiber edge, and the marked generator.
- Step 3: checked the A_s square against the quotient/corepresenting description of A and the point-fiber criterion. Verdict: repaired to spell out the constant-fiber extension and its marked distinguished edge.
- Step 4: checked each converse generator separately against the three clauses in the cartesian-fibration definition and the composition property of cartesian edges. Verdict: repaired; no inverse-triangle claim is used for type (iii).
- Step 5: checked the final detector restriction and the constant base map at s against the last paragraph of the source proof. Verdict: repaired to state why the diagonal is over S.
- Mathlib searches: reran the recorded LeanFinder, Loogle, grep, and LeanSearch queries; they find only unmarked horn or ordinary-category declarations, so no Mathlib leaf is available.

Changes made: corrected the node's `created.item` to this delivered item (the worker record named a different item), rewrote all five proof steps to follow the source proof with explicit generator-by-generator arguments, and retained the existing three-node citation set and searches. No new node or statement change was needed. Edge cases checked: S empty, S a point, empty X, the zero-dimensional detector, and n=1 final horns.
