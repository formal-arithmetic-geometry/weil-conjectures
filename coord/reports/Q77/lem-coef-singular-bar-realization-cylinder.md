# Worker report

## Files written

- `item.json` (the item node, now `split`; no new nodes and no Mathlib leaves).
- `citations.json` (verbatim statement quotations for every node used by every proof step).

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, walking-span/bar/realization/cylinder terms, and relevant declaration names; no sorry-free project declaration states this item.

## WANTED:

None. The proof is explicitly agent-written from the available blueprint paragraph and the existing DAG interfaces.

## What was wrong or missing

The imported item had a complete statement but no proof or proof dependencies. I supplied the missing chain decomposition and quotient-topology argument, retaining the statement and its hypotheses. No duplicate or new auxiliary node was needed: the existing Bousfield--Kan comparison-calculus node gives the chain, face, degeneracy, and functoriality data, and the existing simplicial-realization-cylinder node gives the product realization homeomorphism. The recorded Mathlib searches return only abstract model-category cylinders or walking-span categorical primitives, so the item remains non-Mathlib.

## Review by Q77

I read the item in `dag/nodes/sec-six-functors/lem-coef-singular-bar-realization-cylinder.json`, the blueprint source `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md` (Paragraph 2), and the complete statements of `def-cbc-enhanced-diagrams-cones`, `lem-coef-bousfield-kan-comparison-calculus`, and `lem-coef-simplicial-realization-cylinder`.

Step 1 classifies every walking-span chain into the constant a, b, or c chains and the two mixed chain families. The Bousfield--Kan statement explicitly supplies the endpoint-face and identity-degeneracy rules used in this classification. The realization-cylinder statement supplies the natural homeomorphism from each mixed family to `|U(c)| × [0,1]`; I checked the endpoint directions against the labels c and a/b.

Step 2 computes the coordinates from the barycentric labels: on c-to-a chains `w = 1-t`, hence `w/2 = (1-t)/2`, while on c-to-b chains the coordinate is `1-w/2 = (1+t)/2`. I checked the all-c midpoint and the endpoint faces, where the Bousfield--Kan rule applies the actual arrows `U(c→a)` and `U(c→b)`. The geometric-realization quotient statement verifies that these compatible formulas descend through every face and degeneracy identification.

Step 3 uses the quotient topology from `def-cbc-enhanced-diagrams-cones` to check continuity on each piece and continuity of the inverse after splitting at the midpoint. The inverse agrees on the endpoint identifications, so the piecewise maps are inverse homeomorphisms of the stated double-cylinder quotient. Step 4 uses the Bousfield--Kan functoriality clause to verify naturality under strict diagram maps; the same quotient argument handles empty values of any of `U(a)`, `U(b)`, or `U(c)`.

I tested the construction on the constant point diagram, diagrams with an empty endpoint, and the case `U(c)=∅`; the formulas reduce to the expected interval/glued-end spaces and no nonemptiness hypothesis is used. Every proof dependency is an existing node in the same unit, every citation quote is a verbatim substring checked against that node's statement, and no compiler, Lake, build, or Lean-writing command was run.
