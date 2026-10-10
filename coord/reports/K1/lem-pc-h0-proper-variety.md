Files written:

- `dag/nodes/sec-picard-framework/lem-pc-h0-proper-variety.json`: split statement; no new node files.

Attachments:

- None. The slopmaster2 source checkout available to this worker has no declaration for this item.

WANTED:

- `literature/stacks-project/varieties.tex`, Tags 04L2 and 0BUG, for `lem-pc-h0-proper-variety` (not materialized in this checkout). I read the official Stacks pages for both tags online; Tag 04L2 states exactly clauses (1) and (4), and Tag 0BUG gives the finiteness and flat-base-change ingredients. The proof here expands these through existing DAG nodes and is marked agent-written.

What was checked and corrected:

- The statement now introduces all notions it uses: proper morphism conventions, variety, and geometric integrality. The second clause explicitly asserts equality as `k`-algebras.
- Part (1) was checked against the existing nodes `lem-pc-euler-characteristic-well-defined`, `def-pc-curve`, `lem-sc-integral-scheme-stalks-in-function-field`, and the Mathlib leaf `lem-weil-pbc-finite-dimensional-domain-is-field`. These give finite-dimensionality, integrality, injectivity into the generic stalk/function field, and the field conclusion respectively. The Euler-characteristic node carries the finite-dimensionality statement in this unit and itself proves it from the coherence theorem.
- Part (2) was checked against `lem-sc-flat-base-change-coherent`, `def-pc-geometrically-irreducible`, `lem-pc-proper-base-change`, `def-pc-curve`, `lem-pc-finite-extension-alg-closed`, and `lem-pc-finrank-field-base-change`. Geometric integrality supplies integrality after algebraic closure, proper base change supplies the other variety hypothesis, and the scalar-extension leaf makes the final one-dimensional argument explicit.
- The imported proof's phrase “comparing dimensions ... style” was replaced by the exact finite-rank equality. The imported “e.g. connected and integral” wording was removed because the cited variety definition already states the required hypotheses. No statement was weakened.

## Review by K1

I read the item node, its unit and chapter records, the standing stage-1 brief, and the delivery-error checklist. I checked the item against Stacks Tags 04L2 and 0BUG: 04L2 gives precisely the two requested claims and 0BUG gives the proper-cohomology and base-change route behind them. I searched the DAG for duplicate global-sections, generic-point, finite-dimensional-domain, algebraically-closed-extension, and scalar-extension statements before editing; all auxiliary facts used by the split already exist as nodes. I checked each proof step against the statement of every cited node, verified that every non-elementary fact appears in `uses`, and verified that `proof_deps` is their union. The LeanSearch service returned HTTP 500; LeanFinder and Mathlib source grep found `finite_appTop_of_universallyClosed` and `isField_of_universallyClosed` in `Morphisms/Proper.lean:150-170`, which directly cover part (1), but no declaration for part (2). JSON syntax was validated locally.
