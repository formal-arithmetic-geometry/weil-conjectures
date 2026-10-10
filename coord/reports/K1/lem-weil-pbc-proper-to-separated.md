# Delivery report

1. Files written:

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-proper-to-separated.json`: statement node, converted to a Mathlib leaf; verdict `AlgebraicGeometry.IsProper.of_comp` exact match.

2. Attachments:

- `AlgebraicGeometry.IsProper.of_comp` belongs to existing node `lemma-nagata-proper-to-separated-target` as well as this item.

3. WANTED:

- None.

4. Problems found:

- The imported graph proof was unnecessary once the pinned Mathlib declaration was checked. The existing imported node `lemma-nagata-proper-to-separated-target` also states the same commutative-triangle result in the Nagata chapter; this is recorded in `blueprint.same_as` rather than duplicated as a new node.

5. Unfinished:

- Nothing.

## Review by K1

I checked the item against the imported statement and the source documentation in `WeilConjectures/Compactification/EliminationOfIndeterminacy.lean`, which explicitly identifies the blueprint result `lemma:nagata-proper-to-separated-target` with Mathlib's `AlgebraicGeometry.IsProper.of_comp`. I read the declaration and surrounding definitions in `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`, lines 35-45 and 111-129. Its hypotheses are `[IsProper (f ≫ g)]` and `[IsSeparated g]`, and its conclusion is `IsProper f`. Substituting the item's morphism `g : X -> W` for Mathlib's first leg and the structure morphism `W -> Y` for its second leg gives the item's composite `X -> Y` as the proper hypothesis and the separated target morphism as the separated hypothesis, so the statement agrees exactly.

There are no proof steps after conversion to a Mathlib leaf. The imported graph-factorization paragraph is therefore not retained as a DAG proof: the Mathlib declaration supplies the complete result. I searched the whole DAG for the proper/separated triangle and found `lemma-nagata-proper-to-separated-target`, whose statement is the same result with names `T, Y, B`; I searched the blueprint with `tools/blueprint_refs.py search` for both `proper separated target` and `nagata-proper-to-separated-target`, and recorded that node in `blueprint.same_as`. I also searched the Lean source and `dag/lean_names_upstream.json`: the upstream mapping assigns `AlgebraicGeometry.IsProper.of_comp` to that existing Nagata node, and no slopmaster2 declaration carries this curve-estimates item tag.

For the Mathlib search requirement, I recorded LeanSearch and LeanFinder concept searches, a source grep, and local declaration lookup. The source grep located `IsProper.of_comp` at lines 124-129, and I read those lines rather than relying on a name-only match. Small edge checks are immediate: taking the second leg to be an identity recovers properness of the first leg, and taking the first leg to be the item's `g` gives precisely the required conclusion. No hypotheses beyond the commutative triangle, proper composite, and separated second leg are used.
