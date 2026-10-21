# Q143: lemma-nagata-sheaf-ideal-powers-assoc

## Files written

- dag/nodes/sec-nagata-compactification/lemma-nagata-sheaf-ideal-powers-assoc.json — statement, now split into five steps. No exact Mathlib match for the global sheaf assertion.
- citations.json — verbatim statement excerpts for all 14 step/node citations.
- report.md — this report.

No new DAG nodes, no new Mathlib leaves, no Lean files, and no unit or chapter changes. The sandbox initially contained only searches.jsonl; I retained all prior log entries and read their named hits, then added the second phrasing and source searches through msearch.py. All searches recorded in the item come directly from that log. The present imported item and its blueprint_update have the same statement, which is unchanged.

## Attachments

None claimed. The instruction says not to repeat the rejected attachment. The current read clone does now contain AlgebraicGeometry.Scheme.IdealSheafData.powMulMap_assoc, powMulMap_powZeroUnit_left and powMulMap_powZeroUnit_right in lean/WeilConjectures/AlgebraicGeometry/RelativeProj/Rees.lean at lines 240, 250 and 258. I read their statements and proofs. These are affine module maps, compared after inclusion into the section ring; the global sheaf equality remains to be justified. They confirm the ring calculation, and are not used as an unsupported assertion of a finished global proof. No new node is needed for their few-line pure-tensor arguments.

## WANTED

None. The needed blueprint and Stacks TeX sources are present.

## What needed correction

The import had no dependencies, an unjudged single paragraph, and no Mathlib searches. Its concluding sentence hid the affine tensor comparison and the argument that equality on affine opens implies equality of sheaf maps. I supplied the existing nodes and wrote the actual comparison and uniqueness arguments. I also made all three equations explicit, including the associator, both unitors and the natural-number degree identifications. No statement dispute, missing hypothesis or source error was found.

Mathlib search hits include IdealSheafData products and powers (Basic.lean:410–424), Submodule.nat_power_gradedMonoid (Algebra/DirectSum/Internal.lean:302), TensorProduct.assoc (Associator.lean:147), TensorProduct.ext_threefold (Basic.lean:227), and Submodule.mulMap/mulMap' (Submodule.lean:64,129). I read those source lines. They supply powers, ring-level multiplication, generators and regrouping, but do not themselves state associativity and both unit laws for the global sheaf multiplication maps. The tensor-power multiplication hits concern tensor powers, not ideal powers. Completion therefore needs the split, not a Mathlib-leaf label. The original search hits about local cohomology diagrams, completed tensor maps, quotient ideals and the presheaf tensor object likewise do not state the requested sheaf identities.

## Unfinished work

No stage-1 argument is omitted. Existing cited nodes retain their own proof obligations; I do not claim those nodes are newly proved by this delivery. Stage 2 and Lean compilation are outside the authorized scope.

## Blueprint and route

I read the chapter record sec-nagata-compactification and the unit sk-lem-nagata-sketch-blowups. The argument supplies the multiplication identities for the unit's Rees construction. The main-20261015 blueprint file states the identical item; the preserved blueprint_update.proof[0] gives the affine-ring/localization/sheaf-equality route, expanded here as steps 1, 2–3, 4, 5. I searched the whole imported blueprint with blueprint_refs.py for ideal power, ideal-power, tensor product, associativity and associative, as well as the DAG and upstream source. No other blueprint node states this entire claim. def-nagata-sheaf-rees-algebra depends on this item, and is deliberately not cited back, preventing that circularity.

The only statement tool use outside the unit is lem-weil-pbc-quasi-coherent-tensor-product-affine-sections: its canonical affine tensor isomorphism is needed for the specified affine route. It is declared with its reason in split_report.tool_uses for maintainer review. All other cited nodes are definitions or Mathlib leaves.

## Not duplicates

No new nodes were created. Powers are reused from def-sbc-ideal-sheaf-powers, affine tensor sections from lem-weil-pbc-quasi-coherent-tensor-product-affine-sections, generation and the universal property from def-weil-pbc-module-tensor-product, and the affine basis from lem-weil-pbc-affine-opens-basis. Ring associativity, the balancing equalities, restriction compatibility and sheaf uniqueness are short arguments in the item's proof, rather than redundant nodes.

## Review by Q143

I read the imported proof together with its current blueprint_update and the main-20261015 statement. For its affine comparison I read Stacks schemes.tex, Tag 01I8, lemma-widetilde-constructions, item (1), and Section 01LA, item (8). For generation and the universal property I read algebra.tex, Tag 00CX, lemma-tensor-product, including the quotient construction. For the sheaf tensor and its canonical associativity I read modules.tex, Tag 01CA, section-tensor-product, including the associativity display. I also read sites-modules.tex, Tag 03CY, lemma-sheafification-presheaf-modules, to check the tensor construction's factorization convention, and schemes.tex, Tag 01IT, lemma-basis-affine-opens, with the warning immediately below it that intersections of affine opens need not be affine. There are no new nodes needing additional sources.

For step 1 I opened def-sbc-ideal-sheaf-powers: it explicitly supplies quasi-coherent powers and their affine sections, including degree zero. I opened lem-weil-pbc-quasi-coherent-tensor-product-affine-sections: its statement says that the canonical pure-tensor section map is bijective, and that the tensor remains quasi-coherent. Thus it applies twice to the triple tensor, with no finiteness, flatness or separation assumption. def-weil-pbc-module-tensor-product explicitly states the bilinear universal property used to identify multiplication on sections. These are the precise statements quoted in citations.json.

For step 2 I checked that its target is the same ideal after natural-number associativity, and that the associator orientation matches the displayed equation. The same tensor statements identify generators and say that they generate; applying that fact twice handles arbitrary triple tensors. Equality of products follows in the ring and hence in its subideal. This is an actual calculation, not a new node restating the associativity clause.

For step 3 I checked the cited degree-zero assertion and both module tensor calculations separately. The inverse maps are specified, and the balancing relation verifies both composites. The right unit uses commutativity to identify multiplication with the scalar-action convention. The same affine comparison identifies the sheaf unitors on every generator. No assertion that multiplication is injective occurs.

For step 4 I opened def-pur-sheaf-tensor-product and checked its statement specifies sectionwise tensor restriction followed by sheafification; I opened def-weil-sheaf-of-modules-category and checked restriction is semilinear. Together with the powers and module tensor definitions this gives exactly the restriction formulas written in the step. The fraction computation verifies the blueprint's localization assertion explicitly. It does not identify sections on a general open with a tensor of sections.

For step 5 I opened lem-weil-pbc-affine-opens-basis: its statement supplies affine opens contained in an arbitrary open W, so neither quasi-separatedness nor an affine-intersection assumption is smuggled in. The sheaf category definition makes the target a sheaf and the maps natural. Applying the uniqueness part of the sheaf axiom to the explicitly displayed restricted sections proves equality on W; it is a two-line use of the definition, not a hidden descent theorem.

I tested the statements and steps when X is empty, the coefficient ring is zero, the ideal is zero or the unit ideal, some or all exponents are zero, and for a nilpotent nonflat ideal such as (2) in Z/4Z. In particular I^0 is the whole ring even for I=0; positive powers can vanish and the same generator calculations still apply. No reducedness, Noetherianity, finite generation, injectivity of tensor multiplication, or flatness of an ideal is used. I checked delivery-errors B–E: all notions have existing definition dependencies, all non-elementary inputs are cited by statement, no new node is a duplicate or an item's clause, and no cyclic Rees-algebra dependency is introduced. Every step is below 1000 characters, so no long step hides a lemma. Search provenance is retained exactly, including queries from the earlier attempt.
