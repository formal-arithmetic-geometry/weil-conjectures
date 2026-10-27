# Stage-1 delivery: lem-pur-quotient-system-flat-models

Group NW, 2026-10-22. Direct delivery with the worker's own review.

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-quotient-system-flat-models.json`: existing statement node, now split into seven steps; not a Mathlib leaf. The statement and its statement dependencies are unchanged. Existing searches, provenance and blueprint fields are retained; actual logged searches and the precise split report are added.
- No new DAG nodes; no new Mathlib leaves; no unit or chapter changes.
- `citations.json`: one verbatim statement extract for each of the fifteen step/node citations.
- `searches.jsonl`: five searches recorded by the required msearch command, including two different natural-language formulations. `write_split.py` is the sandbox-only script that writes the item and extracts/validates the citation quotes.

## Attachments

None. I searched the exact item id and blueprint tag throughout `lean/WeilConjectures/`, and searched the concepts quotient systems, flat models and semilinear systems. There is no declaration stating every clause of this item. `CategoryTheory.Sheaf.flatModel_quotSMulTop` in `CategoryTheory/Sites/ReductionFlatModel.lean` concerns bounded complexes, constant Noetherian coefficient rings and a single ideal quotient; it gives neither arbitrary unbounded good inputs nor the whole-system comparisons. `DerivedCategory.KFlatModel` and its existence result in `CategoryTheory/DerivedCategory/Complete/NormalizedTower.lean` give representatives for individual constant-ring derived objects, rather than this statement.

## WANTED

None. The item is an agent-formulated simultaneous refinement, and the existing Stacks sources supply its general ringed-topos input. I read `literature/stacks-project/sites-cohomology.tex`, especially labels `lemma-pullback-K-flat` (0G7E), `lemma-derived-base-change` (06YY), `lemma-tensor-product-K-flat` (07A2), `lemma-K-flat-quasi-isomorphism` (06YP), and `lemma-pullback-tensor-product` (07A4). The tag-to-label assignments were checked in `literature/stacks-project/tags/tags`. The proof is marked agent-written because the sequence-topos specialization and explicit transition squares are my argument, rather than a literal Stacks theorem.

## Errors and corrections

No statement dispute or mathematical change to the item. Its original source correctly warns that the simultaneous-system claim is not the literal statement of the two initially cited tags. The proof now supplies the missing intermediate construction: the constant-sequence geometric inverse image and the single ring map from the constant coefficient ring to the varying ring object. This permits applying the existing general K-flat pullback theorem directly to whole systems. In particular, the proof never assumes that a quotient map is flat or that arbitrary termwise tensor extension is exact.

The current blueprint ancestor is `def-weil-frobenius-coefficient-twists`; I read its `main-20261015` text under `sec-six-functors-basics/sk-def-purity-conv/`, together with that unit's conventions. Its scalar-extension and finite-reduction compatibility is the relevant place. I also read the recorded chapter and unit. The split stays below that compatibility via the item's existing three-node ancestry. The general ringed-site results are declared as generic tools in `split_report.tool_uses`; they do not replace a purity route step. No SGA source is used.

## Not duplicates

No new nodes. I searched the whole DAG for K-flat, ringed-topos, semilinear-system and componentwise statements, and used the existing general nodes instead of introducing new flat-model or operation clauses. The whole-blueprint searches `K-flat`, `tensor cancellation`, `semilinear` and `quotient system` found no blueprint statement identical to this item. `blueprint.same_as` remains empty. The existing `lem-pur-system-ringed-sequence-site` supplies the general small presentation; its specialized coefficient-site definition is not incorrectly applied to arbitrary sites.

## Review by NW

I checked the item against its Stacks source and the precise current blueprint ancestor, and reviewed delivery-errors B through E with the source and cited statements open. No new statement-only nodes are needed, so there is no new source attribution, definition, or Mathlib match requiring certification. Every step is below 1200 characters; none exceeds the long-step threshold. The proof separates the projection construction, K-flat preservation, derived scalar comparison, tensor computation, tensor quasi-isomorphism preservation, exact inverse image, and the strict transition calculation.

Step 1 uses the statement of `lem-coef-semilinear-derived-sections` identifying systems with modules on the inverse-sequence topos, and `lem-pur-system-ringed-sequence-site` for its small presentation. Both statements permit a general sequence of commutative ring sheaves. The short added adjunction calculation is explicit: maps from a constant sequence are cones, and cones are maps to its limit; finite limits of sequences are componentwise. Thus the diagonal is a geometric inverse image. Countable multiplication preserves smallness relative to the module universe, so the later general-site theorems have the required small presentation. The given compatible maps R to B_n assemble into one ring-object map, with no new hypothesis.

Step 2 uses `def-pur-sheaf-tensor-product` exactly for its sectionwise tensor followed by sheafification and induced restriction maps. With vertical covers this yields the stated strict D_B, including its actual transitions. `lem-weil-pbc-ringed-topos-kflat-pullback` explicitly states preservation of both K-flatness and flat terms for arbitrary ringed-topos morphisms. I checked its complete statement: it is not restricted to bounded complexes or flat structural ring maps. Apply it once to the sequence projection and independently to each identity-topos R-to-B_n map. This proves both kinds of K-flatness without assuming that levelwise K-flatness alone implies system K-flatness.

Step 3 applies the same theorem first to constant-ring inverse image, making the constant complex a good system representative. `lem-weil-pbc-ringed-topoi-derived-pullback` then supplies the actual natural representative comparison for extension from the constant ring to B, and explicitly states quasi-isomorphism preservation on good complexes. Those are clauses of its statement, not inferred from its proof. The composite ringed projection has exactly D_B as its ordinary functor. The componentwise-exactness clause of `lem-coef-semilinear-derived-sections` translates quasi-isomorphisms of system complexes into componentwise ones. Naturality on the homotopy category gives naturality on every cochain map of the displayed inputs.

Step 4 uses `lem-weil-pbc-site-derived-tensor-descent` for its canonical two-variable K-flat comparison, natural in both variables. Its site-smallness and flat-term K-flat hypotheses hold by steps 1 and 2. `lem-pur-kflat-total-tensor-model` explicitly permits unbounded complexes in both directions and gives flat terms for the direct-sum total. `def-pc-tensor-complex-sheaves` specifies exactly that direct-sum total and the signed differential. The ordinary system tensor is componentwise under the ringed sequence description, so this is the displayed Z_T itself. It is a derived-system isomorphism before taking any individual evaluation.

Step 5 uses the final K-flat clause of `lem-weil-pbc-total-tensor-homotopy-cone-signs`, which explicitly covers quasi-isomorphisms with arbitrary endpoints in either variable. Factoring the two-variable map into two fixed-factor maps is elementary; step 2 supplies the fixed K-flat factors and step 3 supplies both quasi-isomorphisms. This avoids concealing a tensor-exactness assertion behind the definition of flatness.

Step 6 uses precisely the exact levelwise geometric inverse-image clause of `lem-coef-semilinear-derived-sections`. It assumes a geometric morphism of arbitrary small-site topoi, with the output coefficient rings C_n=u^{-1}B_n, exactly as in the item. This statement constructs the functor on whole ordinary derived system categories. Exactness makes its termwise action preserve cohomology and quasi-isomorphisms, giving Z_F and its natural localization comparison. There is no separate coefficient-flatness assumption.

Step 7 uses only the explicit sheaf tensor and total-complex definitions already cited. I checked the formulas on local pure tensors, including x tensor b going to f(x) tensor beta_n(b) along both routes. Tensoring the two actual strict squares produces the tensor transition square on every total summand. Applying u^{-1} produces the inverse-image square. Degree-zero cochain maps respect the stated Koszul sign. The maps extend through the defining sheafification. Thus equality is proved on system maps before localization; no faithfulness claim about derived evaluation is used.

For edge cases I checked P=0 or Q=0, the zero coefficient ring, constant towers and identity maps, the identity geometric morphism, genuinely unbounded direct-sum totals, and nonflat/nonsurjective coefficient transitions. For example R=Z, B_n=Z/2^n has nonflat quotient coefficient maps; only the good-input preservation theorem is used. A compatible constant base R=Z mapping to a tower with B_1=Z[x], B_n=Z for n>=2 and transition Z to Z[x] gives a nonsurjective transition; the same single ring-object map and strict tensor formulas still apply. No test requires quotient transitions to be surjective. At no point is a flatness conclusion made about the underlying R-module of a B_n-flat module.

All fifteen citation entries are exact substrings of the statements read. I checked that none of the principal generic tool dependencies reaches this item, and the required server checks will check the resulting entire DAG. The searches returned ordinary module flatness, scalar extension under a flat ring map, and site-cover preservation results; none gives this unbounded whole-system theorem. No search was invented or recorded from an unavailable service as a negative result. No Lean file was written, compiled, or built; no repository or launcher file was edited.

## Unfinished work

None in the split. The maintainer's independent mathematical review remains part of the delivery protocol. Server-side dry-run and push results are reported by deliver.py.
