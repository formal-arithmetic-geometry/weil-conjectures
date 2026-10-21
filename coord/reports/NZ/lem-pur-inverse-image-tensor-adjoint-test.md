# Stage-1 delivery: lem-pur-inverse-image-tensor-adjoint-test

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-inverse-image-tensor-adjoint-test.json`: statement item, now split in six steps; no Mathlib match for the entire statement.
- `citations.json`: one verbatim statement quotation per step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified log; `write_split.py` is a sandbox-only drafting aid, not a delivery node.

0 new nodes; 0 Mathlib leaves. All original item fields outside the split-owned fields, including source, blueprint ancestry, creation record and inherited Mathlib searches, are retained. No unit record is changed: this is not its key node.

## Attachments

None. The item tag has no occurrence under `lean/WeilConjectures/`. Concept searches there found the sheaf tensor universal property and the special condensed-point tensor comparison, which do not state this item with arbitrary scheme map, varying coefficient sheaf, specified set-sheaf adjunct, and the two conditional evaluations. In particular the `pointUpperStar` tensor isomorphism in `SixFunctors/ProEtale/ModuleObject/Basic.lean:424` concerns another functor and is not an attachment.

## WANTED

None. The sources used are present in the read clone.

## Problems found and decisions

The item had no proof. Its statement is correct, and is unchanged. The main pitfall is to prove only that the forward adjunct is linear and then assume the inverse is linear because the original unit sections generate all target sections. That generation claim is not available. I instead use the already existing module transport bijection, including its reverse direction and its explicit underlying set-sheaf adjunct formula. The existing topological-space inverse-image adjunction is insufficient for these sites; it is not cited. The general ringed-topos tensor-formula adjunction alone does not explicitly identify the specified set-sheaf adjunct, so I use the stronger geometric-module-transport statement.

All three generic tool lemmas from other units are declared in `split_report.tool_uses`, with their purposes; the purity convention unit contains no competing proof of these generic sheaf constructions. This realizes the final tensor/base-change naturality sentence in the current blueprint `main-20261015/.../sk-def-purity-conv/lem-pur-finite-kummer-level.proof.md` through the original parent comparison steps 3, 4 and 7. No route through SGA is used.

## What could not be finished

Nothing in this one-level split. The existing cited nodes remain the responsibility of their own DAG items; they are used only through their statements. No Lean files or compilers were used.

## Not duplicates

No new nodes were created. DAG tag/concept searches located `lem-weil-pbc-geometric-module-construction`, `lem-weil-pbc-geometric-module-transport`, and `lem-pc-sites-sheaf-tensor-bilinear-universal`; these are reused. Whole-blueprint searches with `tools/blueprint_refs.py search` for `bilinear`, `adjoint`, and `module-transport` located no blueprint statement of this full test, so the item's `same_as` stays empty. The nearest blueprint ancestor is confirmed as `lem-pur-finite-kummer-level`.

## Mathlib searches

Ran leanfinder, loogle, grep, and leansearch using the required msearch.py command, then a second leanfinder phrasing and a more focused grep. Exact queries and actual hits are appended to the item from this sandbox's searches.jsonl; inherited searches are retained. All services answered. I read Mathlib `Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:50-110`: its pullback is a chosen left adjoint and its construction uses presheaf pullback and sheafification. Those declarations do not by one-line specialization identify the specified underlying set inverse image or prove the original-unit-tensor test and the supplied-data evaluations. The other hits supply sheaf hom extensionality or sectionwise tensor structure, not the full item. No leaf is asserted.

## Review by NZ

I read Stacks `sites-modules.tex`, Tags 03D1 and 03D2 (pushforward and inverse-image module actions), Tag 03D3 (module Hom adjunction), Tag 03D7 (ringed-topos adjunction), and the bilinear-representability display in Section 03EK following the sheafification-tensor lemma 0GMW. I also read the current blueprint ancestor proof and the purity-convention unit, together with the repository's chapter/unit records. There are no new nodes needing further source readings.

Step 1 cites the actual statement of `def-weil-proetale-inverse-image`, which specifies the small-site set adjunction, its unit, finite-limit preservation, and transport of algebraic operations. I checked the full statement of `lem-weil-pbc-geometric-module-construction`: it gives the underlying natural isomorphisms AND the addition/action comparisons, not just existence of functors. With A=S=h^{-1}R and c=id its right action uses exactly the adjunct eta_R of id. Its left operation comparisons identify I with the specified inverse-image module functor. Thus both functors can be identified through module-linear underlying isomorphisms. Smallness and common universes come from the item's compatible-site convention; no finite-type, flatness or coefficient-constancy assumption is used.

Step 2 cites `lem-weil-pbc-geometric-module-transport`. I checked that its statement asserts the natural module Hom bijection and the formula for its underlying set adjunct; the proof takes both from that statement. Its coefficient map is specialized to the identity, so no extension-of-scalars comparison theorem is smuggled in. The sectionwise linearity calculation explains the forward direction, while the reverse direction is genuinely supplied by the cited bijection. Specializing its arbitrary module argument to M tensor_R N is legitimate.

Step 3 cites `lem-pc-sites-sheaf-tensor-bilinear-universal`. Its statement explicitly defines the bilinear sheaf maps sectionwise and gives the pure-tensor-composition bijection. I verified the target is h_*K with the R-action fixed in step 1, and computed the composite of the two bijections, giving exactly the item formula. Naturality in M and N is written out via the defining induced tensor map, rather than falsely claiming the citation explicitly asserts more than its stated naturality in the output.

Step 4 uses the already proved bijection's injectivity and componentwise equality of bilinear sheaf maps. It is an elementary deduction and makes no local-generation argument. Step 5 cites the specified unit from the inverse-image definition and writes the two coefficient-change evaluations separately. Unit naturality gives inverse-image(pi)(eta(x))=eta(pi(x)); each assumed b formula applies over the actual object h(V), and pi' has its stated pure-tensor formula. Restriction of scalars is interpreted through h^{-1}phi, with no added hypothesis that phi is surjective or flat.

Step 6 cites the specified inverse-image unit and the tensor bilinear universal property. It writes all three evaluations in the first composite, including unit naturality for g^{-1}(b^h), then both evaluations in the second. In particular the b^g normalization is applied to sections over h(V), not to arbitrary target sections. The supplied delta's algebraic compatibility and unit formula provide exactly the scalar and fibre-product identifications needed; no naturality or invertibility of b, and no existence claim for delta, is used. The induced tensor-map pure formula follows immediately by applying the cited universal property to the paired module maps.

For delivery-errors B-E, I checked all objects and hypotheses are introduced, citations use statements rather than proofs, all non-elementary steps have actual theorem nodes, and no new statement restates a clause of the item. The dependency-closure inspection of each cited node found no route back to this item. The only elementary steps are deductions from the earlier bijections or explicit substitutions into supplied formulas. Each proof step is below 1,100 characters, so none hides a lemma in a long step. Small cases checked: h=id reduces the test to the ordinary sheaf tensor universal property; M=0 or N=0 gives the unique zero map on both sides; the zero ring and empty scheme still have the same adjunction/bilinear argument; phi=id and g=id reduce the displayed evaluations to the normalization itself. No excluded non-finite-type or non-flat morphism is required anywhere. Every citations.json quote was checked as a literal substring of its cited node statement. The source error cases of delivery-errors E do not occur, so no statement correction is needed.
