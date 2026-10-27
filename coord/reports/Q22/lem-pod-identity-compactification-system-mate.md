# Stage-1 delivery: lem-pod-identity-compactification-system-mate

## Files written

- `dag/nodes/sec-poincare-duality/lem-pod-identity-compactification-system-mate.json`: split statement, unchanged hypotheses and conclusions, six explicit elementary assembly steps using existing nodes. No new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every step/node pair.
- `report.md`: this report. `searches.jsonl` is the required search tool's log; `write_split.py` is sandbox-only preparation.

## Attachments

None. Searched the full project `lean/WeilConjectures/` for the item id and the identity-compactification/mate notions, and read `SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/ProperLowerShriek.lean`, especially its identity-open definitions and the proper compactification comparison. Those declarations concern condensed module objects, and do not state the simultaneous varying-coefficient system mate, its exact normalization, and all transition comparisons requested here. They do not attach this item. No Lean was changed or compiled.

## Literature and wanted material

No WANTED material. The proof is agent-written. Read the master blueprint `sec-poincare-duality/sk-lem-finite/prop-cohomological-finiteness.md`, Proof Step 6, and compared the main-20261015 statement. Step 6 asserts proper coincidence and Frobenius equivariance but does not give this system-level calculation. The parent `lem-pod-proper-coincidence-frobenius` now uses precisely this cancellation before its separate limit-comparison lemma. Read the chapter record and the item's recorded unit `sk-thm-sf-compatibility`; the route is coefficient and exchange compatibility, with ordinary sheafification/adjunction operations used as tools.

Read Stacks `sites-modules.tex`, Tag 03CY (`lemma-sheafification-presheaf-modules`), Tag 03DI (`lemma-extension-by-zero`), and Tag 03DJ (`lemma-extension-by-zero-exact`), including the explicit hom correspondence; also `sites-cohomology.tex`, Tag 07A7 (`remark-base-change`) and Tag 0GL1 (`lemma-j-shriek-and-tensor`). The ringed-diagram and strict-system refinements are taken from their actual existing node statements, not attributed to these Stacks tags. There is no SGA citation.

## Problems found and changes

The original node was statement-only, with no proof. Its statement is retained verbatim. In particular it concerns ordinary derived categories of strict semilinear systems, rather than the normalized subcategory, and an equality in that category before evaluation. I supplied the naturality equation there and did not infer morphism equality from equality at all finite evaluations.

The scalar bookkeeping is also spelled out: the compact-support coefficient comparison is a composite of the open scalar comparison and the ordinary direct-image comparison. Naturality at the canonical identity-open map identifies that whole composite, and naturality at the quotient map then identifies the tower arrows. No proper base-change isomorphism, commuting tensor with a limit, flat coefficient quotient, or conservativity on morphisms is used.

## Mathlib and blueprint searches

The six fresh searches are recorded exactly from `msearch.py` in the item's `mathlib_searches` and `searches.jsonl`; the inherited searches are retained. Both semantic phrasings were read. LeanFinder finds restriction/pushforward for Zariski scheme modules, not the pro-etale varying-ring systems. LeanSearch finds unrelated extension-by-zero and shift identities. Loogle finds `CategoryTheory.Adjunction.id`, its unit and counit, and abstract conjugate formulas. Read `Mathlib/CategoryTheory/Adjunction/Mates.lean:316` through the identity-adjunction formulas at 329 and 335; these are formal ingredients, not a declaration of the geometric-system item. Grep found those formulas and one unrelated semilinear-typeclass comment. The item is not a Mathlib leaf.

Searched the whole DAG and blueprint for identity compactification, identity extension, open unit, adjunction mate, extension by zero, and quotient transitions. The existing `lem-sf-open-tensor-normalization` is the needed system-open normalization tool; the existing sheafification and scalar coherence nodes provide the remaining facts. The projection-formula identity-compactification blueprint node concerns a tensor projection formula, not this exchange/tower assertion. No new node was necessary.

## Not duplicates

No new nodes. All facts used are existing statements or the displayed elementary naturality calculations.

## Review by Q22

I read delivery-errors sections B through E, including the duplicated isolated-run copy, against the actual cited statements and the sources above. All six proof steps are below 2000 characters. Each is a substitution, universal-property argument, triangle equation, or naturality calculation from the cited statements; none hides an extra existence or geometric comparison lemma.

1. I checked the actual extension-by-zero presheaf formula and the module sheafification universal property. For the identity immersion every test object is in the nonzero branch, including over the empty scheme. Factoring the identity through sheafification gives the inverse, and uniqueness proves naturality, including maps into restricted coefficients. `lem-coef-semilinear-derived-sections` explicitly supplies the module category of the ringed topos of sequences and its ordinary complexes, so the constructed chain isomorphism is one map of systems. This does not rely on evaluations detecting equality.
2. I checked that `lem-sf-open-tensor-normalization` specifies the open unit by the unchanged section, and explicitly applies to arbitrary strict inverse coefficient systems. At the identity that unit is the inverse of the sheafification identification from step 1. The triangle identity fixes the counit after that identification. `def-weil-exact-derived-adjunction` explicitly localizes these original units and counits, so an arbitrary, possibly twisted, adjunction with the same functors has not been substituted.
3. I checked the same normalization node's restriction formula for its specified base-change map, its source and target, and its system clause. With both opens identities restriction is the identity functor, so the displayed conjugated equation is a literal specialization of that formula. Multiplication by the source isomorphism gives exactly the item's first equation. No additional mate-pasting assertion is needed.
4. I read `lem-coef-semilinear-derived-sections` for natural transformations actually constructed on the ordinary derived system categories, and `def-weil-frobenius-square-exchange` for the order of the compactification composite. Naturality at `u_N` has source `G_s F_a JN` and target `F_a G_Y N`. Substitution yields the required equality in that category. It applies to arbitrary system input N, without cartesianness, flatness, boundedness, or taking a limit.
5. I checked that `lem-trf-open-square-exchange` is for finite `A_{E,n}` on the small pro-etale sites, and explicitly says that its canonical exchange restricts to the identity. This includes our `A_m`, our square has identity vertical opens, and the finite counit mate/composite is exactly the one in the Frobenius-exchange definition. The same naturality calculation therefore proves the finite version for the specified map, not merely an unspecified isomorphism.
6. I read the statements of all five nodes cited in this step. The ordinary scalar comparison is natural in the input. The compact-support comparison is explicitly the composite with the open scalar comparison. The latter is characterized by the identity before sheafification, so its equation with `u` is forced by step 1. Naturality of the former and then of `h` gives the two written squares. Both direct-image definitions prescribe exactly these quotient-induced tower arrows. Here the coefficient comparison uses only finite rings `A_{m+1}` and `A_m`; restriction to R is simply applied afterwards. The coefficient-composition coherence is asserted by the cited compact-support comparison. Properness permits the identity compactification already fixed by the item; the argument introduces no extra geometric hypotheses.

I tested the zero complex, empty Y, the identity Frobenius situation, and the first quotient `A_2 -> A_1`. The proof uses no nonexistent `A_0`, no flatness of `A_2 -> A_1`, and works for noncartesian system objects because it uses naturality on the full ordinary derived category. No statement dispute was found. Citations were generated from, and checked as literal substrings of, the live statements. Off-unit generic tools are declared in `split_report.tool_uses`; the unit route is unchanged.

## Unfinished work

None in the stage-1 split. Independent maintainer review remains the delivery process's next step.
