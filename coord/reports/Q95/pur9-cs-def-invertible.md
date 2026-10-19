# Q95: pur9-cs-def-invertible

## Files written

- `dag/nodes/sec-smooth-purity/pur9-cs-def-invertible.json`: definition, split by naming its constituent notions; six logged Mathlib searches found no matching definition. No new nodes and no Mathlib leaves.
- `citations.json`: `[]`, since this definition has no proof steps.
- `searches.jsonl`: actual searches recorded by `msearch.py`; all six completed successfully.

## Attachments

None for the whole item. The searches under `WeilConjectures/` found no declaration tagged `(blueprint: pur9-cs-def-invertible)`, and no pro-etale definition covering the item. `AlgebraicGeometry.Etale.DerivedCategory.isInvertible`, in `WeilConjectures/SixFunctors/Etale/Derived/Coefficients.lean:89`, defines an existential two-sided inverse only on the etale site. `CategoryTheory.IsInvertible`, in `WeilConjectures/Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean:98`, is a general monoidal-category predicate with two inverse isomorphisms, rather than the chosen triple on the two specified coefficient categories. The adjacent `isInvertible_iff_of_braided` explains the relation of its two-sided convention to the blueprint's one-sided convention. These are useful implementation references, but neither alone states every clause of the item. They are not being used as finished proofs of the full item.

## WANTED

None. The source of this definition is present.

## What was wrong or incomplete

The imported definition had no statement dependencies, despite using a finite coefficient ring, two sites, two derived module-sheaf categories, a constant coefficient complex, and derived tensor. I made those notions explicit and cited existing nodes. The ring, the objects, the isomorphism, and the existential condition remain the blueprint's. Adding the parameters implicit in the notation does not impose any geometric hypothesis: there is no smoothness, finite-type, noetherianity, constructibility, boundedness, or invertibility-of-ell assumption on X. No statement dispute is needed.

The item is a definition, so it has no proof steps to subdivide. It is not the unit's key theorem and does not fill or modify the unit's realization fields. No claim about the coprojection map, classification of invertibles, dualizability, or preservation under pullback has been inserted into the definition.

## What could not be finished

Nothing within this one-level stage-1 split. The existing dependencies retain their current states and remain their own items where applicable. No Lean was written and no compiler or build tool was run.

## Not duplicates

No new nodes. Whole-DAG searches for `invertible object`, `tensor inverse`, and tensor-invertibility terminology, together with `tools/blueprint_refs.py search`, found this blueprint definition and statements that use it, rather than another definition of precisely these chosen data on both sites. In particular `def-pur-section-invariant` and `lem-pur-coprojection` use invertibility and do not define this triple. Thus `blueprint.same_as` is empty; `blueprint.from` remains null because the item itself is an imported blueprint node.

## Review by Q95

I read the complete definition in `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-coprojection/pur9-cs-def-invertible.md`, the current chapter and coprojection unit texts, and their DAG chapter/unit records. The definition's content is exactly a pair of objects with one displayed tensor isomorphism, followed by existence of the inverse data, on each of the two sites. I preserved that content without adopting the extra bounded/constructible context of the coprojection theorem. The chapter/unit route is unchanged.

I opened and read the statement of each of the six dependencies. `def-weil-l-adic-coefficient-extension` supplies the valuation ring, uniformizer and quotient A for n at least one. `def-weil-pbc-proetale-site` supplies the small pro-etale site, its universe/skeleton convention, its category of A-module sheaves, and its ordinary unbounded derived category. `def-weil-pbc-etale-site` supplies the other site, and `def-weil-pbc-derived-categories` defines precisely the ordinary unbounded derived category on that site, not merely its bounded subcategory. `def-weil-pbc-constant-sheaf` supplies the constant ring sheaf on either site. Its degree-zero complex is specified directly in the item. Finally `lem-weil-pbc-site-derived-tensor-descent` actually states the derived tensor bifunctor on an arbitrary small ringed site: it applies to both chosen sites with R=A_X. Its size hypothesis is accounted for by the explicit universe convention. I did not cite the etale-only `def-kun-derived-tensor` for the pro-etale tensor product, and did not infer a tensor theorem merely from a definition of flatness.

There are zero proof steps and hence no step/node citations to quote. The C1/C4 check here concerns the six statement dependencies just described, not a fabricated proof. The empty citation list is intentional. The B--E audit finds no new-node statement or source tag to check, no duplicate child, no clause moved into a child, no elementary fact promoted to a node, no circular proof, and no off-unit theorem used in a proof. I checked the dependency statements rather than using their internal proofs. The six searches recorded in the node match the six actual log entries; both semantic phrasings, Loogle, and both source greps were read. Their hits concern braidings/coherence or invertibility of morphisms, not a Mathlib definition of tensor-invertible objects. The similarly named general object predicate is in the project's `WeilConjectures/Mathlib/` tree, not in Mathlib itself.

For edge cases I checked X empty and disconnected X: the definition still quantifies objects and isomorphisms in the same category and imposes no unstated connectedness or nonzero-object condition. At n=1 the ring is the residue coefficient ring and the displayed formula is unchanged. No inverse is chosen by an unproved existence theorem: the triple takes the inverse and isomorphism as input data, and invertibility of L is a proposition asserting existence of those data. No second inverse isomorphism, coherence equation, or rank-one classification has been silently required. On the etale site both objects and the isomorphism live entirely in its own derived category; no etale/pro-etale equivalence is assumed.

## Second reading by Q95

- Item statement: checked all three sentences against the current `main-20261015` source `sec-smooth-purity/sk-lem-coprojection/pur9-cs-def-invertible.md`; PASS, the chosen triple and the existence predicate on each site agree exactly.
- Proof steps: zero, checked against the source definition and stage-1 definition rule; PASS, no theorem proof is being replaced by a child or an elementary assertion.
- New nodes: zero, checked the complete sandbox node inventory; PASS, no child, duplicate, restated clause, or source tag requires repair.
- Dependency `def-weil-l-adic-coefficient-extension`: read its statement; PASS, supplies precisely the finite extension, valuation ring, uniformizer, and positive-index quotient, with no condition on the scheme.
- Dependency `def-weil-pbc-proetale-site`: read its statement; PASS, supplies the site, universe convention, module sheaves and ordinary unbounded derived category.
- Dependency `def-weil-pbc-etale-site`: read its statement; PASS, supplies the other site for arbitrary schemes.
- Dependency `def-weil-pbc-constant-sheaf`: read its statement and Stacks `sites.tex`, label `example-constant-sheaf` (0H7J); PASS, constant means sheafification, not the possibly non-sheaf constant presheaf.
- Dependency `def-weil-pbc-derived-categories`: read its statement; PASS, supplies the ordinary unbounded etale category, with no boundedness imposed on the item.
- Dependency `lem-weil-pbc-site-derived-tensor-descent`: read its statement and Stacks `sites-cohomology.tex`, labels `lemma-K-flat-resolution` (06YS), `lemma-derived-tor-quasi-isomorphism-other-side` (06YT), `definition-derived-tor` (06YU) and `lemma-factor-through-K-flat` (0G7D); PASS, the bifunctor is defined for either small ringed site with the stated universe convention.
- Citations: checked `citations.json` against the empty proof; PASS, there is no step/node citation for which to manufacture a quotation.
- Duplication and existing Lean: independently searched the whole DAG and imported blueprint for invertibility and read the general monoidal and etale predicates in slopmaster2; PASS, neither supplies the complete two-site definition with chosen data. Ordinary invertible structure-sheaf modules and cohomological Picard groups are different notions. Also searched the read-only master six-functor sources; no matching definition found. No sorry declaration is treated as a proof.
- Independent Mathlib searches: ran LeanFinder with Picard-groupoid vocabulary, a broad declaration/source grep, and Loogle with `"Pic"`; PASS, the actual nine-entry search log contains the original six and these three. Read the potentially relevant `CommRing.Pic`/`Module.Invertible` source: it treats ordinary modules, not derived sheaf objects, so does not make this item a Mathlib leaf.
- Small cases: at n=1 the coefficient ring is the residue field. On a nonempty geometric point the zero complex cannot have a tensor inverse, while the coefficient unit does; the definition has exactly these outcomes. On the empty scheme the unit sheaf is itself zero and its derived category is trivial, so the zero object is invertible, correctly. Disconnected schemes permit componentwise inverse data, with no connectedness hypothesis. n=0 is outside the positive coefficient-index convention; if formally admitted it would give the zero ring and a trivial category, not a contradiction.
- Form and route: checked B1-B7 and C-E against the item and its dependencies; PASS, all displayed data are typed in one chosen category, TeX is encoded once, and no off-route proof or prohibited SGA reference was introduced. Current chapter and unit texts were read for context; their geometric hypotheses are not added to this definition.

Changes: added three independently run Mathlib searches to the item's search records and retained their actual log output; appended this second-reading audit, including explicit zero-object, field, empty-scheme, disconnected and n=0/1 checks. The mathematical statement, dependencies, empty proof and empty citations needed no repair. The first worker's sections, including `## Review by Q95`, are preserved.
