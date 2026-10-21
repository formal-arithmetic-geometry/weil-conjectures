# Stage 1 report: det-lem-stratified-lattice-scheme

## Files written

- dag/nodes/sec-six-functors-basics/det-lem-stratified-lattice-scheme.json: existing statement, split into ten proof steps; no exact Mathlib match.
- citations.json: verbatim cited statements, one entry for every step/dependency pair.
- searches.jsonl: six executed Mathlib searches, with their original tool output inspected.
- report.md: this report. write_split.py is a sandbox-only construction script.

New nodes: 0. New Mathlib leaves: 0. No repository, launcher, Lean source, compiler, Lake or build operation was used for writing or testing.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and for lattice-sheaf notions did not locate a project declaration proving all three clauses. The many integral-lattice and adic-tower declarations have different conclusions. No existing sorry declaration was counted as a proof.

## WANTED

None. The current blueprint, Bhatt–Scholze PDF, and the relevant Stacks sources are present and were read locally.

## Source and imported-proof corrections

The three conclusions and the qcqs hypothesis are retained. I added the implicit prime/finite-extension, condensed-coefficient, module-object, lisse, lattice, size and constant-sheaf conventions and their definition dependencies. These are the chapter's existing coefficient conventions; no Noetherian, normality or invertibility-on-X hypothesis was added. This is a clarification, not a STATEMENT-DISPUTED correction.

The imported proof's phrase “finitely many affine V_k covering X on which L is trivial” cannot mean Zariski-open charts: lisse E-modules only trivialize pro-étale locally. Step 3 explicitly extracts affine pro-étale objects from a trivializing covering and combines them into one flat surjective quasi-compact map. This keeps the unit's fpqc lattice-scheme route. No unit/chapter records were changed because this item is a detail node, not the unit's statement.

The imported citation to Tag 0APK was described as quasi-affine descent; the actual lemma is effective descent for ind-quasi-affine morphisms. In Stacks' convention a quasi-affine scheme is quasi-compact, so an infinite disjoint union of nonempty affine schemes cannot itself be quasi-affine even though it is an open of the spectrum of the product of their rings. I checked more-groupoids.tex lemma-ind-quasi-affine and more-morphisms.tex definition-ind-quasi-affine. Step 6 verifies the exact existing DAG theorem's hypothesis on every quasi-compact open, using finitely many components, instead of asserting the whole infinite union is quasi-affine. This repairs the local inference while preserving the stated unit route and its Tag 0APK.

The imported invert-ell node gives the localization of the coefficient ring, not its asserted continuous-section formula. Step 1 uses it only for localization, and cites the existing continuous-coefficient-realizations node for the continuous-function comparison, including compatibility with A→E.

The universal lattice does not require a separate module-descent lemma: once representation and étaleness are established, evaluation at the identity of the representing pro-étale object produces it, with its exact pullback property.

## Not duplicates

No new node was created. The whole-DAG and blueprint searches found lem-weil-pbc-lattice-sheaf-locally-constant, lem-weil-pbc-continuous-coefficient-realizations, lem-a1-ind-quasi-affine-fpqc-effective-descent, and the existing 02KU/02VN property-descent nodes. These are cited directly. The local classification node uses isomorphism classes of pairs; step 2 explicitly proves its equivalence with the embedded submodules in this item's statement, so it is not silently treated as the same formulation.

## Review by NF

I read the current main-20261015 statement and all three paragraphs of its proof, the enclosing sk-lem-stratified-lattice unit and sec-six-functors-basics chapter, Bhatt–Scholze Definition 6.8.1, Lemma 6.8.2, Definition 6.8.3 and Proposition 6.8.4(6), including its lattice-coset proof on printed pp.58–60. For scheme descent I read Stacks more-groupoids.tex, Tag 0APK (lemma-ind-quasi-affine), and descent.tex Tags 02KU (lemma-descending-property-separated) and 02VN (lemma-descending-property-etale). There are no new nodes with sources to audit.

I opened and read the statement of every cited node. Step 1 uses exactly the natural continuous-coefficient comparison and the ring localization isomorphism, checking total disconnectedness and writing the localization/tensor maps. Step 2 uses exactly the pair-valued lattice sheaf and its trivial-bundle coset classification, checking injectivity of the unit map on free charts, image/pair equivalence, and restriction compatibility. This establishes the sheaf property as well as clause (1); it does not use an uncited rank lemma or the Noetherian-only étale-local lattice-existence node.

For step 3 I checked that the pro-étale-site definition supplies the finite affine extraction over every affine open, weak-étale stability gives the finite coproduct map's flatness, affine permanence makes the finite union affine, affine schemes are qcqs, and qcqs-morphism permanence gives quasi-compactness against the original quasi-separated X. Thus the singleton cover meets the effectivity and separated-descent hypotheses. The source's affine charts need not be Zariski trivializing opens.

Step 4 uses the coproduct theorem's actual open-and-closed components, the full clopen-description theorem's bijection of morphisms with label functions, and fpqc descent of morphisms. I wrote the local-constant-sheafification argument instead of citing the finite-constant representability node for an infinite set. Step 5 uses these same two coproduct statements to turn each label's sheaf transition into an actual scheme morphism, to invert it, and to check the cocycle. This is an elementary reuse of those statements; it does not assume an unproved continuous matrix action.

Step 6 takes only effectivity from the existing ind-quasi-affine descent statement. I verified its quantifier over all affine opens and all quasi-compact opens, showed that a quasi-compact open meets only finitely many components, and placed it in an affine finite coproduct. Affine permanence gives the same description after restriction to an affine base open. The quasi-compact open is quasi-affine; neither the whole lattice scheme nor T→V is asserted quasi-compact. Step 7 checks étaleness on the identity charts and describes the diagonal componentwise, then uses the exact 02VN/02KU descent statements. The singleton map is flat, surjective, and quasi-compact as required. Surjectivity of the result follows from the nonempty standard-lattice component, with no appeal to a nonexistent global lattice of L.

Step 8 uses the fpqc-base-change node and weak-étale stability with their actual unrestricted base-change hypotheses. The explicit two inverse constructions between morphisms and lattice sections use fpqc descent of scheme morphisms in one direction and the established lattice sheaf property in the other; the cocycle is precisely the one already constructed, so this is not a statement about an unrelated descended object. Step 9 uses the existing étale-implies-weakly-étale clause so the representing scheme is an allowed site object, and evaluates the representing isomorphism on its identity to obtain the actual embedded universal lattice. Step 10 tests rank zero and empty X. For positive rank and an infinite lattice set, the proof never uses finite S or quasi-compactness of the representing scheme. The finite-extension coefficient assumption is exactly the original chapter assumption.

I checked delivery-errors B–E against these files: no new statement-only nodes or leaf records need validation; all notions introduced in the item are defined inline or cite their definition nodes; every non-elementary input has an explicit node citation; citations.json copies the statements verbatim; no proof cites a hidden argument of a node. The remaining constructions are written out rather than moved into clause-sized helper nodes. Every step is below 2000 characters. I also checked the transitive dependencies of each substantive tool against this item; none reaches it, so the old import cycle is not retained by the replacement proof. Off-unit uses are declared in split_report.tool_uses with reasons: generic coefficient, scheme-cover, clopen-coproduct and fpqc descent tools implement the same unit route.

I read all six search outputs. Loogle returned ideal-sheaf order-lattice instances, not integral lattices. The semantic searches returned p-adic period rings, étale over-categories, generic constant-sheaf results and coproduct/gluing declarations. The candidate Scheme.LocalRepresentability.isRepresentable was opened: it assumes relatively representable Zariski-open charts, so it does not give fpqc effectivity here. The generic IsStack class was also opened; it defines effectivity rather than proving this scheme descent theorem. Grep found no relevant lattice-sheaf theorem. Two semantic phrasings were tried, and the exact executed queries, results and verdicts are retained in the node.

## Unfinished work

None in this one-level stage-1 split. Existing dependency nodes retain their own stage state. Delivery validation is performed by the required server dry run; no local DAG/preflight checker was run.
