## Worker report

Files written:

- `dag/nodes/sec-zeta-weil/lem-zl-condensed-henselian-lisse-rigidity.json`: statement, split; original statement unchanged. Six steps follow Hemo–Richarz–Scholbach, Corollary 4.4(1)-(2).
- `dag/nodes/sec-zeta-weil/lem-zl-henselian-wstrict-local-invariance.json`: statement, unsplit; no Mathlib match. Bhatt–Scholze Lemma 2.2.13, using the local-ring characterization of Lemma 2.2.9. No proof or proof dependencies are installed in this new node.
- `citations.json`: verbatim extracts for all eleven step/node citation pairs.

Attachments: none. I searched `WeilConjectures/` for the exact blueprint tag, henselian/lisse combinations, and the w-strict locality/quotient terminology. The existing w-strict localization and w-contractible cover constructions do not assert henselian reduction invariance; no closed declaration gives the item. No Lean was written or compiled.

WANTED: none. Both HRS and Bhatt–Scholze PDFs are present in `literature/`; Stacks `more-algebra.tex` and `tags/tags` are present.

The incoming node had no proof or proof dependencies. It already recorded unsuccessful item-level Mathlib searches with two semantic formulations; I read and retained those results. I added the component-space topology and constant-discrete-scalar notion to statement dependencies because they occur in the statement. I found no statement dispute or change of coefficient category. In particular I retain the ordinary derived category and arbitrary commutative condensed coefficients, without a t-admissibility assumption.

Nothing required by this split remains unfinished. The new lemma is intentionally statement-only, as required for a one-level split. The existing component-site equivalence and pullback/locality nodes are reused without changing them. There is one new node and zero Mathlib leaves.

## Sources and searches

I read Hemo–Richarz–Scholbach, `hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf`, pp. 8–10, including the construction (4.1), Proposition 4.3(3), and all of the proof of Corollary 4.4. The proof first compares clopen subdivisions using unique henselian lifting of idempotents, next invokes w-strict locality invariance, and finally uses Proposition 4.3(3). This is exactly the route in the split.

For the new node I read Bhatt–Scholze, `bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`, Lemmas 2.2.9 and 2.2.13 on pp. 10–11. The latter is for an arbitrary ring henselian along an arbitrary ideal. Its w-strict locality is equivalent, by Lemma 2.2.9, to the definition already recorded in `sk-def-pe-wlocal`. I also read Stacks Tag 09XI, `more-algebra.tex`, `lemma-characterize-henselian-pair`, especially clause (3), against the project's idempotent formulation of henselian pairs. Step 1 uses that formulation directly and needs no new idempotent theorem.

Before creating the node I searched the whole DAG statements for henselian pairs and w-strict locality, for the BS lemma number 2.2.13, and for Tag 09XI. I ran `tools/blueprint_refs.py search` for henselian terminology, `w-strictly`, and `henselian along`, and used `ancestor` to check the recorded ancestry. None states the new lemma. The unit and chapter records were read; the item's ancestry remains the local-perfect-model input to Step 3 of smooth-proper relative duality. I read the current main-20261015 proof of that ancestor, whose perfect-form paragraph explains this downstream use. No unit route or realized fields are changed; this item is not the unit's key theorem.

The five new-node Mathlib queries are logged in `searches.jsonl` and copied exactly into its `mathlib_searches`: two LeanFinder formulations, LeanSearch, Loogle `HenselianRing`, and a source grep for henselian/w-local or henselian/w-strict combinations. All five services succeeded. The semantic hits were `HenselianRing`, `HenselianLocalRing`, their constructor/projection declarations, the local-ring TFAE, and adic-completeness implying henselianity. I read the Henselian module's definition and root-lifting API. None states w-strict locality invariance, and the grep returned no hits. There is therefore no exact or one-line Mathlib specialization.

## Not duplicates

lem-zl-henselian-wstrict-local-invariance vs sk-def-pe-wlocal: the existing node defines w-strict locality; it makes no comparison across a henselian quotient.

lem-zl-henselian-wstrict-local-invariance vs det-pe-wlocal-strict-contractible: the existing node records definitions and equivalent formulations, not invariance under a henselian ideal.

lem-zl-henselian-wstrict-local-invariance vs lem-zl-condensed-henselian-lisse-rigidity: the new node concerns w-strict locality alone; it has no extremal disconnectedness, component homeomorphism, condensed coefficients, derived category, or rigidity conclusion. The item proves the topological comparison and constructs its equivalence using the pre-existing component-site theorem. The item's clauses are not renamed as new nodes.

## Review by Q35

I checked B–E with the node statements and the sources open. The item agrees with HRS Corollary 4.4 in both topological clauses and in its lisse-equivalence clause. HRS defines lisse as dualizable. The extra concluding assertions about morphisms and scalar extension follow from equivalence and from the existing coefficient-compatible pullback theorem; they add no hypotheses.

For Step 1, I opened `def-weil-pbc-henselian-terminology`: its statement explicitly gives unique lifting of idempotents for every finite A-algebra, so taking B=A supplies exactly the bijection used. `lem-weil-pbc-spec-clopen-idempotent` explicitly identifies clopens with D(e) for unique idempotents. The formula for inverse image is membership in a prime under the quotient homomorphism. This is the elementary translation, not a separate node. Tag 09XI verifies that this is the henselian condition used by HRS.

For Step 2, I opened `sk-def-pe-wlocal`, including its affine qcqs/spectral paragraph; `lem-pe-spectral-components-profinite` gives compact Hausdorff component spaces; and `lem-weil-pbc-quasicompact-components-clopen-intersection` states the intersection formula for components under exactly the compactness and compact-open-basis conditions satisfied by affine spectra. That formula supplies clopen separation of distinct components. Every clopen is saturated because a connected component cannot meet both it and its complement. The injectivity argument uses surjectivity on clopens, while the surjectivity argument uses injectivity on clopens and compactness of the image. I wrote both arguments and the closed-map proof of homeomorphism, so no inverse-limit reconstruction theorem or Stone duality is silently assumed.

For Step 3, the new node explicitly says A is w-strictly local iff A/I is; the henselian-pair hypothesis is precisely the item's hypothesis. It is not applied to another ideal or localization. `sk-def-pe-wlocal` defines w-contractibility as w-strict locality plus extremally disconnected component space. Step 2 transfers that second condition, proving both directions, rather than mistaking w-strict locality alone for contractibility.

For Step 4, `lem-zl-condensed-wcontractible-lisse-evaluation` explicitly supplies the coefficient-compatible component maps and their equivalences on dualizable objects. Both T and Z are affine and w-contractible at this point. I also opened `lem-zl-condensed-lisse-proetale-locality`: its statement covers every scheme morphism and asserts exact monoidal pullback, preservation of dualizables, the canonical coefficient identification, and constant-scalar compatibility. Those are exactly the properties taken here, regardless of that node's separate descent assertion.

For Step 5, the cited evaluation node actually states how the component-site inverse image is constructed from finite clopen subdivisions and their inverse limits. I wrote its compatibility with i on a clopen piece as the equality Z times_T T_U = Z_{h^{-1}U}. The inverse-limit construction is compatible with this identity: affine coordinate rings use filtered colimits and base change A to A/I commutes with them. Thus the two inverse-image composites agree; no theorem that an arbitrary point-map square is a square of sites is being assumed. The coefficient identifications all come from the same condensed ring. This is functoriality of the cited construction, not a new comparison lemma whose content equals the rigidity theorem.

For Step 6, I checked that a homeomorphism h identifies the two categories of profinite sets over the component spaces, including their finite jointly surjective coverings and their coefficient sheaves. Consequently h-star is an equivalence. Conjugating by the two equivalences of Step 4 proves that the actual restriction i-star is an equivalence. The final citation is exactly the scalar-extension clause of the existing locality/pullback statement; full faithfulness then needs only the definition of equivalence.

For the new node, I checked that all objects and both meanings of w-strict locality are stated, its source is the precise BS lemma, its proof and proof dependencies are empty, its chapter and unit are inherited, and its blueprint.from points through this item to the correct ancestor with a definite proof place. The tests were I=0 (the identity equivalence); A=0 (empty component spaces); an algebraically closed field and its square-zero thickening; the henselian pair k[[t]], (t) (the nonzero generic part remains, but both component spaces are a point); and a field with non-separably-closed residue field (both sides fail strict locality). No nonzero ring can have I=A under the henselian hypothesis because uniqueness of idempotent lifts would identify 0 and 1. Arbitrary, non-finitely-generated ideals are allowed by the source; no finite-presentation hypothesis was added. These checks also cover zero condensed coefficients and the zero dualizable object: the categorical equivalences still make sense.

I corrected the initially drafted Step-2 citation extract to quote the affine-spectral sentence, rather than the unused w-contractibility clause of that definition. Every step/node quote is a verbatim substring of its cited statement. No proof step exceeds 2000 characters. There are no circular dependencies, no statement-only proof sketches in the new node, no SGA citations, and no newly claimed Mathlib leaves. The three off-unit citations are declared as generic tools in split_report.tool_uses: the affine clopen dictionary, profiniteness of component spaces, and the general component/clopen-intersection theorem. They supply background algebra/topology, not a substitute route for a unit step.

Mechanical validation will be performed by the required remote dry run; this report records my mathematical self-check, not independent approval.
