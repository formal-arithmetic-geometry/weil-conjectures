Files written:

- `dag/nodes/sec-smooth-purity/lem-kun-tor-cokernel-flat.json` — the item, split into two proof steps; no new nodes.
- `citations.json` — verbatim citations for Step 2.

Attachments: none. No sorry-free project declaration states this item exactly.

WANTED: none. The imported blueprint proof is agent-written; the blueprint source path is retained as the source record, and no unavailable external theorem is needed after reusing the existing ringed-site criterion.

## Not duplicates

- `lem-kun-tor-cokernel-flat` vs `lem-weil-pbc-site-flat-opcycles-tor-criterion`: the latter is the more general statement for an arbitrary small ringed site and assumes exactness of every tensor complex in one degree; this item specializes to the small etale site of a scheme with constant ring sheaf and phrases the hypothesis as cohomology vanishing in every lower degree.
- `lem-kun-tor-cokernel-flat` vs `lem-pc-module-flat-opcycles-tor-criterion`: the latter is only the one-point-site/module-over-a-ring case, while this item concerns sheaves on the etale site.

## Review by Q39

I read the imported item node, its blueprint proof record, the chapter and unit context, and the existing general node `lem-weil-pbc-site-flat-opcycles-tor-criterion`. I also read `def-kun-derived-tensor` to verify that the tensor of a complex with a degree-zero module is the direct-sum total tensor complex and that the tensor factors may be interchanged by the sign symmetry. Mathlib searches were run for the item with LeanFinder, Loogle, grep, and LeanSearch, with a second LeanFinder/Loogle/grep phrasing; they found only one-ring module flatness criteria, no matching sheaf theorem, and LeanSearch was unavailable.

Step 1 uses no node: for an arbitrary module sheaf and any integer `a`, the hypothesis includes `n = a - 1`, and the definition of cohomology identifies vanishing in that degree with exactness there. Step 2 cites the general ringed-site criterion and the derived-tensor convention. I checked that the small etale site of `T` is a permissible small site, that `Λ_T` is its structure sheaf, that the assumed flatness supplies the criterion's flat-term hypotheses, and that Step 1 supplies exactness after every module-sheaf tensor. The criterion's opcycle at degree `a` is exactly `coker (K^(a-1) → K^a)`, the stated `N`. I checked the edge case that `a-1<a` for every integer `a`; no boundedness or extra hypothesis was introduced. The only correction to the imported proof was replacing its hidden Tor/stalk paragraph with the explicit vanishing-to-exactness step followed by the existing general criterion, and recording the tensor-convention citation.

What was wrong in the imported split: its single paragraph used the general flat-opcycles argument without citing the existing general node and without making the degree `a-1` exactness inference explicit. No statement correction was needed, and no new node was justified.

What I could not finish: nothing; the sandbox is ready for the required dry run.


## Second reading by Q39

- Item statement: checked every quantifier against the original blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-tor-cokernel-flat.md` and against Stacks `sites-cohomology.tex`, Tag 08G0, label `lemma-last-one-flat`, lines 12403–12428, and Tag 0F1M, label `lemma-bounded-below-tor-amplitude`, lines 12487–12501; PASS. The blueprint assumes ordinary tensor vanishing, so it needs neither boundedness nor K-flatness. The existing general criterion states precisely this variant. Added definition references without changing any hypothesis or conclusion. Source copies were read under `/home/ubuntu/weil-launcher-nt/literature/` because the shared repository omits these untracked source documents.
- Step 1: checked against the full statement of `def-pc-acyclic-complex-modules`, specifically its formula $H^i=\ker d^i/\operatorname{im}d^{i-1}$; PASS after adding the missing definition citation. The inequality $a-1<a$ and the vanishing-quotient identity are elementary for every integer $a$.
- Step 2: checked the full statements of `lem-weil-pbc-site-flat-opcycles-tor-criterion`, `def-kun-derived-tensor`, and `def-weil-size-convention`; PASS after spelling out the single surviving totalization summand, differential, sign $(-1)^{j\cdot0}=1$, and differential compatibility of the tensor swap. The standing small-site convention supplies the criterion's smallness, the same commutative constant ring sheaf is used throughout, every term is flat by hypothesis, and step 1 supplies universal exactness at $a-1$. The criterion concludes flatness of exactly the stated cokernel, not of the image or the cohomology sheaf.
- New nodes: none; checked the sandbox node list, and B1–B7 impose no new-node repairs. Searches of all `dag/nodes/` for Tag 08G0, flat opcycles, and cokernel flatness confirmed the existing ringed-site criterion is reusable. The module-only criterion is not the sheaf statement; no duplicate, special-case, elementary, or clause-restating node was introduced.

Edge cases checked: the zero complex gives the zero flat cokernel; on the empty scheme every module sheaf is zero; over a field the conclusion agrees with flatness of every stalk; $a=0$ uses degree $-1$ and $a=1$ uses degree $0$, with the same calculation and no lower bound assumption. A complex consisting of multiplication by $2$ from degree $a-1$ to degree $a$ over $\mathbf Z$ has cokernel $\mathbf Z/2$ but fails the hypothesis on tensoring with $\mathbf Z/2$ in degree $a-1$, so the criterion does not mistakenly assert its flatness. A complex supported only in degree $a$ has cokernel its assumed flat degree-$a$ term and satisfies the lower-degree hypothesis.

I independently ran `msearch.py` with the semantic query “In a category of module sheaves, tensor homology vanishing forces the coimage of a differential between flat objects to be flat”, Loogle `"opcycles"`, and a grep combining `opcycles|coimage|cokernel` with `flat|Flat`. The semantic results are module-over-one-ring exactness criteria; Loogle gives opcycle objects and their cokernel isomorphisms; grep gives no match. None states this sheaf flatness theorem. Read `WeilConjectures/CategoryTheory/DerivedCategory/FlatModel.lean`, lines 63–82: `CategoryTheory.ObjectProperty.flat_opcycles_of_exactAt` has categorical-flatness hypotheses; its agreement with tensor-flat sheaves still needs a comparison, so it is not an exact one-line attachment (as the existing ringed-site criterion's candidate record also explains). Read the unit and chapter records: using the ringed-site criterion as a generic tool does not change their route. The tool use remains a request in `split_report`, not a worker-written maintainer `tool_uses` field.

Changes made and why:

- Added the existing definition dependencies for the site, constant ring sheaf, cochain complex, module-sheaf category, flatness, ordinary tensor, and cohomology, so the statement is independently interpretable.
- Added the cohomology-definition citation to step 1 and the standing small-site convention to step 2.
- Replaced “up to the stated sign symmetry” by the explicit degree-zero sign and chain-map calculation required by E5.
- Rebuilt `citations.json` with one verbatim statement quote for every repaired citation; each quote includes the hypotheses the step actually uses.
- Preserved the first reader's review and corrected search records to contain the actual logged queries/results. The initial invalid Loogle query is now identified as invalid rather than absence evidence; the service outage remains unavailable.

The original blueprint proof's assertion that the cokernel sequence has flat terms would assume the desired flatness of its final term. Its right exactness after tensoring does not require that assumption. The first worker had already removed this circular wording; the retained ringed-site criterion provides the complete independent diagram chase. This is a proof repair, not a disputed or weakened statement. No mathematical obstruction remains.
