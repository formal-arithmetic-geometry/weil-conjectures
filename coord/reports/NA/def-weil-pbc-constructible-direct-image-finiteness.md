# Stage-1 worker report

## Files written

- `dag/nodes/sec-proper-base-change/def-weil-pbc-constructible-direct-image-finiteness.json`: definition, split; no new nodes; Mathlib searches found no match.
- `citations.json`: empty list because this item is a definition with no proof steps.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the archived master source for the item id, blueprint tag, `FIN`, and constructible direct-image terminology. No declaration states this definition exactly; no sorry-free attachment is claimed.

## WANTED

None.

## Corrections and limitations

The imported item was an unsplit definition. I retained its complete two-clause predicate and all coefficient, base, and invertibility hypotheses from the master blueprint source. The Stacks 09AI equivalence is explanatory context in the definition; FIN itself is explicitly a hypothesis, so no theorem node is split from it. All notions used in the statement are already represented by the four existing statement dependencies, and introducing a new node would duplicate a clause or restate the item. The item remains a definition with empty proof and proof-dependency lists.

## Review by NA

I read the master definition `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/def-weil-pbc-constructible-direct-image-finiteness.md` (order 1301), the `sk-thm-properbasechange` unit, and the `sec-proper-base-change` chapter. I checked the full statements of `def-weil-pbc-site-comparison-morphism`, `def-weil-pbc-adic-coefficient-datum`, `def-weil-pbc-constructible-complexes`, and `def-weil-pbc-proetale-modules`: these are exactly the notions named by the item's statement dependencies. The statement introduces the finite-level coefficient `Lambda=P_n=A/I^n`, the noetherian finite-dimensional base and invertibility assumption, the comparison pullback characterization of constructibility, and both FIN clauses (constructibility of every higher direct image and a uniform nonnegative amplitude bound). Because this is a definition there are no proof steps or node citations, and `citations.json` is therefore `[]`.

I checked the edge cases that the amplitude clause quantifies over every constructible sheaf and every degree `q>c`, while the constructibility clause separately quantifies over all `q>=0`; `c` is required to be nonnegative and no properness or existence assertion is silently added. The source note's distinction was preserved: Tag 09AI motivates the comparison equivalence under a Noetherian coefficient ring, whereas FIN is a predicate assumed by the blueprint. Whole-DAG and whole-blueprint searches found no duplicate predicate. I ran the required LeanFinder, Loogle, grep, and LeanSearch searches with the item id: the first three returned only unrelated etale-topology/condensed declarations or no hits, and LeanSearch was unavailable; these results are recorded verbatim enough in the node. No Lean files were written, no compiler or Lake tools were run, and no live project files were changed.

Nothing remains unfinished.


## Second reading by NA

- Item coefficient/base paragraph: checked against blueprint order 1301 and def-weil-pbc-adic-coefficient-datum; retained finite P_n, torsion, perfection, Noetherian finite-dimensional T and invertibility; made n>=1 and scheme data explicit. No condition on S or properness was added.
- Item constructibility clause: checked def-weil-pbc-site-comparison-morphism, def-weil-pbc-proetale-modules, def-weil-pbc-constructible-complexes and def-weil-pbc-etale-constructible-sheaf; the essential-image definition is specified for either S or T with the existing finite stratification convention. PASS after explicit definition-node citations.
- Item FIN clause 1: checked the blueprint's every-F/every-q>=0 quantifiers and def-weil-pbc-proetale-operations plus def-weil-derived-cohomology-sheaves; defined R^q by cohomology of ordinary finite-coefficient Ru_* on F[0]. PASS after adding the missing notion dependencies.
- Item FIN clause 2: checked blueprint order 1301 against prop-weil-pbc-restriction-direct-image, statement [a,b+c] and proof vanishing p>c, and thm-weil-pbc-amplification-proper's specified bound 2e. FAIL in the import: existential c shadows the parameter; PASS after fixing c before the clauses and using that c in the vanishing clause.
- Source context: opened proetale.tex section-constructible (09AI), definition-constructible (09AJ) and lemma-compare-constructible (09AK), confirmed by tags/tags. The lemma assumes a Noetherian ring and any scheme, with affine-local constructibility. Our finite coefficient is Noetherian. The blueprint's finite global stratification on a possibly non-quasi-compact S is its explicit convention; no global/local equivalence on arbitrary S is asserted. Removed the comparison-equivalence assertion from the definition and retained it as source context here, so it creates no hidden theorem obligation.
- Proof steps: none; this item defines a conjunction and makes no finiteness or existence assertion. Empty proof/proof_deps and citations.json=[] are correct; C1-C4 and E1/E5 introduce no proof obligations.
- New nodes: none; B1-B7 and duplicate/specialization checks are vacuous. Searched the whole DAG for 09AI and uniform-bound/FIN predicates; the existing higher-level amplification/tower definitions use FIN and do not duplicate it. Independent Mathlib searches used general pushforward/cohomological-dimension vocabulary; LeanFinder returned only underived pushforward tools, Loogle and grep returned no hits. No leaf matches this conjunction.
- Edge cases: F=0 makes its higher direct images zero; the universal quantifier still ranges over all F. Empty S has only zero input and satisfies every nonnegative bound; empty T forces S empty. The identity of a field scheme has zero positive direct images and admits c=0. c=1 permits degree 1 but requires degrees >=2 to vanish; c=0 requires all positive degrees to vanish. n=0 is outside the positive coefficient tower; n=1 and the zero quotient ring are allowed. No empty scheme was excluded by the dimension convention.

### STATEMENT-DISPUTED: shadowed amplitude bound

The imported definition binds c both as a parameter and existentially inside clause 2. Variable-binding check: its literal clause is `exists d>=0, forall F, forall q>d, R^q u_* F=0`, independent of the displayed parameter c. Consequently it does not supply the `p>c` vanishing used by the next blueprint proposition, nor its stated interval [a,b+c]. The faithful correction fixes c>=0 externally and requires vanishing above that c. An unspecified bound is separately `exists c>=0, FIN(u,Lambda;c)`. This repairs the source's intended bounded predicate rather than silently preserving the erroneous binding.

Changes: corrected the shadowed bound; introduced missing objects and positive n; defined constructibility for both schemes; added existing definition dependencies for schemes, Noetherian rings, dimension, etale constructibility, Ru_* and cohomology; corrected the Stacks tag/label context and removed a theorem assertion from the definition; recorded independent searches. No new nodes, no changed target declarations, no Lean edits or compiler runs. The first worker's sections are retained as requested; the bound and source-context findings above supersede its claim that nothing needed repair.
