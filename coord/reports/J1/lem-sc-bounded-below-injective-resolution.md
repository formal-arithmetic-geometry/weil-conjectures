Files written:

- `dag/nodes/sec-picard-framework/lem-sc-bounded-below-injective-resolution.json` — split statement; proof uses one existing ringed-space enough-injectives node, one new Mathlib leaf, and the existing bounded-below K-injective leaf.
- `dag/nodes/sec-picard-framework/lem-sc-bounded-below-injective-resolution-existence.json` — statement, Mathlib leaf (`CochainComplex.Plus.exists_quasiIso_injective`).
- `citations.json` — verbatim statement excerpts for every proof citation.

Attachments: none.

WANTED: `literature/stacks-project/sites-cohomology.tex`, Tag 07A5, because the local literature checkout contains citation metadata but not the source TeX.
WANTED: `literature/stacks-project/injectives.tex`, Tag 079P and Lemma 01DI, for the same reason.

## Review by J1

I checked the target node against its source description and the parenthetical Ext-vanishing use in the `thm-sc-p1-duality` blueprint ancestor. No sorry-free declaration in either project source tree carries the target under its full ringed-site hypotheses. The existing `lem-sc-ringed-space-module-sheaves-enough-injectives` statement explicitly supplies that `Mod(O_X)` is abelian and has enough injectives, which is exactly what step 1 takes from it. The new node is the generic bounded-below replacement statement; its Mathlib search was run with LeanFinder, Loogle, grep, and LeanSearch (the latter was unavailable), and the declaration and source lines were read. Its `CochainComplex.Plus.exists_quasiIso_injective` hypotheses specialize to the module category and the given bounded-below complex, yielding the quasi-isomorphism and injective terms used in step 2. Step 3 cites the existing Mathlib leaf `lem-weil-pbc-bounded-below-injectives-kinjective`, whose statement directly says that a bounded-below complex of injectives is K-injective. I verified each citation quote against the node file and checked the zero complex and a complex concentrated in one degree as edge cases. The split keeps the item conclusion in the item proof and does not create a node restating the ringed-site conclusion.

## Second reading by J1

- Item statement: checked against Stacks Tag 07A5 (`sites-cohomology-section-unbounded`) and Tag 079P (`injectives-theorem-K-injective-embedding-grothendieck`); the ringed-site, bounded-below, termwise-injective, quasi-isomorphism, and K-injective clauses agree. Zero complex and a one-object trivial-covering site satisfy the statement.
- Step 1: checked against the new ringed-site node, whose statement gives Grothendieck abelian, hence abelian with enough injectives; the cited statement supplies exactly the category hypotheses used.
- Step 2: checked against `CochainComplex.Plus.exists_quasiIso_injective` at Mathlib `DerivabilityStructureInjectives.lean:61-69`; its `Plus` strict lower-bound hypothesis and injective-object terms match the bounded-below complex used here. Tested on the zero complex and a complex concentrated in degree 0.
- Step 3: checked against `lem-weil-pbc-bounded-below-injectives-kinjective` and Mathlib `CochainComplex.isKInjective_of_injective` at `KInjective.lean:133-134`; its conclusion is exactly the K-injective clause.
- New node `lem-sc-ringed-site-module-sheaves-enough-injectives`: statement-only and self-contained with definition nodes; checked against Tags 07A5 and 079P, with TeX written once and no unrecorded proof dependency.
- New node `lem-sc-bounded-below-injective-resolution-existence`: exact Mathlib leaf; declaration, file, and lines were read, and grep, LeanFinder, Loogle, and unavailable LeanSearch runs are recorded in `searches.jsonl`.

Changes: added the missing ringed-site enough-injectives node because the worker cited the ringed-space-only 01DI node for a ringed-site target; redirected step 1 and its verbatim citation; recorded the source and edge-case checks. The existing target node is an origin copy and is not counted as a new node.

## Not duplicates

- `lem-sc-ringed-site-module-sheaves-enough-injectives` vs `lem-sc-bounded-below-injective-resolution` (079P): the new node only establishes that `Mod(O)` is Grothendieck abelian and has enough injectives; the item additionally constructs a bounded-below quasi-isomorphism and proves K-injectivity.
- `lem-sc-ringed-site-module-sheaves-enough-injectives` vs `lem-weil-derived-limit-existence` (079P): the new node is a category-theoretic hypothesis; the existing node computes derived inverse limits.
- `lem-sc-ringed-site-module-sheaves-enough-injectives` vs `prop-weil-pbc-rlim-functoriality` (079P): the new node supplies enough injectives; the existing node proves functoriality of derived limits.
- `lem-sc-ringed-site-module-sheaves-enough-injectives` vs `prop-weil-pbc-derived-inverse-limit-computation` (079P): the new node concerns the ambient category; the existing node identifies an inverse-limit computation.
- `lem-sc-ringed-site-module-sheaves-enough-injectives` vs `prop-pur-kinjective-resolutions-exist` (079P): the new node proves only the ambient enough-injectives fact; the existing node is a K-injective resolution existence result in its purity setting.
- `lem-sc-ringed-site-module-sheaves-enough-injectives` vs `def-pur-derived-internal-hom` (079P): the new node is an abelian-category property; the existing node defines derived internal Hom.
- `lem-sc-ringed-site-module-sheaves-enough-injectives` vs `prop-weil-pbc-kinjective-resolutions-exist` (079P): the new node supplies the category hypotheses; the existing node gives the bounded/unbounded resolution result used elsewhere.
- `lem-sc-ringed-site-module-sheaves-enough-injectives` vs `lem-weil-pbc-kinjective-functorial-existence` (079P): the new node establishes enough injectives; the existing node asserts a functorial K-injective construction.
- `lem-sc-ringed-site-module-sheaves-enough-injectives` vs `def-pur-kinjective-complex` (07A5): the new node establishes the ambient category; the existing node defines K-injectivity.
