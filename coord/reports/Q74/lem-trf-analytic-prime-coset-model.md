## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-analytic-prime-coset-model.json`: item split, original statement unchanged, seven proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-immediate-minpoly-coefficient-preparation.json`: statement-only supporting lemma; no Mathlib match. It prepares the coefficients and approximation radius of the original minimal polynomial, not a coset or the conclusion of the item.
- `dag/nodes/sec-trace-formula/lem-trf-complete-ultrametric-simple-root-lifting.json`: statement-only supporting lemma; no Mathlib match for arbitrary complete real-valued nonarchimedean fields.
- `citations.json`: verbatim full statements for every node citation, keyed by proof-step number.

Attachments: none. Searched the project under `lean/WeilConjectures/` for the item's blueprint tag, special/critical cosets, immediate prime-degree extensions and the proposed auxiliary notions. No declaration states the complete item or either auxiliary statement. No Lean was written or compiler invoked.

WANTED: Michael Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3, Lemma 6.1.2 and Proposition 6.1.4, printed pp. 37--41, for lem-trf-analytic-prime-coset-model and its two new nodes. The source path named by the inherited item is absent from this machine's literature directory and not listed in LIST.md. Read the cited version at https://arxiv.org/pdf/0707.3953v3 (PDF pages 36--41); no download or change to literature was made. The proof origin is consequently marked agent, as the brief requires for a missing local document.

Issues found: the seed statement is sound. Its references to Proposition 6.1.4 and Lemma 6.1.2 are accurate. The proof cannot simply invoke Proposition 6.1.4 as a new node: that would move essentially the whole item. Instead the only deep preparation node ends at coefficient estimates for the original minimal polynomial. The coset construction, nonattained infimum, normalization, all representatives and exact root calculation are carried by the item's steps. Completeness is metric completeness; neither discreteness nor maximal-ideal-adic completeness is silently assumed. The normalization uses the algebraically closed residue field and divisible value group to produce the (p-1)st root inside K.

Nothing mathematical left unfinished in the item's assembly. The two new supporting statements remain unsplit by design. Delivery checks are recorded below.

## Not duplicates

lem-trf-immediate-minpoly-coefficient-preparation vs lem-trf-immediate-prime-polynomial-obstruction: the existing node only gives an unrestricted nonattained polynomial infimum and |pb|<s; it does not give an element of the specified L, its minimal polynomial, the coefficient bounds, or the linear coefficient alternative. The new node gives coefficient preparation and no coset conclusion.

lem-trf-immediate-minpoly-coefficient-preparation vs lem-trf-analytic-critical-polynomial-minimum: that node is an attainment theorem over tame type-2/type-3 rational analytic fields; the new node concerns an immediate degree-p extension and nonattained distances.

lem-trf-immediate-minpoly-coefficient-preparation vs lem-trf-analytic-prime-coset-model: the new node says nothing about S, special cosets, splitting, normalization to a=1, all representatives, or exact roots. It isolates the derivative/translation estimates that the proof uses to discard intermediate coefficients.

lem-trf-immediate-minpoly-coefficient-preparation vs lem-trf-spectral-norm-algebraic-extension: the existing Mathlib leaf constructs the extending norm and describes it by spectral coefficient bounds; it provides none of the approximation-radius preparation inequalities.

lem-trf-complete-ultrametric-simple-root-lifting vs lem-per-henselian-simple-root-stability: the existing node assumes the valuation ring is henselian and starts with an actual simple root to establish stability under perturbing coefficients. The new node derives a root from a simple residue root using metric completeness, without assuming henselianity.

lem-trf-complete-ultrametric-simple-root-lifting vs def-weil-pbc-henselian-terminology: the latter defines henselian pairs by lifting idempotents; it does not prove that the nondiscrete valuation ring of a complete real-valued field lifts polynomial roots.

Whole-DAG searches covered special/critical cosets, immediate degree, Proposition 6.1.4, Lemma 6.1.2, approximation radius, translated generators, higher coefficients, simple roots and Newton/Hensel lifting. Blueprint searches used `tools/blueprint_refs.py` with coset, immediate, Hensel, minimal polynomial, simple root, simple, Newton and coefficient. No blueprint node states either new lemma. The nearest blueprint ancestor was checked with `ancestor`. Read latest blueprint `sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`, and the chapter/unit records. The extended Temkin branch is inherited ancestry; no change of the unit route is made.

## Mathlib search results read

All new-node searches ran through the mandated msearch command, recorded in searches.jsonl. For the preparation lemma, two semantic phrasings returned ordinary minimal-polynomial facts, purely inseparable normal forms, unrelated number-field primitive elements, and the spectralNorm constant-coefficient identity. Read the latter at Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean:991--1004; it does not give the preparation. Grep of RingTheory/Valuation and Analysis/Normed found no immediate-extension coefficient preparation. The Loogle NormedField/Polynomial.IsRoot hits only concern eventual nonroots in ordered fields.

For simple-root lifting, both semantic phrasings and LeanSearch found `hensels_lemma`, `Field.henselian`, `HenselianLocalRing.is_henselian`, and `IsAdicComplete.henselianRing`. Read Mathlib/NumberTheory/Padics/Hensel.lean:462 and RingTheory/Henselian.lean:108--114 and the adic-completeness instance. The first is only over p-adic integers, the second treats a field as its own local ring, and the last two require exactly the henselian/adic structure not supplied by metric completeness of a dense-valued field. None is a one-line specialization to the node. Loogle `IsHenselianRing` returned an unknown identifier (zero hits), so the final node uses the successful `HenselianLocalRing.is_henselian` query instead. Unused exploratory searches are retained honestly in the log.

## Review by Q74

I checked the item against Temkin's Proposition 6.1.4(i)--(iii), its proof on printed pp. 39--41, and the definition and critical-coset calculation preceding Lemma 6.1.2. I read the minimal-polynomial shrinking argument for the preparation node and the simple-residue-root Hensel argument for the lifting node. Both new nodes introduce their own fields, absolute values, polynomials and hypotheses. Neither contains a proof. Every use of a definition refers to its actual definition statement: field, valuation ring and polynomial ring nodes were opened. Residue field, value group, minimal polynomial, degree and derivative are defined inline where needed.

Step 1 cites only the new preparation statement. Its hypotheses are precisely complete K and L, compatible absolute values, positive residue characteristic, immediate residue/value-group extension and degree p, all provided by the item. The quoted statement explicitly supplies theta, r, R, f, the strict higher-coefficient estimates, and the extra estimate if the linear term is discarded. It therefore supplies every non-elementary fact this step takes. Discarding terms is just a finite ultrametric sum.

Step 2 uses those established identities; on |c|<=R the perturbation has norm below s while f(c) has norm above s, and outside this ball the leading term dominates. These two explicit cases justify the unrestricted nonattained infimum without any unquoted Krasner or Berkovich-disc assertion. Such inputs, when needed, belong in the later proof of the preparation lemma.

Step 3 checks the additive subgroup claim by the binomial expansion, including the p=2 sign correction. For inadmissible c the leading term dominates the linear term; a smaller-than-|b| value would contradict |pb|<s. This is the actual restricted-infimum argument, not an appeal to a definition of critical coset. It explicitly supplies the admissible parameter and error exhibiting splitting over L. Thus neither a subgroup theorem nor Lemma 6.1.2 is silently imported as an unsupported black box.

Step 4 cites the simple-root lifting statement. The monic polynomial X^(p-1)-u has integral coefficients, an integral residue-root lift, norm-small value and unit derivative: p-1 is prime to p. Divisibility gives q of the exact required norm. Algebraic closedness gives a nonzero residue root. The lifted root remains a unit because it is within norm <1 of a unit; hence t has norm r. This last observation is also implicit in t^(p-1)=A, and was checked explicitly.

Step 5 writes both substitutions and both inequalities. Since |t|^p=s, division scales the infimum to one and preserves zero membership over both fields. No tame extension or descent lemma is used. Step 6 writes the formula for each representative, proves its |pv| bound, uses the already-established subgroup identity, and rules out an inadmissible parameter lowering the infimum. The same subgroup identity over L supplies an approximation with the strict |p alpha^p| bound needed in the next step.

Step 7 cites simple-root lifting again, now over complete L. I checked all coefficients of the translated monic polynomial, separating |alpha|>=1 and |alpha|<1, and proved its derivative has norm one. The resulting exact root is outside K by the infimum established in step 6. The final degree argument can also be checked directly by taking bases of L over K(beta) and K(beta) over K: their pairwise products form a K-basis, so their cardinalities multiply. Since beta is outside K and p is prime, the relative degree is p and K(beta)=L. No primitive-element theorem or separability assumption is added.

Small-case checks: at p=2 there are no higher coefficients and the normalization exponent is one; the subgroup's negation error is exactly 2c^2, which satisfies the given strict bound. In characteristic p the binomial errors and every |p x| are zero; an inseparable degree-p extension has polynomial T^p+b and a_1=0, so the preparation and truncation retain the expected purely inseparable model. In mixed characteristic the inequality |p|R^p<r^p is essential and retained. A trivial extension cannot meet [L:K]=p. For simple-root lifting a zero polynomial cannot satisfy |H'|=1; a linear monic polynomial satisfies the conclusion directly, including p=2 normalization. I found no counterexample or need to change the item statement.

I checked B--E of delivery-errors against the resulting nodes: statements are self-contained, new nodes are genuinely supporting statements rather than restatements, all non-elementary citations have matching verbatim quotations, no citation relies on another node's proof, no duplicate is introduced, and no statement dependency creates a cycle. All proof steps are shorter than 2000 characters. No SGA source is used.

## Delivery validation

The first server dry run exited 0: preflight passed, OK (not pushed), commit 4a5e5298a5e. Before the final dry run I expanded the last step to include the elementary basis proof of the degree formula, so that the item itself carries this argument rather than relying on the report. The final dry run and push are run sequentially, waiting for each process to exit.
