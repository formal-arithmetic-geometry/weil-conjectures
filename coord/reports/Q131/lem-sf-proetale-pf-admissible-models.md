# Q131: lem-sf-proetale-pf-admissible-models

## Files written

- dag/nodes/sec-six-functors/lem-sf-proetale-pf-admissible-models.json: existing statement, now split into seven assembly steps; no Mathlib match for the complete item.
- citations.json: a verbatim statement quotation for each cited node at each step.
- searches.jsonl: actual msearch results, preserved as recorded by the search command.

No new nodes, no new Mathlib leaves, and no Lean files. The remaining sandbox prepare.py is only the local JSON-writing script.

## Attachments

None. Searched WeilConjectures for the item id, admissible-model terminology, Tor amplitude and flat representatives. Existing flat-model declarations cover parts, not all clauses of this item; none is proposed as an attachment.

## WANTED

None: the relevant Stacks source files and blueprint paragraph are present locally.

## Corrections and dependency audit

The mathematical statement is retained. Its extension-by-zero definition citation was wrong: def-weil-extension-by-zero defines the pro-etale functor, whereas the item's model is on the etale site. Replaced it in the statement and stmt_deps by def-weil-pbc-extension-by-zero. This changes the reference to the correct definition, not the intended functor or assertion. Exactness is taken from lem-weil-pbc-extension-by-zero-exact, not from a definition.

The former empty proof is replaced by an argument; the old Mathlib searches remain. New searches are exactly those in searches.jsonl. The interrupted LeanFinder request finished and its logged eight hits were read before continuing; there was no need to repeat that query. Both semantic phrasings returned etale algebra/morphism facts, not the derived-site assertion. LeanSearch also found DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE, which covers the bounded-representative substep alone. It does not establish constructible origin, flatness, Tor transport or comparison admissibility. Loogle and the site/flat grep returned no hits. Thus the complete item is not a Mathlib leaf.

## Blueprint and route

Read the chapter record sec-six-functors, the unit sk-thm-sf-pf-proetale and the current main-20261015 proof of thm-sf-pf-proetale. This item makes the input choices and bounded-below domain checks underlying that proof's finite-coefficient transport paragraph explicit. It changes neither the chapter nor the unit route. Its nearest ancestor is thm-sf-pf-proetale; the existing precise from.place is retained. Whole-blueprint searches for '08G1' and 'admissible models' found no imported duplicate of the combined assertion. DAG searches by tags 08G1/09AL and flat/K-flat/origin keywords found the generic facts cited below, so no new nodes were created. Off-unit generic tools are declared in split_report.tool_uses.

## Not duplicates

No new nodes. In particular the existing general ringed-site flat model and K-flat pullback nodes are reused rather than recreated as etale specializations.

## Review by Q131

I read Stacks sites-cohomology.tex lemma-tor-amplitude (08G1), lemma-bounded-flat-K-flat (06YQ), lemma-pullback-K-flat (0G7E), lemma-derived-base-change (06YY), and definition-derived-tor with its preceding one-factor K-flat construction (06YU). I read homology.tex Tag 0118, section-truncations, including the canonical truncation formulas, and corrected my initial source-place reference (05RX is about filtered derived categories, not these formulas). I also read proetale.tex lemma-compare-constructible-derived (09AL) and lemma-morphism-comparison (099R), and sites-modules.tex lemma-extension-by-zero-exact (03DJ). These are the source facts for the item; the assembly is marked agent-written, because its simultaneous fixed-witness and interval formulation is an explicit refinement of the blueprint paragraph.

For step 1 I opened lem-sf-proetale-constructible-origin: clause (ii) explicitly asserts equivalence for intrinsic bounded constructible complexes, with precisely A_{E,n} coefficients. Essential surjectivity therefore supplies the witnesses. I opened lem-exc-comparison-tor-interval: its statement is an iff for each fixed interval, testing all module sheaves, and requires only a finite commutative ring and a bounded-below etale object. Bounded constructible origins satisfy the latter condition. Isomorphic objects have the same derived tensor cohomology, so the Tor tests apply through any specified witnesses. I do not replace supplied origins with specially chosen ones.

For step 2 I opened def-kun-truncations, whose statement gives the kernel/cokernel formulas and explicitly says good truncations retain cohomology in the indicated ranges. Applying both formulas constructs the bounded representative. The maps are quasi-isomorphisms because only already-zero cohomology is removed. This is a direct definition calculation and is elementary; no general module-only roof lemma is used for sheaves.

For step 3 I opened lem-sp-ringed-site-tor-flat-model and checked its (1)-(2) equivalence on any small ringed site, without point or constructibility assumptions. It supplies exactly a representative supported in [a,b]. I opened lem-weil-pbc-independent-bounded-flat-kflat: it requires only bounded-above flat terms and a site small in the coefficient universe; our finite interval and common larger universe satisfy these hypotheses. I deliberately make no constructibility claim about individual model terms: none is needed or supplied by 08G1.

For step 4 I opened both lem-weil-pbc-ringed-pullback-preserves-kflat and lem-weil-pbc-ringed-topoi-derived-pullback. The former explicitly supplies K-flatness and flat terms under ringed-topos pullback; the latter explicitly says the derived computation comparison is an isomorphism on every such complex. The morphism r_e with its constant coefficient map is a ringed-topos morphism, so no flatness of the scheme morphism is assumed. The zero terms remain zero by the module pullback formula. Its derived representation is obtained by applying Lr_e^* to the chosen model isomorphism.

For step 5 I opened the etale extension definition and exactness theorem. The theorem explicitly preserves quasi-isomorphisms when applied termwise. It gives the model j_!C of M_0 and the support bound because an additive functor sends zero to zero. The corrected definition citation now names this same etale functor.

For step 6 I opened def-kun-derived-tensor and def-pc-tensor-complex-sheaves. The first explicitly constructs derived tensor by resolving one factor and gives the signed symmetry allowing the K-flat factor to be on the right. Thus no assumption that C or j_!C is flat is hidden. The second gives exactly the direct-sum formula and differential used here. A summand can be nonzero only with i in [u,v] and h in [a,b], which proves the asserted total interval by adding inequalities. This is a definition calculation rather than a new derived tensor comparison lemma. Bounded complexes have no cohomology below their lowest term, so both inputs are bounded below.

For step 7 I opened def-weil-proper-morphism and def-weil-finite-type-morphism: proper includes finite type and separated, and finite type includes quasi-compact. I opened lem-pc-separated-quasi-separated, which explicitly supplies quasi-compactness of the diagonal for separated morphisms. Finally I opened prop-weil-pbc-comparison-direct-image, whose statement requires qcqs and a D+ etale input, precisely the conditions just verified for M_0 and Q_0. It is used only for the admissible domain, not any unproved cohomological bound on the direct images.

I checked the return categories B-E point by point: every object is introduced, no new node is a restatement of a clause, and every non-elementary step cites actual theorem statements rather than a source-only tag or another node's proof. Every cited statement was opened and is copied verbatim into citations.json; the step-specific use is explained above. Every proof step is under 2000 characters. There are no hidden long-step sublemmas. No SGA source is used.

Small cases checked: empty X or empty schemes allow zero complexes; K_0=0 and L_0=0 satisfy the construction; u=v yields the single cohomology sheaf; a=b is the flat single-degree case of 08G1; n=1 is a finite residue-field coefficient ring but the proof does not rely on field coefficients; arbitrary negative intervals add in the same way; the compactification morphism r need not be flat; and witnesses supplied in advance enter without change. These tests expose no statement dispute.

## Unfinished work

None at stage 1 of this item. The reused nodes retain their own existing status and proofs; they are not modified. No compiler, Lake or build command was run.

## Validation

The first required server dry run passed at 4c921904032. A subsequent final source-place check corrected the truncation reference to homology.tex Tag 0118; the final required dry run is repeated on that corrected content before push.
