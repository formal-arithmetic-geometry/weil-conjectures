# Stage-1 worker report

1. Files written: dag/nodes/sec-proper-base-change/lem-weil-pbc-derived-sections-pushforward.json (statement, split; not a Mathlib leaf); citations.json; this report. No new nodes and no new Mathlib leaves. searches.jsonl is the search command's audit log.
2. Attachments: none. Searched the slopmaster2 project for the exact blueprint tag, derived sections and pushforward, and read Comparison/LowerStarAcyclic.lean:160–200 and Etale/Derived/GlobalSections.lean:57–66. The first proves a vanishing implication for comparison pullback of a sheaf, not this natural isomorphism for arbitrary pro-etale bounded-below complexes. The second concerns a scheme morphism between two etale sites. Neither states the item. The generic composition construction in CategoryTheory/DerivedCategory/RightDerivedFunctor/Comp.lean is infrastructure, not an attachment to this specific statement. No upstream master sorry was treated as a proof.
3. WANTED: none.
4. The imported item has no mathematical statement error. Its proof was empty. I retained all hypotheses and its specified canonical comparison and supplied the missing argument. The etale-cohomology definition cited by the original statement explicitly discusses abelian coefficients; the new proof uses the existing generic K-injective bridge for left Lambda-module coefficients, without imposing commutativity on the finite ring. Added that definition to statement dependencies. No changes to the chapter, unit route, or unit realization were needed (this is not a unit key node).
5. Nothing left unfinished at this one-level split. Generic cited nodes retain their own existing open obligations.

## Review by NH

I read the chapter and unit records, the ancestor blueprint lem-weil-pbc-comparison-global-cohomology.md in full, and the injective-resolution argument it prescribes. I checked it against Stacks derived.tex:013K (lemma-injective-resolutions-exist), 070J (lemma-bounded-below-injectives-K-injective), 070I (lemma-K-injective), and 070Y/070K (computing right derived functors on K-injectives). For the category hypotheses I read injectives.tex:079H (theorem-injective-embedding-grothendieck) and 079Q (remark-existence-D); for injective preservation I read homology.tex:015Z (lemma-adjoint-preserve-injectives). The comparison formula is the opening construction of proetale.tex:099R and the existing comparison-morphism node, whose whole statement I opened. No external source is missing and there is no new node source to audit.

Step 1 uses the pro-etale-modules statement for its small skeleton and ring sheaf and the comparison-morphism statement for the fixed-ring module adjunction. The ring-sheaves-Grothendieck statement explicitly allows noncommutative rings, so its two site applications and its one-point-site module-category application meet its size and coefficient hypotheses. The enough-injectives statement supplies that property from Grothendieck abelianness. I replaced the tempting commutative-ringed-site resolution node with the existing generic bounded-below resolution-existence node: its statement gives a quasi-isomorphism from the actual complex J, not merely a resolution of a sheaf. The bounded-below-injectives node says precisely that the resulting complex is K-injective.

Step 2 uses exactly the exactness clause of the finite-level comparison proposition, not its separate unit or acyclicity conclusions. The comparison-morphism statement gives the adjunction in the needed direction. The right-adjoint-preserves-injectives statement then gives termwise injectivity of nu_*I, and the bounded-below-injectives statement applies because nu_* takes zero to zero. No higher-direct-image vanishing or preservation of quasi-isomorphisms by nu_* is assumed.

Step 3 uses the comparison-morphism formula for restriction, the generic K-injective bridge's formula RvK=v(I), and the K-injective-computes statement for independence and functoriality. Left exactness is verified directly from sectionwise kernels, and additivity from sectionwise group operations. The bridge's and computes lemma's Grothendieck hypotheses are all supplied in step 1; its bounded-below input condition holds for J and for nu_*I. Resolving nu_*I a second time is unnecessary precisely because step 2 proves it is already K-injective. This is the core reason the composite derived functor is computed by the same sections complex.

Step 4 takes only the explicit underived restriction formula from the comparison-morphism statement. T/T is terminal in both full site categories since its structure map is the unique arrow over T, and the inclusion is identity on underlying schemes and arrows. I wrote out the degreewise identity, its Lambda-linearity and compatibility with differentials. This is an elementary step, not an unproved derived-composition theorem.

Step 5 uses the comparison principle's actual bijection on homotopy-category Hom sets to replace roofs by maps into the K-injective representative; the computes statement gives canonical independence and functoriality. I checked that these statements really mention the required quasi-isomorphism and resolution comparisons. I wrote the naturality square at chain level and why additive functors preserve its homotopy equivalences. Thus the morphism is the prescribed derived evaluation comparison, not merely some isomorphism between its source and target. citations.json quotes every cited statement verbatim, including all clauses used; no citation takes a lemma from inside another node's proof.

I searched the whole DAG for resolution, injective preservation, composition and Grothendieck statements, and the blueprint for “derived sections”, “injective resolution”, and “global cohomology”. This found the generic nodes reused here and no duplicate exact blueprint statement. The item's blueprint ancestor and precise proof place were retained, and same_as remains empty. Generic tools outside this unit are declared in split_report.tool_uses; they implement the ancestor's prescribed resolution route and do not replace a unit step.

The Mathlib searches were run with msearch.py, including two semantic phrasings. I read the returned hits: degreewise right-derived functor operations, underived pushforward comparisons, and abstract localization infrastructure do not state this particular derived comparison. LeanSearch returned Internal Server Error and is recorded unavailable. No search was fabricated, and no new leaf is claimed.

For the B–E audit: no statement-only new nodes, duplicate nodes, moved conclusion, cycles, or new false auxiliary statements were introduced. Every non-elementary resolution and preservation fact is a cited existing statement; elementary kernel/evaluation/homotopy calculations are written out. The proof works for J=0, a sheaf in degree zero, arbitrary shifts of such a sheaf (including negative lower bounds), T empty, the zero coefficient ring, and a noncommutative finite ring such as M_2(F_2). These cases require neither bounded-above cohomology nor constructibility nor properness. I checked that none of those hypotheses was silently introduced.

## Not duplicates

No new nodes.

## Second reading by NH

I reread the item statement against the blueprint ancestor proof and the cited Stacks passages 013K, 070J, 070I, 070Y, 070K, 079H, 079Q, and 015Z. The hypotheses (scheme, finite possibly noncommutative ring, and bounded-below pro-etale complex) and the canonical evaluation comparison agree; zero complexes, degree-zero sheaves, empty schemes, and shifts introduce no excluded case.

Step 1 was checked against the statements of the pro-etale module definition, comparison morphism, Grothendieck ringed-site lemma, enough-injectives lemma, bounded-below resolution lemma, and bounded-below K-injective lemma. Each supplies the stated category or resolution fact; no proof-internal fact is used.

Step 2 was checked against the finite-level exactness proposition, comparison adjunction, right-adjoint-preserves-injectives lemma, and K-injective lemma. Exactness is applied in the correct direction and the pushed-forward complex remains bounded below.

Step 3 was checked against the comparison-morphism formula, K-injective bridge, and K-injective computation lemma. The left-exact/additive assertions are the stated sectionwise kernel calculation, and the representative used is the one supplied by those statements.

Step 4 was checked directly against the comparison-morphism direct-image formula and the terminal-object evaluation. The degreewise identity, Lambda-linearity, and differential compatibility are elementary.

Step 5 was checked against the K-injective comparison principle and K-injective computation lemma. Its roof replacement, homotopy invariance, and naturality argument use only their stated bijection and canonical resolution independence.

There are no new auxiliary nodes to audit under B1--B7, no duplicate or Mathlib leaf candidates, and the existing generic nodes were searched and reused. I corrected the node metadata so `created.item` names this delivered item rather than its blueprint ancestor; no mathematical statement or proof step required correction.
