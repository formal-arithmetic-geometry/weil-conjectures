## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-open-affine-cover.json`: statement, split into seven proof steps; not a Mathlib leaf. Statement and statement dependencies unchanged.
- `citations.json`: 21 literal statement quotations, one for every step/node citation.
- `searches.jsonl`: actual search-command log; the item searches and the exploratory gluing searches are preserved. `write_split.py` is a sandbox-only preparation script, not a delivered node.

No new nodes and no new Mathlib leaves. Every ingredient was found in the existing DAG.

## Attachments

None for the item. I searched the project source under `lean/WeilConjectures/` for the exact blueprint tag, finite locally free schematicity, quasi-affine algebraic-space covers, finite-flat-equivalence-global and 07S6; no project declaration states the item. Scheme morphism results and locally free module results do not imply this schematicity theorem. The existing `lem-pc-schemes-criterion` already records its closed project declaration and Mathlib counterpart; I cite that node without editing it.

## WANTED

None. All mathematical sources needed are present.

## Findings and changes

The imported item was unsplit and had no proof. Its statement is correct. I read Stacks spaces-properties.tex Tag 07S6, proposition-finite-flat-equivalence-global, the whole proposition proof and its following paragraph; the latter explicitly allows a locally closed subscheme of an affine scheme. I also read Properties Tag 01ZY, lemma-ample-finite-set-in-affine, including case (2), and its invitation to prove that case directly. The split writes that direct argument using the existing prime-avoidance and principal-open nodes. It does not invoke an ample sheaf on a possibly non-quasi-compact U: the DAG's definition of ample assumes quasi-compactness, so that would not justify the statement as given.

I retained the item source, statement, stmt_deps and all inherited metadata. The current blueprint `latest` direct-images proof (3), chapter record and unit record were read. The item is a supporting schematicity input along the recorded long alteration chain, not the unit's own statement; no unit fields were changed. `blueprint_refs.py ancestor` confirms that the inherited nearest ancestor is null. I retained that ancestry and its detailed place/via rather than inventing a replacement. Whole-DAG tag and concept searches and `blueprint_refs.py search` found no duplicate item. Searches for gluing found the existing `lem-pc-schemes-criterion`, so no gluing node was created. Searches for invariant affine neighbourhoods found the existing `lem-sfb-locally-free-groupoid-invariant-affine`, so no 03JE node was created.

Mathlib item searches were run with the required command: two semantic phrasings, LeanSearch, Loogle and source grep. Hits concern finite scheme morphisms, quasi-affine schemes and scheme open covers, not schematicity of an algebraic-space target. The exploratory gluing searches returned `Scheme.LocalRepresentability.isRepresentable`; I read its local source, including its Zariski locally-surjective hypothesis, then reused the existing 01JJ node. No unrun search is recorded as a new result.

## Not duplicates

No new-node/existing-node pairs: this delivery creates no nodes. In particular, the item is not the affine quotient theorem 03BM (its U need not be affine), not the invariant-neighbourhood theorem 03JE (its target is an algebraic space to be shown a scheme), and not the 01JJ gluing criterion (it must construct the representable open cover).

## Review by NL

I checked the actual node statements and the sources, rather than their titles. The item's proof follows 07S6 and retains its invariant-affine/affine-quotient/open-gluing route. The subsidiary source statements read were Groupoids 03JE (lemma-find-invariant-affine), Groupoids 03BM (proposition-finite-flat-equivalence), Spaces 02WU (lemma-finding-opens), Schemes 01JJ (lemma-glue-functors), Algebra 00DS (lemma-silly), and the base-change statement in spaces-topologies.tex lemma-fppf (03Y9). No SGA source is used.

Step 1 uses the algebraic-space definition only for scheme-test representability, the groupoid definition for its pointwise identities, and the finite-locally-free definition for flatness and local finite presentation. R is the pullback over X, not the product over S. Its groupoid maps are written explicitly as diagonal, exchange and composition of pairs; the diagonal sections prove the surjectivity needed later. Finite local freeness is obtained by applying the item's universal scheme-test hypothesis, not by citing an uncited stability theorem.

Step 2 uses `lem-sfb-space-fppf-covering-calculus` parts (2) and (4): its statement explicitly gives base change on point-surjective fppf families and comparison with scheme coverings. The singleton p has the required chart flatness and local finite presentation because it has them on every scheme test, and has point-class surjectivity by hypothesis. Thus T times_X U is a surjective fppf scheme cover. The quotient identification is proved by evaluating invariant maps on local lifts and gluing; `def-weil-pbc-sheafification` is used only for its actual universal property. I did not substitute the existing etale-atlas presentation theorem, which requires p to be etale and would not apply here.

Step 3 uses the finite-fibre clause of `def-pc-finite-locally-free`, the basis clause of `lem-weil-pbc-spec-localization-away-basic-open`, prime avoidance, and clause (0) of `lem-weil-pbc-affine-ideals-closed-subscheme`. The last node explicitly states affineness of a principal open as a scheme; the topological localization node alone would not say that. The orbit is nonempty because of the diagonal section, so the prime-avoidance node's r >= 1 hypothesis holds. J is not contained in any orbit prime because each prime has its own chosen basis element. The argument f in J proves D(f) is inside the union of those basis opens, so the resulting affine neighbourhood lies inside U. No finite cover of U or ample-sheaf hypothesis is used.

Step 4 applies exactly the existing 03JE statement: each orbit is already in an affine open. This gives an invariant affine W containing the orbit, with equality of the two inverse-image opens. That equality proves R_W = W times_X W = U times_X W, so its projections are scheme tests of p. The definition of finite morphism then supplies affineness of R_W over the affine W. This avoids assuming that arbitrary intersections of affine opens are affine.

Step 5 uses the full statement of `lem-a1-finite-flat-affine-relation-quotient`: both source and relation schemes are affine by step 4, both projections are finite locally free, and the kernel-pair relation is an equivalence on every test. The theorem supplies the affine S-quotient and its universal property, with the S-structure included in its statement. Nothing is borrowed from its proof.

Step 6 uses `lem-weil-pbc-open-immersion-etale` and `def-weil-etale-morphism` to verify the flat/l.f.p. hypothesis on W -> U, then the actual statement of `lem-trf-etale-relation-finding-opens`. Despite that node's name, its statement and source 02WU allow surjective flat locally finitely presented s,t; they do not require etaleness of the relation. All those hypotheses were checked in step 1. The restricted relation is the one in step 4, so the conclusion really gives the maps M_W -> X as representable open immersions.

Step 7 verifies the open-cover hypothesis of `lem-pc-schemes-criterion` on every T -> X. The fppf pullback P -> T is surjective, and the opens b^{-1}(W) cover P and map into the inverse images of the open scheme tests V_W. This proves the V_W cover T. Thus we have the Zariski coverage required by 01JJ, not merely local lifting for the fppf topology. Zariski sheafness follows from the actual fppf-sheaf algebraic-space definition and the open-immersion/etale definitions, since open covers are fppf covers. All objects and the set-indexed family fit the site's chosen universes. The criterion produces a scheme over S.

I tested U empty and the zero ambient ring: no orbit is chosen, surjectivity makes X empty, and empty gluing gives the empty scheme. For a nonempty point, the orbit contains it, so rank zero cannot occur there. Nilpotent basis elements cannot be the chosen element avoiding its point prime. Repeated or comparable orbit primes are allowed by prime avoidance. A non-quasi-compact union of principal opens is permitted throughout; only each finite orbit is reduced to one affine open. Nonreduced finite relations are allowed by 03JE and 03BM. There is no separatedness, Noetherian or finite-type assumption hidden in the application.

I checked B--E point by point: no new unsplit node carries a proof, no new notions or duplicated facts are introduced, TeX is single-escaped in the decoded statements, every non-elementary input is an existing cited node, all literal quotations occur in those statements, and proof_deps is exactly the union of uses. I also checked the transitive dependencies of the substantive reused nodes: none reaches the item, so no cycle is introduced. Every step is shorter than 1000 characters, below the long-step threshold. Off-unit generic scheme-theoretic tools are declared in split_report.tool_uses; they implement the item source's specified route rather than replace the unit's argument.

## Unfinished work

No mathematical part of the one-level split remains. The dependencies retain their own existing statuses; they were not re-split. Required server dry run and delivery are performed after this report is written.
