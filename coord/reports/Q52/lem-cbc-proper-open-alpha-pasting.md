# Q52: lem-cbc-proper-open-alpha-pasting

## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-proper-open-alpha-pasting.json: existing statement split into seven proof steps; no new nodes, no Mathlib leaves.
- citations.json: 21 entries, each quote checked literally against the current cited statement.
- searches.jsonl: actual search-command output records; the inherited item's Q65 searches are retained in its node.

## Attachments

None. Searched WeilConjectures by the exact blueprint tag and by proper-open alpha/pasting terminology. Existing finite étale proper/open composition and pro-étale open/clopen APIs do not assert all three arbitrary-B strict-tower alpha identities. StrictTowerProperOpenArrows.lean defines the actual alpha and beta but does not prove this item, and is under Sheaf rather than a finished upstream attachment.

## WANTED

None. All sources used are present.

## Corrections and scope

The statement is unchanged. The original item had no proof. Its source cites Stacks 0F7C, 0F7D and 0F7F, whose literal assertions concern étale proper/open gamma maps. I read their proofs, but did not apply these assertions as a theorem about arbitrary constant pro-étale B-modules. The split is explicitly agent-written: it proves the underived alpha refinement by restriction, then uses exact localization. It follows the existing parent route and the final compatibility sentence in the current main-20261015 thm-cbc-complete-proetale proof.

The general ringed open/closed exact-sequence statement already supplies the only extra detection fact required. There is consequently no new detection node: the image argument is written out in step 1. Likewise I create no nodes restating the three clauses. The ordinary normalization formula (N) is explicitly derived from beta's adjunction transpose and the existing clopen projector.

The search for a prospective detection node was run before discovering that its proof is elementary from an existing node; those real searches remain recorded rather than being discarded. Loogle query `SheafOfModules, Mono` reported an unknown identifier, so it is explicitly marked invalid, not evidence of absence. The later fully qualified query ran successfully. The second semantic phrasing and the sheaf-monomorphism hits were read: none states the full item. No Mathlib source was searched outside msearch.py.

## Not duplicates

No new nodes. Reused lem-cbc-proper-open-clopen-projector for the already separated clopen normalization. Finite étale lem-cbc-proper-open-interchange-coherence and the proper-map-fixing-an-open blueprint lem-weil-pbc-proper-open-comparison-composition have different coefficient categories and do not prove this arbitrary-B statement. Searched the whole imported blueprint with clopen, clopen component, extension by zero, restriction detects, alpha, proper-open and 0F7C, and inspected the matching DAG statements. No blueprint node states the full item, so its same_as remains [].

## Review by Q52

I read Stacks more-etale.tex, lemma-shriek-proper-and-open and the complete proofs of lemma-shriek-proper-and-open-compose (0F7C), lemma-shriek-proper-and-open-compose-horizontal (0F7D), and lemma-shriek-proper-and-open-base-change (0F7F). I also read proetale.tex lemma-open-immersion (09BN), lemma-ses-associated-to-open (09AH), and its j_! to j_* consequence, and the current blueprint thm-cbc-complete-proetale.proof.md. There are no new-node sources to review. I read the full statements of each of the six nodes used below and checked their dependency reach does not contain this item.

Step 1 uses lem-weil-pbc-proetale-ringed-open-closed for exactness, the complementary closed restriction's vanishing on j_!, and the short exact sequence for the image I. This really is a ringed pro-étale statement for arbitrary ring sheaves, so specialization to the constant B sheaf meets its hypotheses. Exact restriction kills I both on the open and on the closed complement, hence the sequence kills I. This is sheaf-level detection, not a false assertion that evaluation is faithful in the derived category. The two operation definitions fix which restrictions and extensions are meant. The opens used in the original squares are quasi-compact; the outer and pulled-back ones are composites or base changes of these.

Step 2 uses the proper/open-arrow definition's actual beta inverse transpose, the operation definition's normalized square comparison, and the open-extension definition's unit-preserving adjunction. I wrote and inverted the transpose equation, tracking the particular unit; mere invertibility of some comparison would not suffice. The derived arrow definition explicitly starts with termwise module operations, so this is its underlying module formula, not a finite-coefficient substitution.

Step 3 takes from lem-cbc-proper-open-clopen-projector exactly its identification of the intrinsic pi and alpha and its equation G_s pi_s=1. I checked the properness of both verticals and quasi-compactness of both horizontal opens against that node's statement. Combining it with step 2 yields the explicit restriction (N). This step does not assume the target theorem's pasting laws. The operations fix all compositors, and the open extension's unit is the normalization in the displayed formula.

Step 4 uses only (N), already proved, naturality, and the specified inverse-image/open units of the two operation definitions. I checked the source is P_p1 P_p2 L_i2 M and the target is L_k P_r1 P_r2 M. Restriction changes the first alpha factor to P_r1 P_i1 alpha_Q2, so (N) applies to Q2, and then (N) applies to Q1. The two square relations concatenate to precisely the outer relation. Detection from step 1 concludes equality of the original sheaf maps, rather than only their restrictions.

Step 5 restricts by P_k P_l, not by P_l alone. Q2 is evaluated at L_i M; after its restriction the input for Q1 is exactly P_k P_p L_i M. The unit-preserving open compositor in the open-extension definition identifies successive open units with the outer one. Both results land in P_r M. Detection applies to the composite open lk. Thus no hidden comparison lemma or node restating the horizontal clause is used.

Step 6 checks the two cube paths on their common target L_k1 P_r1 P_c M. I checked ak1=kd, rd=cr1, hp1=pa, and p1k1=i1r1, including their pullback functor directions. On the left (N) for Q is pulled back by P_d, and beta_k cancels by step 2. On the right beta_i cancels by step 2 and then (N) for Q1 applies. The written chain of scheme-map identities checks that theta is the same canonical starting identification. This uses the operation definitions' actual square/compositor data, not a freely chosen isomorphism, and requires no proper base-change isomorphism or torsion condition.

Step 7 uses lem-sp-exact-derived-transformation-pasting exactly for equalities between finite composites/whiskerings of exact functors with their derived compositors. Its statement explicitly covers unbounded categories and noninvertible cells. Natural sheaf maps commute with tower transition maps and complex differentials; hence their sheaf equalities are actual tower/complex equalities. The operation and arrow definitions specify exact descent and induced units, and the clopen-projector statement explicitly identifies its ordinary and derived projections. These ensure the localized cells are the intrinsic maps in the statement. I did not infer equality from evaluation. The two generic off-unit tools are declared in split_report.tool_uses with their roles.

I tested B=0, zero modules, empty source opens, identity open or vertical maps, cartesian squares (s=1), and a disjoint extra component in W_S. Detection reduces to I=0 also for the empty open. In a cartesian square (N) reduces to beta normalization; disjoint extra components are discarded by pi, while restriction to the retained component remains identity. An empty V gives zero target on both sides, including if the outer comparison's other pullback has extra components. No noetherian, constructible, torsion, finite-ring, boundedness, cartesian-original-square or evaluation-faithfulness assumption was introduced. Every step is shorter than 2000 characters; the calculations contain no unextracted non-elementary subclaim. The six cited statements cover the non-elementary tools. There are no statement disputes or unfinished mathematical clauses.

## Unfinished work

None for this one-level split. The existing unsplit clopen-projector dependency remains its own item; no proof of that node is being claimed here.
