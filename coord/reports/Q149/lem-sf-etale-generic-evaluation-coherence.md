# Stage-1 delivery: lem-sf-etale-generic-evaluation-coherence

## Files written

- `dag/nodes/sec-six-functors/lem-sf-etale-generic-evaluation-coherence.json`: statement, split; six explicit proof steps, no Mathlib match. The statement and its original statement dependencies are unchanged.
- `citations.json`: one verbatim statement quotation for every proof-step/node citation.
- `report.md`: this report.

## New nodes

None. The argument uses existing statements and elementary substitutions; no clause of the item has been moved to a new lemma.

## Attachments

None. Searched the slopmaster2 project under `WeilConjectures/` for the exact node id, generic evaluation/coherence, stratum Hom/mate, and evaluation/exchange. The matches concern underived open-immersion exchanges, other six-functor composition statements, or unrelated evaluations; none states this whole ordinary unbounded etale identity for arbitrary finite commutative coefficients. The archived upstream master is not used as completed-proof evidence. This worker wrote no Lean and invoked no compiler.

## Literature and searches

Read `literature/stacks-project/sites-cohomology.tex`, the internal-Hom section including equation-internal-hom (08J8), lemma-internal-hom (08J9), and the construction and K-flat/K-injective discussion around them. The cited identity of this item is an agent-written formal calculation, not a theorem attributed verbatim to Stacks. Read the current blueprint `main-20261015` statement and proof of `thm-weil-etale-geometric-biduality`, especially paragraph 4, the generic-fibre induction clause; this calculation supplies the evaluation compatibility required by its descendant `lem-sf-etale-generic-exchange-algclosed`. Read the chapter and unit records and retained their route.

Read the full statements of all six proof dependencies: `lem-sf-ringed-derived-closed-symmetric-monoidal`, `lem-sf-etale-generic-stratum-mate`, `def-kun-unbounded-exchange`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `lem-sf-etale-generic-immersion-projection`, and `lem-sfb-ringed-derived-monoidal-comparisons`. These statements give the particular maps and normalizations used below; no proof-internal construction is used as an unstated interface.

Retained the imported item's searches and read their recorded results. Ran five fresh logged searches with the required `msearch.py Q149 lem-sf-etale-generic-evaluation-coherence` command: LeanFinder with two formulations, Loogle for `"mate", "evaluation"`, LeanSearch for the evaluation/projection/adjunction statement, and Mathlib grep for `(internalHom.*baseChange|baseChange.*internalHom|exchange.*evaluation)`. All services answered; grep had no hits. The closed-adjunction hits give individual formal laws, and the rigid dual-mate hits require duals; they do not specialize in one line to this entire derived immersion statement. Read Mathlib `CategoryTheory/Monoidal/Closed/Basic.lean:82-120` and `CategoryTheory/Monoidal/Rigid/Basic.lean:580-608` to check those candidate signatures and their hypotheses. The signatures returned for sheaf and light-condensed statements concern other categories and have no exceptional counit comparison. The exact five fresh queries and their returned summaries/digests are appended to `mathlib_searches` and are in `searches.jsonl`.

Whole-DAG searches for evaluation/coherence, exceptional counit identity, tensor-Hom transposition, generic exchange and immersion projection were made before considering new facts. `tools/blueprint_refs.py search` found no blueprint node for evaluation coherence or exceptional counit identity; broader tensor-Hom and mate searches were also read. They exposed the existing generic infrastructure now cited. No new node was necessary.

## WANTED

None.

## Problems found and corrections

The imported item had no proof. Its statement is coherent and true with its stated counit and projection compatibility hypotheses; no STATEMENT-DISPUTED or statement weakening is needed. The word “mate” is expanded explicitly rather than used to assert the desired equality. The proof distinguishes the ordinary inverse/direct-image counit from the exceptional counit throughout. It introduces the actual test object C and its adjoint t, so that applying the normalization of theta to its own component yields evaluation rather than an arbitrary object isomorphism.

The chapter/unit records still mention excluded older literature, but this delivery cites and uses no SGA source. Their historical route metadata is not edited. The blueprint ancestry and same_as list are retained: no whole-blueprint match states this more specific identity. The two off-unit general infrastructure statements are declared in split_report.tool_uses, not in the maintainer-owned tool_uses field.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs.

## Review by Q149

I checked the item against the sources above and checked every proof citation against the cited node's statement, rather than against a theorem used somewhere in that node's proof. Step 1 uses the closed symmetric monoidal theorem for the unbounded ringed-site tensor-Hom bijection and its evaluation counit, then uses the stratum-mate statement's displayed formula with u equal to theta itself. Its inverse followed by u is the identity, which explains precisely why the resulting arrow is evaluation. The hypotheses are a finite commutative A, the chosen closed/open immersion factorization, and arbitrary ambient complexes; neither citation imposes boundedness or constructibility.

Step 2 uses only the defining transpose formula of def-kun-unbounded-exchange, with f=s, f'=s', g=g_X, g'=g_S. Its ordinary derived adjunctions and square isomorphism apply to these unbounded constant-A module categories. The displayed computation expands the counit, then uses naturality at u; this is a two-line substitution, not a new mate-coherence lemma. In particular it does not assume exchange is invertible. The citation quotation includes the definition's full explicit mate composite.

Step 3 uses naturality in the final variable of the closed adjunction and the natural tensor-pullback comparison. The other equality is the hypothesis defining beta as pulled-back evaluation. I verified the tensor comparison direction: m_U goes from U(qC) tensor UP to U(qC tensor P). Naturality at t then gives a map to UN, followed by a to N'. The intermediate source q'TC tensor UP and final target N' agree on both sides. No internal-Hom preservation theorem or perfectness hypothesis is silently used here.

Step 4 applies the same stratum-mate characterization on S' and X', now to the ordinary adjoint computed in steps 2 and 3. It produces exactly exceptional counit after F'(d') after the primed projection. Naturality of an adjunction moves the two maps of the Hom target inside its ordinary adjoint; this is part of its natural Hom bijection and introduces no extra geometric result.

Step 5 uses the precise cartesian compatibility clause of the immersion projection statement, and the general derived monoidal-comparisons statement for the monoidality of the inverse-image square/composition identification. I wrote its full equation, including chi, m_U and b, and checked its source TC tensor TFP and target F'U(qC tensor P). This avoids saying merely that the diagrams “transport”. Naturality of the assumed canonical transformation b at d changes F'(Ud) after b into b after T(Fd). This is a direct naturality substitution. The monoidal-comparisons node allows arbitrary ringed topoi and unbounded complexes; constant-A etale pullbacks are instances by the exact inverse-image and constant-ring identifications already named in the item. These two generic tools do not replace the unit's geometric biduality route.

Step 6 substitutes exactly the exceptional counit equality assumed in the item, with N=Rs^!M; its domain is TFN, not an ordinary-direct-image expression. Functoriality and step 1 leave precisely pulled-back evaluation. Injectivity of the cited tensor-Hom bijection proves equality with beta under the stipulated b_P identification. I checked that the proof never inverts e, a or beta. Empty strata, zero P and zero M give the same zero maps; identity base change gives the usual evaluation formula. No noetherian, algebraic-closedness, invertibility-of-order, finite-Tor or constructibility hypothesis was added.

Against delivery-errors B--E: all delivered data is self-contained in the unchanged item statement and named definitions; there are no new unsplit nodes, missing new-node searches, proof sketches inside new statements, duplicate nodes, Mathlib leaves or new source tags to misidentify. Every non-elementary input is an existing cited statement. Elementary flags are reserved for the written counit/naturality substitutions of steps 2, 3, 5 and 6; the two applications of the stratum-Hom theorem are marked non-elementary. The proof is not a restatement of the conclusion and has no induction or hidden stratum theorem. No step is over 2000 characters, and each displayed comparison is the explicitly assumed or cited one. Every citation quote was copied verbatim and locally checked against the current statement. The server review_split check passed before the full delivery dry run.

## Unfinished

None in the split. The cited existing unsplit infrastructure remains its own stage-1 work; it has not been copied or split here.
