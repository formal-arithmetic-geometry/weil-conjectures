# Q62 stage-1 delivery: lem-trf-dualizing-counit-transitivity

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-dualizing-counit-transitivity.json`: statement, now split into four steps. The statement and statement dependencies are unchanged. Mathlib supplies the categorical ingredients through existing nodes; the geometric identification and final cancellation are written in the item.
- `citations.json`: seven verbatim statement excerpts backing every proof-step citation.
- `report.md`: this report.

There are **0 new nodes and 0 new Mathlib leaves**. `searches.jsonl` retains the five actual searches made with msearch.py; their precise queries and results were appended to the item's existing searches, preserving the inherited searches.

## Attachments

None. I searched all of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag, structural/dualizing counit terminology and dualizing composition. I read the relevant `TraceFormula/Defs.lean` package and `TraceFormula/ProperPushforward.lean`; the package's dualizing comparison data and its statements about trace-class pushforward do not supply a declaration of this exact counit identity for the specified conjugate comparison. A package field or a later trace-class theorem is not an attachment.

## WANTED

None. The current blueprint companion proof and the needed categorical sources are available locally.

## Problems found and corrected

The item had no proof. Its source suppresses the compact-support composition comparison when asserting that the structural counit is pasted. The statement already makes the normalization and the precomposition explicit, and is correct. The proof now names both independently specified structural and composite adjunctions, identifies the inverse right-adjoint comparison using conjugation, and displays the counit identity and the cancellation. This avoids identifying arbitrarily chosen isomorphisms of dualizing objects with the adjunction-compatible one.

The source points to `fix-prop-adjunctions` item 3. That node's exceptional clause still carries the stronger ambient-admissibility hypothesis of its item 2. I did not invoke that clause under the weaker, actual trace-formula constructible datum. Instead I used the existing general categorical nodes on the specified constructible adjunctions; the item itself and `def-trf-admissibility` already specify their conjugate composition normalization. No route or hypothesis is changed, and no ambient exceptional adjoint is needed.

## Unfinished work

None for this one-level stage-1 split. No Lean file was written, compiled or built. No repository or live launcher file was modified; only the designated sandbox was written. The deliver.py tool packages the permitted delivery in its own worktree.

## Not duplicates

No new nodes were created. Whole-DAG and whole-blueprint searches included counits, structural counits, pasted counits, dualizing counits and counit transitivity; `tools/blueprint_refs.py ancestor` confirmed `lem-trf-trace-source-exchange` as the blueprint ancestor. The potentially related `lem-pur-composite-integration-counit` concerns tensor-twist descriptions of the composite counit with invertible projection formulas, rather than the comparison between an independently specified structural adjunction and its composite. `fix-prop-adjunctions` has a stronger exceptional hypothesis as explained above. Neither requires changing `blueprint.same_as` from the searched value `[]`. All general-purpose ingredients here already have nodes.

## Review by Q62

I read the chapter record `sec-trace-formula`, the full unit record `sk-p-proper`, and the current `main-20261015` companion proof of `lem-trf-trace-source-exchange`, in particular Step 3's equation epsilon_aY Ra_Y! tau_f = epsilon_aX. The split implements that sentence in the unit's kernel-evaluation argument and leaves the chapter and unit records unchanged. I also read the current companion proof of `thm-trf-dualizing-complex-composition`, which constructs the comparison by right adjunction and evaluates at A_s. No new node needs a separate source review.

For Step 1 I opened the complete current statements of `def-trf-admissibility`, `def-trf-dualizing-complex` and `thm-trf-dualizing-complex-composition`. The first supplies exactly the three specified adjunctions on D^b_ctf(-,A) and says exceptional composition is conjugate to compact-support composition. The second identifies both dualizing objects with structural upper shriek of A_s. The third supplies the canonical dualizing isomorphism; its normalization is specified by the item and the admissibility definition, not inferred merely from existence of an isomorphism. The coefficient ring is the same A_{E,n} throughout, X and Y are separated finite type, and their structure maps have the specified constructible adjunctions by hypothesis. A_s is the constant free rank-one complex, with constructible cohomology and Tor amplitude [0,0]; it is an allowed input for these structural adjunctions. No smoothness, site-perfectness or properness over s enters this argument.

For Step 2 I read `def-weil-pbc-composite-adjunction` in full and checked its F,G,H,I substitution to obtain ML left adjoint to RS and e_N = epsilon_aY,N M(epsilon_f,SN). I read Stacks `categories.tex`, Tag 0DV0, label `lemma-compose-counits`, including its proof by composing the two Hom bijections, and checked Mathlib `CategoryTheory/Adjunction/Basic.lean:567–581`, especially `comp_counit_app` at line 580. The cited node explicitly states the pasted formula; no claim is taken from its proof alone.

For Step 3 I read the statements of `def-weil-pbc-adjunction-conjugate` and `def-weil-pbc-adjunction-mate` in full, and re-read the composition-normalization paragraph of `def-trf-admissibility`. The conjugate node explicitly states preservation of isomorphisms and the inverse formula, so conjugating alpha gives the inverse of the comparison obtained by conjugating alpha^{-1}. The mate node explicitly states its transpose characterization, giving exactly e_N ML(j_N) = epsilon_aX,N alpha_{TN} when both vertical functors are identity. I checked the direction with Stacks Tag 0B65, label `lemma-transformation-between-functors-and-adjoints`, and read Mathlib `CategoryTheory/Adjunction/Mates.lean:260–295`, including `conjugateEquiv_counit` at line 285. Thus the non-elementary compatibility is actually in the cited statement and not hidden behind the word 'transport'. No new categorical lemma is needed.

Step 4 is elementary substitution, functoriality and cancellation, all written in the displayed four-line calculation. I checked its source and target: alpha^{-1}_{omega_X} starts at H omega_X, then ML(i_f) ends at MLRS A_s, then e_A_s ends at A_s. This is exactly the comparison direction required in the conclusion. The given definition of tau_f supplies the first equality; the preceding steps supply the middle equality. Properness of f is needed only for the notation Rf_* = Rf_! already in the item; the proof keeps Rf_! throughout. There is no hidden appeal to a statement about a proper structure map.

I checked edge cases including f = identity without treating the chosen identity counit as literally the identity, X empty, and f = identity on the nonproper scheme A^1_k. The formula requires neither properness of a_X nor invertibility of an individual counit. As a normalization check, let all functors be the identity on vector spaces over F_3 and let their counits be multiplication by nonzero scalars a (L), b (M), c (H), with alpha multiplication by d. Then e = ab, j = cd/(ab), tau = cd/b, and b tau d^{-1} = c, exactly the asserted formula including alpha^{-1}. Omitting the comparison or choosing an arbitrary j would fail this check. For n > 1 the proof remains valid because it uses no field property of A, tensor duality or purity theorem.

I checked delivery-errors B–E against the actual node statements and sources: no new statement-only obligations or definition notions are introduced; every non-elementary dependency is cited and quoted verbatim; no proof is replaced by its own clause as a child; no source proof is cited as if it were a node statement; no off-route theorem or SGA source is used. The new proof dependencies are precisely the union of the step uses. All four proof steps are below 2000 characters, so no long step hides a comparison lemma. The comparison is already the existing Mathlib mate/conjugate interface, explicitly applied here.

The five Mathlib searches were read, including the second LeanFinder phrasing that returned `conjugateEquiv_counit` and `comp_counit_app`. Their source types match the formal ingredients represented by the existing mate/composite nodes. The geometric item still records the correct specified comparison, dualizing-object input and final cancellation as a split. I retained all inherited searches rather than claiming to have run them myself.
