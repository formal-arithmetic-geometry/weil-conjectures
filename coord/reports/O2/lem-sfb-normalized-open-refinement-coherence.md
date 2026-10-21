# Worker report

Item: lem-sfb-normalized-open-refinement-coherence. Group: O2. Date: 2026-10-21.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normalized-open-refinement-coherence.json: statement, split; seven proof steps; no Mathlib match for the full statement.
- citations.json: one verbatim statement excerpt for every cited node in every proof step.
- report.md: this report. searches.jsonl is the unaltered search-command log; prepare.py is sandbox-only preparation code.

No new nodes and no new Mathlib leaves. No unit or chapter file changed: this is a descendant of the key node, not the unit's statement.

## Attachments

None. Searched the live project's WeilConjectures source by the exact id/docstring tag and by normalized-open/refinement and lower-shriek terminology. Read the relevant unbounded open derived-adjunction definitions and the bounded-constructible refinement construction. The former supplies the adjunction only; the latter has field, finiteness and bounded-constructible restrictions and does not state all the present normalized coherence assertions. Neither is an attachment for this item. No Lean was written or compiled.

## WANTED

None. The current blueprint source and all cited node statements are present.

## Corrections and source route

The item's statement, assumptions, source and blueprint ancestry are unchanged. Its empty proof was replaced. Preserved the inherited searches and added the six actual searches from this sandbox log, including a second natural-language phrasing. LeanFinder returned adjunction Hom-bijection/naturality primitives, Loogle no hits, LeanSearch generic right-derived transformations and underived module pushforward transformations, and grep the adjunction API. Read Mathlib/CategoryTheory/Adjunction/Basic.lean lines 160-176 and 226-242: these primitives explain the elementary calculations but do not state the pro-etale module-object restriction/compositor coherence theorem in one specialization. The grep for extensionByZero/openImmersionLowerShriek/refinement coherence returned no hits. Every new search record uses the exact logged tool and query.

Read the current main-20261015 unit, det-sf-comp-coherence-cocycle.proof.md (Refinement isomorphisms), and det-sf-comp-coherence-refinement.proof.md (restriction to X, uniqueness, and identity/transitivity). The proof realizes the same adjunction-and-restriction route, expanding the source's assertion that both arrows restrict to the identity into its actual equations. The source's proper-base-change argument for invertibility is outside this item's assertion and is not used. proof_origin.by is agent, since the blueprint is agent-written and the expanded equations are my argument.

The unit record still points to an older chapter/snapshot; I read it and the current main unit source. This item's chapter and unit records were retained as required. No unit route is replaced.

## Not duplicates

No new nodes. The whole-DAG and blueprint searches found no second node with this complete statement. det-sf-comp-coherence-refinement has related uniqueness/transitivity clauses but requires proper maps between dense finite-type compactifications over a positive-characteristic field; it also asserts invertibility on a localizing subcategory. The present item allows arbitrary schemes and maps identical over the open and never asserts invertibility. det-sf-comp-coherence-cocycle compares proper-pushforward candidates, rather than these arrows. Thus neither is a statement-equivalent blueprint entry; same_as remains empty. lem-sfb-identity-open-derived-restriction and lem-sfb-module-derived-compositor-coherence provide the two existing coherence inputs and are cited, not recreated.

## Review by O2

I checked delivery-errors B-E against the actual seven steps and opened every cited node's statement. For the item I read the two current blueprint proofs named above and the unit source. There are no new nodes requiring separate sources, dependency searches or leaf classifications. All TeX is written with single backslashes in the decoded JSON. The proof uses the specified ordinary unbounded module categories and their coefficient transports throughout.

Step 1 uses def-sfb-open-closed-internal-hom-comparisons for the actual open derived adjunction by transport and lem-sfb-condensed-support-derived-localization for invertibility of that adjunction's open unit. The latter explicitly says ordinary unbounded derived supportModules and that the maps are the actual adjunction maps with canonical alpha transport; this matches the coefficient-linear open functor here. Its hypotheses are a commutative condensed ring and a quasi-compact open with a complementary closed immersion; each j, j', j'' has such a complement. Neither source adds Noetherian, finite-ring, constructibility or boundedness assumptions. I declared the support-calculus theorem as a generic off-unit tool in split_report.tool_uses. It supplies only the unit isomorphism, not the refinement argument.

Step 2 uses that derived adjunction definition and the statement of lem-sfb-identity-open-derived-restriction, which explicitly provides a natural isomorphism r_h on all ordinary unbounded objects under exactly hj'=j and inverse-open equality. I wrote the normalized Hom bijection and its inverse using the counit. The triangle identities and cancellation verify it is a bijection; this does not require full faithfulness of restriction on arbitrary objects.

Step 3 uses only that bijection and its inverse, so it is elementary. Substituting the identity gives the specified adjoint formula and the exact displayed normalization; injectivity gives uniqueness.

Step 4 uses the naturality expressly stated for r_h and the naturality of the actual units. Both arrows have source j!K and target Rh*j'!L. The displayed first transpose and the second transpose are both u:K to L. This checks naturality for arbitrary derived morphisms, rather than just representatives or isomorphisms. It is a few-line application of those given natural transformations and the previous bijection.

Step 5 uses the identity clause of lem-sfb-module-derived-compositor-coherence for R(1)_* and the identity clause of lem-sfb-identity-open-derived-restriction for r_1. These are the same canonical identity constraints specified in the item. Their substitutions give eta inverse times eta, so uniqueness proves precisely the claimed identity arrow.

Step 6 uses r_h's naturality at e_k, whose source is j'!K and target is Rk*j''!K. Its intermediate Hom bijection has target Rh*Rk*j''!K, so no unmentioned derived composition identification is hidden. I checked each subscript in the written equation: naturality converts r_h j*Rh*(e_k) into j'^*(e_k) r_h. Normalizing e_h leaves eta_j'; normalizing e_k then leaves the identity. This uses neither properness nor invertibility of e_h or e_k.

Step 7 uses the exact displayed composition equation in lem-sfb-identity-open-derived-restriction and the compositor of lem-sfb-module-derived-compositor-coherence, both read in their statements. The inverse-open condition for hk is computed explicitly before applying the normalized equation for hk. This gives the same identity under the same injective map T as step 6, proving the equality with kappa in the direction written in the item. The canonical associators are those already specified in the compositor statement.

I checked empty U, zero K, zero coefficient ring, identity h or k, j the identity open, and arbitrary unbounded K. The argument is entirely functorial and is valid in these cases; for j=identity the inverse-open condition forces j' to identify all of Z', so the restriction formulas remain correctly typed. No step infers that e is invertible. No non-elementary step exceeds 2000 characters. No node merely restates a clause, no unsupported geometric claim is used, and no source from SGA is cited. citations.json records exact statement excerpts rather than substitutes for the mathematical audit above.

## Unfinished work

None in this one-level split. Existing cited nodes are reused with their current statuses; proving them further is outside this item. Server dry run and delivery are recorded below when complete.
