## Files written

- dag/nodes/sec-trace-formula/lem-trf-coproduct-scheme-pullback.json: split the item in five steps; no statement changes; no Mathlib match for the whole item.
- citations.json: one entry for each step/node citation, checked against the current statement verbatim.
- report.md: this report. searches.jsonl is the unmodified search-command log.

No new nodes; no new Mathlib leaves.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and for coproduct/sheaf/fppf/pullback notions. No declaration gives this arbitrary-family scheme-test comparison with all of its hypotheses and clauses. The scheme-only coproduct and pullback declarations do not suffice as an attachment.

## WANTED

None. All sources used are available locally.

## Issues found and repaired

The imported item had no proof. Stacks 02WQ calls the atlas verification straightforward without giving the test-scheme comparison; the split writes that comparison out. The statement itself is correct and unchanged. No algebraic-space, etaleness, or surjectivity assumption is introduced. The representing bijections for each V_i are hypotheses, not new existence assertions. The proof does not claim that evaluation preserves coproducts of sheaves.

Mathlib searches were run with msearch.py and recorded verbatim by tool/query, retaining the inherited searches. Two semantic phrasings returned structure-sheaf sections on scheme coproducts, scheme-only pullback squares and Zariski local-representability gluing. Read Limits.lean around lines 190--240, 436--450 and 480--497, BigZariski.lean around 110--125, and Sites/Representability.lean around 52--110. The structure-sheaf section isomorphism concerns rings of sections, and the pullback squares concern scheme coproduct maps, not arbitrary fppf sheaves. The local-representability construction assumes a Zariski sheaf covered by open-immersion charts and is not a one-line specialization of this item. The second semantic request completed and was logged even though its process session was lost during a provider interruption; read the completed searches.jsonl entry before using it. No unrun search is recorded.

## Unfinished work

None for the one-level split. The already-existing partition node remains a dependency to be proved according to its own DAG state; it is not treated as a finished Lean proof. No Lean was written or compiled.

## Not duplicates

No new node was created. Reused lem-trf-fppf-sheaf-coproduct-partition rather than creating a cancellation or same-label comparison lemma. Reused lem-weil-pbc-scheme-coproduct-family and lem-weil-pbc-scheme-morphism-gluing for the scheme constructions. The adjacent lem-trf-coproduct-equality-locus describes equality loci of two sections on one scheme; it does not state this two-map atlas pullback, and it is unnecessary here.

## Review by Q61

I read spaces.tex, Tag 0F15 (lemma-coproduct-sheaves-open-and-closed), Tag 02WO (lemma-representable-sheaf-coproduct-sheaves), and Tag 02WQ (lemma-coproduct-algebraic-spaces), including their proofs. Tag 02WQ is the source of the atlas test being expanded; Tags 0F15 and 02WO explain why the summand labels are clopen. I also read schemes.tex around Tags 01JB/01JC and sheaves.tex at lemma-mapping-property-glue for the gluing ingredients. There are no new nodes needing sources. I read the chapter, unit, and nearest blueprint ancestor, and searched the whole imported blueprint for coproduct and partition statements: there is no duplicate blueprint statement. This is support for the existing quotient/coproduct atlas route below the unit, and does not replace any step of the unit.

For Step 1 I opened lem-weil-pbc-scheme-coproduct-family: its statement supplies existence, the outgoing mapping property, and a disjoint clopen covering. Those are exactly what constructs Q and R and the test partition. I opened lem-trf-fppf-sheaf-coproduct-partition: its converse/uniqueness clause identifies equal sections from identical component sections. The equation on each V_i is part of its supplied representation, and p restricts to c_i p_i by hypothesis. All schemes and morphisms remain over S by the summand formulas and uniqueness.

For Step 2 the partition node explicitly states uniqueness of the open subschemes, functoriality under every test-scheme map, and sectionwise injectivity of every c_i. These are the three distinct assertions used: identify the partition on U, pull it and the supplied partition on T back to Z, and cancel c_i. In particular this proves equality as open subschemes; it does not merely infer a factorization through an arbitrary immersion from a pointwise image condition. The fixed site's size assumptions are unchanged. Inverse-image open subschemes of a test object are site objects; no larger indexing category or unlimited colimit is introduced.

For Step 3 each lift is given by the assumed representing bijection at W_i. The scheme coproduct node handles maps from the empty scheme. I opened the statement of lem-weil-pbc-scheme-morphism-gluing: it gives existence and uniqueness for compatible maps on any open cover, and expressly gives equality of morphisms checked on that cover. Different W_i have empty overlaps, so the compatibility hypothesis is verified. The same uniqueness proves the projection equalities. These two Mathlib leaves are generic scheme tools from another unit; finished Mathlib tools are permitted without replacing the present unit's route.

For Step 4 the coproduct node gives disjointness and covering of the V_i and U_i. At a point in the j-th piece, R lands in U_j, so landing also in U_i forces i=j. This is the explicit inverse-image argument, and the open subscheme structures are the restricted structure sheaves. Uniqueness of the given representing bijections then identifies the local lifts, and the morphism-gluing statement identifies their global maps. No uncited comparison theorem is used.

For Step 5 associativity shows that the forward maps commute with test-map composition. A bijection commuting with those maps has a commuting inverse, proving the entire natural isomorphism. For I empty the supplied partition forces T empty, and the coproduct node gives V empty; maps to an empty scheme have empty source, so both functors have the same singleton/empty values. The same observation handles empty summands. I checked the singleton index case, where the construction reduces to the given representing bijection, as well as disconnected tests meeting several pieces; no connectedness or nonemptiness is assumed. Every proof step is under 2000 characters. No clause was moved to a new node, no unsupported non-elementary gluing or partition claim remains, and every cited node's statement was read before producing its verbatim quotation in citations.json.
