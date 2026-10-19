# Stage-1 report: lem-amb-shriek-open-exchange-adjoint

## Files written

- `lem-amb-shriek-open-exchange-adjoint.json`: the assigned statement, split with three proof steps; no new nodes.
- `citations.json`: verbatim statement excerpts for every cited node in Steps 1 and 2.
- `report.md`: this report.

## Attachments

None. I searched the slopmaster2 source for the item id and for the relevant open-exchange and compact-support-adjoint declarations; no sorry-free declaration states this item exactly.

## WANTED

None.

## Not duplicates

No new nodes were created, so no duplicate pair arises.

## Review by Q01

I read the assigned node, the sec-smooth-purity chapter and unit records, the parent blueprint proof for `thm-amb-vector-bundle-purity`, and the source declarations in `WeilConjectures/SixFunctors/Etale/Derived/OpenImmersionLowerShriekLowerStarExchange.lean` and the derived compact-support comparison files. The imported statement uses ordinary unbounded etale derived categories, the normalized open-extension adjunctions, the compactification-independent composition maps, and the canonical base-change exchange; I preserved those hypotheses and the direction of every displayed morphism.

Step 1 cites `lem-amb-unbounded-compact-support-comparisons` for the normalized composition maps and exchange, `lem-amb-unbounded-proper-open-interchange` for the cartesian proper/open interchange being the inverse restriction mate, and `lem-asd-etale-compact-support-normalization` for identifying compact support along an open with `Du_!` and its evaluation counit. I opened each cited statement and verified that it says the exact comparison used by the step. Step 2 expands the adjunct as `u^*κ ∘ η_u`, substitutes the defined `κ` and `δ`, and uses the same proper/open mate formula plus the triangle identity for `Dv_! ⊣ v^*`; the cited comparison node explicitly states that `C` is the canonical proper exchange followed by the inverse open-extension comparison and is compatible with the composition maps. Step 3 is the elementary injectivity of an adjunction bijection and records that all cited constructions are unbounded, so no boundedness condition is introduced. I checked empty opens, the identity base change, and the zero complex: all maps reduce to the corresponding identity or zero mate, with the stated orientation unchanged.

The Mathlib searches were rerun with `msearch.py` and recorded in `searches.jsonl`; they found only generic mate/adjunction declarations and no statement of this geometric compact-support identification. Since the existing DAG already contains every substantive geometric comparison, I created no new node and introduced no duplicate or off-unit tool citation.

## What was wrong or corrected

The imported node had an empty proof and no `proof_deps` or split report. I supplied the missing normalized mate calculation, filled the blueprint location and review metadata, and kept the statement unchanged.

## Unfinished

Nothing.
