# Worker report

## Files written

- `item.json`: split item with four proof steps and no new nodes.
- `citations.json`: verbatim statement excerpts for every proof dependency.
- `report.md`: this report.

## Attachments

None.

## WANTED

None.

## Not duplicates

No new nodes were created, so no duplicate pairs arise. The existing `lem-sp-completion-mate-comparison` has a different statement: it compares completed pullback mates for a cartesian square, whereas this item normalizes direct image of a constant strict tower and its projection augmentation.

## What I checked

I read the item node, its chapter and unit records, the master blueprint source `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/fix-lem-exchanges.md`, and the corresponding main-20261015 blueprint references. The item has no declaration tagged with its blueprint id in the slopmaster2 source and no finished declaration in the upstream master source.

The four steps follow the source's Proof Step 5. Step 1 uses the diagram-site realization and levelwise exact tower category to choose a K-injective representative, checks that the constant tower is K-injective by the exact-evaluation/right-adjoint argument, and computes termwise direct image literally on the diagonal; this proves the isomorphism and identity evaluations. Step 2 checks the hypotheses of the strict-tower derived-limit computation and uses the direct-image/limit comparison's stated underived normalization; on a diagonal representative both sides are the same complex, so the normalized composite is the identity. Step 3 constructs the reduction tower from one flat-term K-flat representative and applies the ringed-topos counit-tensor projection mate, with the canonical tensor/pullback comparison identifying its source and target with the displayed `h_{f,M}`. Step 4 applies the projection mate's naturality and tensor-unit normalization to the strict quotient augmentation, yielding the required tower equality before any inverse limit or evaluation.

For each cited dependency I opened its node and copied the quoted sentence or formula into `citations.json`; each quote is a verbatim part of that node's statement. I checked all hypotheses used in the steps: the index category is the specified small countable tower, module categories are the small-site abelian categories, K-injective and K-flat representatives exist in the stated unbounded derived categories, and the projection mate is formed for the ringed diagram morphism with the given coefficient map. The zero object and identity morphism cases reduce to the same literal diagonal identities. No new node was necessary, no statement was changed, and no SGA source is used.

## Review by N6

I checked the item's exact coefficient datum, small pro-etale sites, ordinary unbounded derived categories, constant tower, evaluation identifications, derived-limit comparison, and projection-mate equation against the item statement and its cited definitions. The source's direct-image generator paragraph gives the diagonal equality used in Step 1, while its final normalization paragraph gives the quotient-augmentation equation in Step 4. I checked every step's cited node statement rather than relying on proof text: diagram realization supplies strict towers and exact evaluation, the K-injective nodes supply representatives and derived computation, the strict-limit node supplies `R lim`, the pushforward-limit node supplies `a`, and the projection-mate/tensor nodes supply the actual map and its unit normalization. I also searched the whole DAG and blueprint for a matching constant-tower normalization node; none states this item, and the closest completed-mate node has a different conclusion and hypotheses. The Mathlib searches were run twice with changed phrasings and are recorded in the item node; all hits were generic derived-functor or inverse-system declarations and none states this project-specific tower normalization.
