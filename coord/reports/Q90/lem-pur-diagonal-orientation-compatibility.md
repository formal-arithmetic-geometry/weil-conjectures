# Q90 — lem-pur-diagonal-orientation-compatibility

1. Files written: `dag/nodes/sec-smooth-purity/lem-pur-diagonal-orientation-compatibility.json` (statement, no new nodes, no Mathlib leaf); `citations.json`; this report.
2. Attachments: none.
3. WANTED: none.
4. The imported statement is retained verbatim. No new node was created: the affine-line rigidity is already stated by `lem-pur-a1-pullback-endomorphism-rigidity`, and the ordinary/pro-etale comparison and tensor/full-faithfulness tools already exist. The fresh Mathlib searches found no matching theorem.
5. Nothing remains unfinished.

## Not duplicates

`lem-pur-diagonal-orientation-compatibility` vs `lem-pur-lisse-uniqueness`: the existing node assumes a separated finite-type base and works directly with pro-etale sheaves; this item is an ordinary-etale coefficient-reduction comparison over an arbitrary Noetherian base and also proves the derived equal-shift injectivity clause.

## Review by Q90

I read the item source in the main-20261015 DNC proof, the current item statement, and every cited node. The Noetherian specialization statement supplies the precise local rank-one, degree-shift hypotheses for both coefficient rings, so Step 1 legitimately removes the common shift and uses the existing tensor/pullback comparison. In Step 2 I checked the two composites have the same unit-fibre restriction, and that the lower-left matrix construction turns their difference into an endomorphism of an affine-line pullback. The ordinary-to-pro-etale comparison is faithful at finite level, its pullback comparison is compatible with composites, and the arbitrary-base rigidity lemma applies because the direct sum is finite locally constant; this verifies all hypotheses despite the base being merely Noetherian. Step 3 is the typed cancellation of the two invertible fibre maps and gives exactly the displayed delta identity. Step 4 repeats the matrix argument for arbitrary finite locally constant sheaves and invokes degree-zero full faithfulness for equal shifts. I checked empty base, $d=0$, $A=B$ ($r=m$), zero coefficient maps, and disconnected/nonreduced bases; all reduce to the same matrix or identity argument. No statement correction, duplicate, attachment, SGA source, or new node was needed.
