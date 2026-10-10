files written:
- `dag/nodes/sec-picard-framework/lem-pc-ringed-spaces-derived-direct-image-composition.json`: item, statement split, no new nodes, Mathlib searches record no direct match.
- `citations.json`: verbatim statement quotes for all three proof-step citations.

attachments:
- None. The existing `AlgebraicGeometry.Etale.rightDerivedLowerStarComp` is for étale sheaves on schemes and does not state this arbitrary ringed-space/module theorem.

WANTED:
- None.

what was wrong in the node, blueprint, or brief:
- The item was unsplit even though its three required ingredients had already been split elsewhere in the DAG. I added those three existing nodes as statement and proof dependencies and wrote the argument at the item level, without creating a duplicate composition node.
- The existing scheme-level node `lem-pc-derived-direct-image-composition` has the same shape but is narrower than the ringed-space statement, so it is not used.

what could not be finished, and why:
- Nothing.

## Review by E1

I read the item against Stacks Tag 0D5T and the supporting Tag 079W and Tag 0D5S arguments. Step 1 cites `lem-pc-ringed-spaces-derived-adjoint-general`; its statement explicitly supplies the adjunction between each derived pullback and derived direct image, so the hypotheses for f, g, and g composed with f are present. Step 2 cites `lem-pc-ringed-spaces-derived-pullback-composition`; its statement explicitly supplies the natural isomorphism from Lf-star composed with Lg-star to the pullback for the composite, which is exactly the transport needed to regard the composite direct image as a right adjoint. Step 3 cites `lem-cat-right-adjoint-composition`; its statement gives the canonical comparison of the right adjoint of a composite with the composite of right adjoints, and I instantiate F with Lg-star and G with Lf-star so the order is Rg-star composed with Rf-star. I then take the inverse to match the item’s displayed orientation. The hypotheses are arbitrary morphisms of ringed spaces throughout, and no properness, finite type, or Noetherian assumption was introduced. I checked the small identity case: with f the identity, the result reduces to the right-derived direct-image identity comparison. The citation quotes are copied verbatim from the three cited node statements.

## Second reading by E1

- Item statement: checked against Stacks Tag 0D5T (`cohomology-lemma-derived-pushforward-composition`); arbitrary morphisms of ringed spaces and the functor direction $D(\mathcal O_X)\to D(\mathcal O_Z)$ agree hypothesis by hypothesis.
- Step 1: checked against the statement of `lem-pc-ringed-spaces-derived-adjoint-general` and Stacks Tag 079W; it supplies all three adjunctions after instantiation, with no unstated finiteness hypotheses.
- Step 2: checked against the statement of `lem-pc-ringed-spaces-derived-pullback-composition` and Tag 0D5S; the displayed pullback isomorphism has the correct order and transports the composite adjunction.
- Step 3: checked against `lem-cat-right-adjoint-composition` and the proof of Tag 0D5T; the assignments $F=Lg^*$ and $G=Lf^*$ give $Rg_*\circ Rf_*$, and inversion gives the item’s orientation.
- New nodes: none; all three cited nodes are existing statement or Mathlib leaves, so B1--B7 do not introduce a new node to audit. Existing-node search was made with `rg` over `dag/nodes`.
- Edge cases: identity morphisms reduce to the derived direct-image unitor; zero complexes and complexes over a field are functorial instances of the same adjunction; for the empty ringed space all categories and functors are still covered by the formal adjunction argument. No integer parameter $n$ occurs in this item.
- Changes: no mathematical or owned-field changes were needed. The inherited `created.item` metadata names an earlier lemma, but it is maintainer-owned and `deliver.py` preserves it for an existing item node; changing it in this split would violate the delivery field contract.
