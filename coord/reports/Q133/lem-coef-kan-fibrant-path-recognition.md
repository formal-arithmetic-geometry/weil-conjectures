## Files written

- `dag/nodes/sec-six-functors/lem-coef-kan-fibrant-path-recognition.json`: statement, now split in six proof steps. Not a Mathlib leaf. Its statement and statement dependencies are unchanged.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- No new nodes, no new Mathlib leaves, and no unit-record changes. This item is a descendant tool, not its unit's key statement.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` for the exact item tag and for `homotopyCartesian`, `homotopyPullback`, `homotopy_pullback`, `PathObject`, `pathObject`, and `fibrantReplacement`, including the alternate words homotopy cartesian and Kan/fibrant paths. No declaration states this item. No attachment is inferred from master reference material.

## Sources wanted

WANTED: Charles Rezk, *Fibrations and homotopy colimits of simplicial sheaves*, Section 2.3, printed p.4, https://rezk.web.illinois.edu/rezk-sharp-maps.pdf, archival copy for lem-coef-kan-fibrant-path-recognition.

WANTED: Kerodon, Proposition 3.4.0.2 (0109) and Proposition 3.4.0.7 (0329), https://kerodon.net/tag/0109 and https://kerodon.net/tag/0329, archival copies for lem-coef-kan-fibrant-path-recognition.

These sources were read online, without downloading into the shared repository. The complete proof is marked `proof_origin.by = agent`: Rezk supplies the two-leg definition and says replacement independence is straightforward, but does not give this explicit arbitrary-base/functorial-Kan path comparison. The proof supplies those details using existing nodes. Kerodon tags are not Stacks tags; no Stacks tag for this comparison was found or asserted.

## Findings and corrections

The item was unsplit with no Lean audit/declaration attached. Its statement is mathematically correct and agrees with Rezk's two-leg definition followed by the specified Kan path formula; no statement dispute or correction is needed. The existing source points to paragraph 2 of `prop-coef-integral-exceptional-adjoint.proof.md`, where the derived coefficient adjunction needs mapping-space coherence. This node's inherited ancestry passes through the sharp-map setup. I read that paragraph and the recorded chapter and unit. The split stays within that descendant comparison and makes no change to the unit or chapter route.

I replaced the empty proof with an explicit comparison diagram. In particular I did not assume that applying an arbitrary functorial fibrant-replacement functor preserves fibrations or strict pullbacks. Instead I chose fibrations over RZ and pulled them back to Z, using right properness. Nor did I use `lem-coef-kan-homotopy-cartesian-invariance` or `lem-coef-kan-homotopy-cartesian-fibration-criterion`: both statements define homotopy cartesianness through this item, so using them would risk circularity. The internal-Hom fibration-corner theorem is an existing Mathlib leaf; it supplies an actual endpoint fibration, which is not part of the statement of the existing constant-path comparison node.

## Unfinished work

None in this one-level split. The cited unsplit/lower-stage nodes retain their own work. New nodes: 0. New Mathlib leaves: 0.

## Not duplicates

No new nodes. Searches of the whole DAG and `tools/blueprint_refs.py search 'homotopy pullback'` and `search 'path'` found the existing strict-pullback-invariance and constant-path-comparison nodes, which are reused. The blueprint searches found no equivalent imported statement; `blueprint.same_as` remains `[]`. `tools/blueprint_refs.py ancestor` confirms `prop-coef-integral-exceptional-adjoint`; its existing exact paragraph reference and via chain are retained.

## Mathlib searches

All new searches used the prescribed Q133/item `msearch.py` command and are recorded verbatim in the node and `searches.jsonl`. Two semantic phrasings, Loogle, LeanSearch, and a grep of Mathlib/AlgebraicTopology were run; all services answered. Hits were read: abstract path-object projection weak equivalences, lifting axioms, bifibrant-object weak-equivalence transport and ordinary pullback constructions do not state the arbitrary-base recognition equivalence. I also read `Mathlib/AlgebraicTopology/ModelCategory/PathObject.lean` (path-object data and good/very-good conditions), and `Mathlib/AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean` (horn lifting). These justify the negative verdict rather than treating search-service hits as matches. The existing historical searches are retained.

## Review by Q133

I read Rezk Section 2.3 on printed p.4, including its definition using two weak-equivalence/fibration factorizations. It imposes no fibrancy or nonemptiness condition on the four corners, just as the item states. I read Kerodon 0109 and 0329 online and opened the statements of each cited DAG node. The former allows arbitrary objects in its six-object diagram and requires fibrations on the corresponding legs; the latter supplies the constant-path inclusion. The DAG constant-path node has the stronger Kan-object hypotheses, which are satisfied only after step 1, exactly where it is used in step 6. No new node needs a separate source check.

1. Step 1 uses the actual functorial model structure and right properness stated by `lem-coef-kan-quillen-model-right-proper-core`. It factors RX and RY over RZ, whose terminal map is a fibration, so the intermediate U and V are Kan. It pulls those fibrations back along r_Z, whose weak-equivalence hypothesis is supplied by fibrant replacement. The maps X to K and Y to L are defined by the naturality equations, not by choosing points. Two-out-of-three makes them weak equivalences. I wrote the elementary horn-lifting arguments for composition and pullback stability, so no separate closure lemma is hidden.

2. Step 2 again uses the core's model axioms to factor f and g with trivial cofibrations. The lifting problems have those trivial cofibrations on the left and the candidate fibrations on the right; no fibrancy of Z is used. Each lift is a weak equivalence because its composite with the initial trivial cofibration is the supplied weak equivalence. I checked `lem-coef-kan-pullback-fibration-invariance` says invariance of strict pullbacks, not merely invariance of abstract homotopy pullbacks. Its two fibration hypotheses hold for T to Z and X_f to Z (respectively T to Z and K to Z); its other outer component maps come from S and are weak equivalences. The under-X/under-Y equations make the Q comparison maps commute. This writes out the replacement-choice argument Rezk leaves straightforward; it does not cite a new restatement of the item.

3. Step 3 applies the same strict-pullback node with base r_Z, outer maps K to U and L to V, and left legs k and p. All three component maps are weak equivalences from step 1. Naturality of r gives w c_0 = d r_Q literally, so two-out-of-three compares the specified maps. No preservation of a pullback or a fibration by R is assumed.

4. Step 4 uses exactly the formula in `lem-cbc-internal-hom-fibration-corner-map`, with the boundary monomorphism and C to the point. I checked its Mathlib source, `AnodyneExtensions/PushoutProduct.lean`, lines 70-93, and the horn-fibration convention at `CategoryWithFibrations.lean`, lines 70-89. The target is C times C by the two vertices of the boundary; the functor space into the point is a point. Every subsequent fibration is a pullback or composite as explicitly described. The uses of B, V and C being Kan are stated where projections to C are needed. This is a Mathlib leaf, so its other-unit location creates no route replacement.

5. Step 5 pulls back beta along the specified fibration E_V to V, so right properness really applies. Its strict-pullback-invariance citation has fibrations E_B to C and E_V to C established in step 4, a common identity base, and weak-equivalence outer maps established in steps 1 and 5. I checked the orientation of endpoints: E_B fixes endpoint 1 at G(b), and its map to C is endpoint 0. Therefore the resulting pullback is precisely the displayed P_R, not the reverse path object.

6. Step 6 uses the statement of `lem-coef-kan-pullback-path-comparison` for the Kan objects U, V, C and the fibration p (indeed q also is one). Its weak equivalence is the actual constant-path inclusion psi. The statement of `def-cbc-enhanced-diagrams-cones` defines the internal functor and constant-diagram maps, which make phi c and psi d identical in every simplicial degree. The core supplies two-out-of-three. Combining steps 2, 3 and 6 proves both directions, including the existential direction since K and L already give admissible replacements.

I checked delivery-errors B through E against the files: no new definition, duplicate, item-clause node, unsplit proof sketch or unlogged search is introduced; every non-elementary step cites the nodes that state its input. `citations.json` was copied from their statements, not from their proofs. No proof step exceeds 2000 characters (lengths 989, 1175, 566, 812, 615, 815), and the few model-axiom operations inside the steps are explicit rather than appeals to an unnamed general comparison theorem.

For edge cases I checked Z empty (then all four original objects mapping to it are empty), X or Y empty with Z nonempty (the replacement and pullback constructions still exist), and a non-Kan Z (the only right-properness pullbacks are along actual Kan fibrations; K and L are never asserted Kan). No argument uses a vertex or surjectivity on vertices. For the empty simplicial set, a weak equivalence from it forces its replacement to be empty as well. For nonempty inputs an arbitrary functorial R can change the simplices substantially; the proof uses only r_T being a weak equivalence, RT being Kan and strict naturality, so it does not require R to preserve products or existing fibrations. I found no source error requiring a departure, and the changes above are the complete corrections to the original missing argument.
