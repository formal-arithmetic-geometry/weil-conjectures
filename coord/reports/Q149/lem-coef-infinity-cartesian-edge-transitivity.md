Files written:

- `dag/nodes/sec-six-functors/lem-coef-infinity-cartesian-edge-transitivity.json`: statement node, split into five proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement citations for every cited node in every proof step.

Attachments: none found. A search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, Cartesian-edge transitivity, inner fibrations, and the relevant declaration names found no project declaration stating this result. The source checkout is read-only reference material and contains no finished attachment.

WANTED: Kerodon Corollary 5.1.2.6 (tag 01TU), statement and proof, for the item; read online 2026-10-17 at https://kerodon.net/tag/01TU but no archival copy is in `literature/`.
WANTED: Lurie, Higher Topos Theory, Propositions 2.4.1.8 and 2.4.4.3, for the horn/mapping-space Cartesian criterion; the existing criterion node records this reference. This session’s IAS PDF fetch timed out. I checked the analogous mapping-space criterion and its full proof in Kerodon Proposition 5.1.2.1 (01TL) online instead; no archival copy is in `literature/`.
WANTED: Kerodon Proposition 3.4.1.11 (tag 0110), for homotopy-pullback transitivity; read online 2026-10-17 at https://kerodon.net/tag/0110 but no archival copy is in `literature/`.

No source error was found. The imported item statement has the required hypotheses: (a) and (b) are inner fibrations, (a(h)) is (b)-cartesian, and the conclusion compares (a)-Cartesian with ((b\circ a))-Cartesian for the same edge.

## Review by Q149

I read the imported item node, its current blueprint ancestry (`prop-coef-integral-exceptional-adjoint`), the unit `sk-prop-sf-biduality-general`, and the chapter record. I also read `def-coef-infinity-fibrations`, `def-cbc-enhanced-diagrams-cones`, `lem-coef-infinity-cartesian-mapping-criterion`, `lem-coef-infinity-hom-bifunctor-functoriality`, `lem-coef-infinity-pinch-comparison`, and `lem-coef-infinity-homotopy-pullback-pasting` in the DAG. No new node was needed: every non-elementary ingredient is already stated by one of those existing nodes.

Step 1 verifies the composite (r=b\circ a) is an inner fibration by explicitly solving an inner-horn lifting problem first in (D) and then in (A), using the definition in `def-coef-infinity-fibrations`; this is a short elementary construction. Step 2 fixes an arbitrary test vertex (z\in A) and writes the complete three-level mapping-space diagram. I checked that the cited pinch-comparison node supplies Kan mapping spaces and that the cited Hom-bifunctor node supplies coherent postcomposition and naturality squares, including higher homotopies. The outer vertical composite is explicitly identified with the map induced by (r=b\circ a), rather than being inferred only on components.

Step 3 applies the existing Cartesian mapping criterion to (b) and the edge (a(h)), at the test vertex (a(z)); its hypotheses match the item’s inner-fibration and Cartesian-edge assumptions. Step 4 applies the existing homotopy-pullback pasting theorem to the stacked diagram, with the concatenated commutation homotopy from Step 2, and checks that its “left square iff outer rectangle” conclusion is exactly the upper-square versus outer-rectangle equivalence. Step 5 varies (z) over all vertices and applies the Cartesian mapping criterion to (a,h) and (r,h), yielding the claimed iff.

I checked every citation quote against the cited node’s statement and recorded each in `citations.json`. I also ran the required semantic, Loogle, and Mathlib-source grep searches. The searches returned only ordinary-category Cartesian-composition declarations (`CategoryTheory.Functor.IsFibered.comp`, `IsStronglyCartesian.of_comp`, etc.), which do not state the two-inner-fibration quasicategory result; the focused quasicategory grep found no relevant declaration. The item’s original searches were retained, and the required searches were rerun and appended to the recorded search list.

I read Kerodon 01TU in full, its proof input 01TL in full, and 0110 in full, and checked the Hom functoriality sources 046J and 03PD and the composition source 01PF online. The proof follows the mapping-space/pasting argument of 01TU using the already existing right-pinched mapping criterion instead of its fixed-triangle model. The source has a harmless denominator typo in the middle displayed fixed-triangle mapping space (it writes C for a D mapping space); our formula uses the correct category at every level. Since these sources are not archived, proof_origin.by is agent and the missing archives are WANTED, rather than pretending to follow a locally archived document. No SGA source is used.

I checked B–E of delivery-errors against this delivery: the statement is unchanged and self-contained through its existing notion nodes; no statement-only child or duplicate or restatement was created; every theorem used is in a cited statement, not merely a citation tag or the proof of that statement. The ancestor’s current main-20261015 file is in sk-thm-sf-package, paragraph 2 (derived mapping adjunction); the inherited historical unit/ancestry is preserved, with no geometric route change. All theorem citations have the same inherited unit, so there is no off-unit theorem tool use to declare. The graph closure of each cited node was traversed and none reaches the item.

Small cases checked: for a and b both identity maps all squares have identity verticals; if b is an identity, the lower square is automatically a pullback and the result compares the identical edge predicate; if B is a point, the assumption says a(h) is an equivalence and the same pasting argument still applies. Empty mapping spaces are permitted Kan complexes and all cited theorems allow them. The edge h provides vertices u and v, so an empty A is excluded by the input rather than imposing any hidden nonemptiness hypothesis on spaces. No existence of other Cartesian lifts, essential surjectivity of a, small indexing category, limits of diagrams, or chosen pullback objects is used. The lower criterion is needed only at a(z); we never infer a universal statement on D from the image of a. Step 1 is the only elementary step. Each of the five proof steps is below 2000 characters; no hidden comparison lemma or long proof has been moved inline.

Nothing mathematical remains unfinished in this one-level split. Existing unsplit dependencies remain separate queue items.

## Not duplicates

No new nodes. Whole-DAG and blueprint searches found the existing Cartesian mapping criterion and homotopy-pullback pasting statement; both are reused. The item itself is not duplicated by a blueprint node (blueprint searches for “cartesian edge” and “homotopy pullback” returned no blueprint matches).
