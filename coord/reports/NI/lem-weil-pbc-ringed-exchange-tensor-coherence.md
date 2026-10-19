## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-ringed-exchange-tensor-coherence.json: statement, split; no Mathlib match.
- citations.json: verbatim statements for every citation in the five proof steps.

No new nodes and no new Mathlib leaves. The generic composition comparison and its tensor compatibility are proved from the existing K-flat representative results rather than creating an elementary lemma. The adjunction manipulation is written explicitly rather than moved into a node restating this item's conclusion.

## Attachments

None. Searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the blueprint tag, projectionFormula/projection_formula, exchange with tensor, and baseChange with tensor; no declaration states the item for arbitrary ringed topoi. Read the TensorHom.lean introduction: its exchange is tensor–Hom/exceptional adjunction, with coefficient categories and projection hypotheses, not this exchange diagram. The master checkout was searched for the item's tag as reference only; no master sorry declaration is used as evidence of completion.

## WANTED

None. All literature used is present.

## Corrections and statement precision

STATEMENT-DISPUTED: the imported reference to def-weil-pbc-projection-formula-map is not a definition for arbitrary ringed topoi: its statement is restricted to pro-etale operations of schemes. It cannot justify the item's general coefficient categories. Replaced that reference by the explicit adjunct definition from Stacks Tag 0B56, equation-projection-formula-map; retained exactly the diagram of Tag 0E48. Derived direct images and their canonical adjunctions are part of the item's given operations, not conclusions inferred from a node about bounded-below etale abelian sheaves.

Made explicit that the chosen commutation isomorphism is a ringed-topos isomorphism. If only underlying topoi were meant, the statement would be ill-typed: take all four underlying topoi to be Sets, O_Y = Z[t], and the other three rings Z, with f induced by t ↦ 0, g by t ↦ 1, and f',g' by identity ring maps. Underlying topoi commute, but the composite ring maps do not. On Q = Z[t]/(t), the two derived pullbacks along these composites are respectively Z ⊕ Z[1] and zero, so there is no pullback commutation isomorphism. Tag 0E48 says a commutative diagram of ringed topoi, so the explicit compatibility is faithful to the source rather than a geometric extra hypothesis. No target or unit statement changed.

Removed the narrow projection definition dependency; added the general mate definition. No cartesianness, properness, boundedness, perfectness, or flatness was introduced. The site-size convention is the universe convention already imposed by the cited generic derived construction.

## Blueprint and duplicate searches

Read dag/chapters/sec-proper-base-change.json, dag/units/sk-thm-properbasechange.json and the three levels in SETUP.md. This is the foundational coherence needed in thm-weil-pbc-amplification-proper proof (b), not an alternative geometric route to proper base change. Ran blueprint_refs.py ancestor for the item and searches for projection, exchange, ringed, monoidal, composition, 0E48 and tensor coherence; searched the DAG for 07A4, 0E48, 0D6D, mate and ringed/tensor composition. The existing lem-kun-proj-formula-natural is for cartesian scheme squares with constant etale coefficients, and prop-sf-pf-coherence uses its finite-type six-functor datum; neither covers arbitrary ringed topoi and noninvertible structure-ring maps. The item's same_as remains empty.

Read every node whose source carries 0D6D. The existing proetale-derived-pullback-composition assumes schemes and identifications of inverse-image coefficient rings; derived-inverse-image-composition and derived-square-iso-pasting concern bounded-below etale abelian sheaves. Instead of citing these outside their hypotheses, Step 1 writes scalar-extension associativity on the generic K-flat representatives, and Step 2 writes the balanced tensor calculation. No new nodes therefore need a Not duplicates pair list.

Mathlib searches were actually run with msearch.py and are in searches.jsonl; the fresh entries appended to the item's existing searches use the exact logged query texts. Two phrasings of projection/exchange compatibility and a phrasing of composition/tensor compatibility gave only ordinary sheaf pullback composition, cartesian over-category coherence and general adjunction identities. Loogle's projection substring hits were unrelated Lean internal declarations; grep's scalar base-change hits are module identities, not this diagram. LeanSearch returned Internal Server Error and is recorded unavailable. None was called a match or an attachment.

## Unfinished work

None in this one-level split. Existing unsplit inputs remain existing items; they were not silently treated as completed Lean proofs.

## Review by NI

I read sites-cohomology.tex Tag 0E48 (remark-compatible-with-diagram) in full, including the labels t,b,p,c and its sentence omitting the verification; Tag 07A4 (lemma-pullback-tensor-product), whose proof constructs the comparison by termwise module tensor maps; Tag 0D6D (lemma-derived-pullback-composition), whose proof computes successive pullbacks on flat K-flat representatives; and Equation 0B56 defining projection as the counit's adjunct. There are no new node statements to check against literature. The proof is marked agent-written because I supply the verification that 0E48 omits.

Step 1 cites lem-pc-kflat-resolution for existence of resolutions with flat terms, ringed-topoi-derived-pullback for the actual comparison computing derived pullback, ringed-topoi-derived-tensor-pullback for preservation of flat K-flat complexes, and site-derived-tensor-descent for the equivalence from their localization. I opened their statements: each explicitly says the property used. The composition formula is written as a scalar multiplication and its inverse, not inferred from the restricted pro-etale composition lemma. It is natural and degree-preserving, hence defines a complex isomorphism. No ordinary pullback on all complexes is localized.

Step 2 uses module-pullback-tensor for the canonical ordinary module comparison, derived-tensor-pullback for its canonical derived counterpart, and site-derived-tensor-descent for the two-variable unique extension. The elementary part is the explicit balanced-tensor computation: splitting a pure tensor commutes with multiplying nested scalar images. Ringed compatibility identifies these images on the two paths. There is no interchange of factors and therefore no hidden Koszul sign. This proves a specific formula for theta, rather than citing a definition for an unproved tensor compatibility.

Step 3 uses the generic adjunction-mate node, whose statement explicitly gives the transpose H(epsilon) theta and its unit formula. The projection transpose follows from its inline definition and the displayed counit-naturality/triangle calculation. The adjunction bijection is a given adjunction, so no existence theorem outside its scope is being invoked.

Step 4 uses only naturality of theta constructed in Step 1, the projection transpose identity from Step 3, and the simultaneous naturality stated by derived-tensor-pullback. I checked the type of a: its source is CB(RE tensor Q) and target HE tensor CBQ; in particular the target-identification factor is theta_Q inverse, not theta_Q. Step 5 uses the same tensor naturality and the mate transpose, then substitutes Step 2 and cancels theta_Q inverse times theta_Q. Both transposes become (delta_E tensor identity) t_C C(t_B); adjunction injectivity gives the desired equality. Naturality follows from naturality of the maps just constructed, without assuming exchange or projection is invertible.

Checked small cases: identity edges give theta and exchange identity and both sides the same projection map; zero E or Q gives zero maps. One-point ringed topoi with a nonflat ring map Z → F_2 are allowed: K-flat resolutions compute derived tensor, rather than dropping Tor terms. Squares arising from two factorizations of the same ring map need not be cartesian; only the compatible ring map and its pullback comparison are used. The incompatible evaluations example above checks why a bare topoi commutation cannot suffice. The unrestricted Q need not be perfect, and nowhere is an inverse projection map used.

Against delivery-errors B–E: statements introduce their objects, TeX has single backslashes, source places use tags and labels, no new proof-bearing leaves or duplicate nodes were made, and all citations have verbatim statements in citations.json. All non-elementary representative/descent inputs are existing cited statements; the later steps carry the actual calculation instead of relabelling the coherence claim. The corrected dependency list is exactly the union of uses, and no dependency is taken from a cited node's proof. The principal repair during self-review was to avoid the pro-etale-only definition/composition citations and to orient the final theta_Q identification correctly.

## Second reading by NI

- Item statement: checked against Stacks Tag 0E48, `remark-compatible-with-diagram`, including all four ringed topoi, edge morphisms, commutative square, arbitrary derived objects, and the displayed two composites; verdict: faithful, with ringed commutation stated explicitly because Tag 0E48 requires a commutative diagram of ringed topoi.
- Step 1: checked against Tags 0D6D, `lemma-derived-pullback-composition`, 0G7E, `lemma-pullback-K-flat`, and the cited K-flat/pullback/descent node statements; verdict: scalar-extension comparison and representative independence are written explicitly and all cited hypotheses are present.
- Step 2: checked against Tag 07A4, `lemma-pullback-tensor-product`, and the module/derived tensor-pullback statements; verdict: balanced-tensor calculation supplies the omitted coherence, with no unproved sign or factor interchange.
- Step 3: checked against Tag 0B56, `equation-projection-formula-map`, Tag 0E48, and `def-weil-pbc-adjunction-mate`; verdict: projection and exchange are defined by the correct counit mates and the transpose identity is stated with its triangle calculation.
- Step 4: checked against the four-arrow diagram in Tag 0E48 and the naturality clauses of the tensor-pullback node; verdict: source and target identifications, including the inverse orientation of `theta_Q`, are type-correct and the transpose expression follows by naturality.
- Step 5: checked against the same Tag 0E48 diagram and the mate bijection; verdict: tensor coherence substitutes exactly the Step 2 formula and cancellation proves equality and naturality without extra geometric hypotheses.
- New nodes: none; therefore B1--B7 and duplicate-node checks are vacuous. Existing cited nodes were searched in `dag/nodes` and their statements were compared verbatim in `citations.json`.
- Small cases: identity square, zero objects, one-point ringed topoi, and a non-flat ring map were checked; no edge case changes the statement. A bare underlying-topos commutation was rejected by the explicit incompatible-evaluations counterexample recorded above.
- Changes made: no node or proof change; this second-reading section records the source and dependency audit required by the delivery contract.
