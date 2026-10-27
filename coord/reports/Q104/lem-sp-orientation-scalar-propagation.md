# Stage-1 report: lem-sp-orientation-scalar-propagation

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-orientation-scalar-propagation.json: statement, split using existing nodes; no Mathlib match.
- citations.json: verbatim statement excerpts for every step citation.
- searches.jsonl: actual search-command log, retained unchanged.

New nodes: 0. Mathlib leaves: 0. The statement and all statement dependencies are unchanged. The item is not the unit's key node, so no unit record is changed.

## Attachments

None. I searched lean/WeilConjectures both for the blueprint id and orientation/scalar terminology. OrientationDatum.lean defines coefficient compatibility as a property of supplied orientation data; it does not prove the required transport assertion for the direct diagonal family and fixed comparisons. Orientation.lean supplies orientations and duality consequences, not this statement. No project declaration found states both clauses.

## WANTED

None. This is an agent assembly proof from existing DAG statements; it is marked proof_origin.by = agent, not attributed to a human source.

## Changes and source audit

The imported item had an empty proof. The split now verifies the finite-Tor domains, fixes the canonical source comparisons, writes the horizontal pasting calculation, and transports the assumed unit equation by the compositor scalar identity. It never assumes coefficient flatness or faithfulness, and never derives composition compatibility from an orientation datum that already assumes it.

I read the current blueprint at literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/_section.md, sk-prop-sp-composition-factors.md and its proof, and sk-prop-sp-composition-comparisons.md and its proof. I also read sk-lem-sp-reduction/sk-lem-sp-reduction-compatibilities.md and its proof, and the reduction proof. The unit's finite-coefficient orientation route and subsequent scalar passage are preserved; no chapter or unit route is replaced. The old source.document snapshot is retained as imported metadata, while each new proof step points to latest/. No SGA source is used.

Whole-blueprint searches for orientation scalar, iterated purity, and coefficient purity found the existing reduction-compatibilities and finite-general-ring statements, but no statement of the whole item. The rational iterated-purity-scalar-pasting node concerns finite extensions of Q_l and cannot substitute for arbitrary finite ring maps. The finite-diagonal-orientation-reduction node only allows the specified quotient rings; it is not used to claim arbitrary coefficient compatibility. Existing det-sp-reduction-compatibilities explicitly allows arbitrary unital finite-ring maps and is used instead. I checked the dependency closure of every substantial proposed citation against this item: none reaches it, so there is no circular invocation of its parent det-sp-composition-factors.

## Mathlib searches

Six searches ran through msearch.py and their queries are copied into the item's mathlib_searches. The first semantic phrasing gave smooth ring/algebra base-change lemmas; these concern algebraic smoothness rather than the purity natural transformation. The second phrasing gave horizontal-composition, interchange and mates lemmas, including CategoryTheory.TwoSquare.hCompVCompHComp and CategoryTheory.mateEquiv_hcomp. These explain the formal calculation but do not state either assertion for the actual exceptional, diagonal-purity and finite-coefficient comparisons. Loogle found CategoryTheory.NatTrans.naturality, whose naturality field I read in Mathlib/CategoryTheory/NatTrans.lean. It is an elementary ingredient of pasting, not a one-line specialization proving this entire item. The CategoryTheory and AlgebraicGeometry greps found no purity scalar/orientation declarations. LeanSearch likewise gave smooth ring maps and base change, not exceptional purity. All services answered; none was recorded as unavailable. No new node was created for naturality, cancellation, or functoriality of tensor.

## Not duplicates

No new nodes. Existing lem-pur-iterated-purity-scalar-pasting is a rational-coefficient result, and lem-sp-orientation-scalar-tower-transport concerns base-change orientations and tower evaluation, rather than composition of f and g. Neither is a duplicate to introduce or a substitute with matching hypotheses.

## Tool uses

lem-sfb-ringed-derived-monoidal-comparisons and lem-pur-cochain-pullback-tensor-coherence are declared in split_report.tool_uses. Their only role is the generic canonical tensor/pullback/coefficient source square. They prove no orientation identity and do not change the unit's route. The other proof citations already lie on the unit route. No maintainer-owned tool_uses field was written.

## Review by Q104

I reviewed delivery-errors B through E against the actual files. There are no new statement-only nodes, new notions, Stacks-tag duplicates, or Mathlib leaf claims to audit. Each step is below 2000 characters. The substantive facts are cited as statements; elementary steps contain the actual formulas rather than words such as 'transport' concealing a calculation.

For Step 1 I opened lem-sp-composite-projection-coefficients: it explicitly gives G_g K and omega_g as constructible finite-Tor inputs, natural unital associative invertible projections, and their composite equation for finite rings. I opened lem-sp-composite-tensor-transpose: its final sentence gives t at the unit and naturality, while its hypotheses match those projections and the counit-preserving composition comparison. det-sp-scalar-extension-functor clause (2) preserves the same Tor interval for arbitrary finite-ring maps. These statements justify using the purity square at G_g K, and tensor naturality at the unit, without an implicit preservation hypothesis.

For Step 2 I opened the derived monoidal comparison statement and its K-flat normalization, and the cochain pullback/tensor coherence statement including its explicit coefficient chain equations. They concern arbitrary small ringed topoi and nonflat ring maps; take the small pro-etale ringed topoi and constant coefficient maps. Scalar extension is the same derived pullback along the identity geometric morphism with its ring map. This identifies the two source paths as the same balanced map. det-sp-scalar-extension-functor clause (3) identifies Tate lines with ordinary scalar tensors, so tensor powers and their even shifts have these same canonical maps. No claim about an arbitrary unbounded derived evaluation functor is used.

For Step 3 I opened det-sp-reduction-compatibilities in full: clause (3) states exactly the scalar purity square, with direct diagonal/DNC orientations over arbitrary finite rings and the specified exceptional mate. The characteristic, finite type, smoothness, pure dimension, coefficient annihilator and finite-Tor hypotheses are those of the item. This avoids the tempting but invalid citation of the quotient-only finite reduction theorem for a general ring extension.

For Step 4 I checked each equality in order: the f square, naturality of gamma_f at r_g, naturality of the canonical source comparison at gamma_g, then the g square. det-sp-finite-general-ring clause (3) states naturality of the purity family. The displayed intermediate maps have source S H_f H_g K and target G_f G_g S K. The source comparison A_K is kept in the formula before the item's stated identifications, so no ill-typed equality is asserted.

For Step 5 I opened det-sp-composition-comparisons: clause (2) explicitly includes theta_B c_gf = G_f(c_g) c_f S(theta_A), for the counit-normalized actual compositor, and permits arbitrary finite coefficient maps without finite projective dimension. Expanding gamma at the unit gives the rho expression using tensor functoriality, with the g-line preceding the f-line. The S-image of the assumed equality is postcomposed with B; Step 3 identifies its left-hand orientation and Steps 2 and 4 identify its right-hand iterate. The final cancellation is of a named isomorphism, not of scalar extension as a faithful functor. This proves the conditional clause rather than citing a new node restating it.

I checked dimension zero in either factor: the source line is the tensor unit, shifts vanish, and the calculation reduces to the unitors already cited. The identity coefficient map reduces the pasted squares to their unit identifications. For the nonflat case Z/l^2 to F_l the proof uses derived tensor on the full objects but ordinary tensor only on locally free Tate lines; it never tensors an arbitrary exact sequence under a flatness assumption. Empty schemes and the zero coefficient ring give the same unique-arrow identities; no step assumes a nonzero stalk or chooses a basis globally. The final Z/l^r specialization has its canonical unital map, since l^r kills A_1. No statement error or source correction was needed.

## Unfinished work

None within this one-level split. The existing dependency nodes remain the library's tasks; this delivery adds none.
