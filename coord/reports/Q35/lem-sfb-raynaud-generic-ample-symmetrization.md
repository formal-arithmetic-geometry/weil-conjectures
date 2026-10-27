# Stage-1 report: lem-sfb-raynaud-generic-ample-symmetrization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-raynaud-generic-ample-symmetrization.json: item, statement unchanged; four proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-generic-picard-class-lifting.json: statement, unsplit; no Mathlib match. Lifts only a positive multiple of a generic Picard class modulo geometric algebraic equivalence, without positivity or an exact generic isomorphism.
- dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-algebraic-equivalence-norm.json: statement, unsplit; no Mathlib match. Inversion on geometrically algebraically trivial lines and invariance of ampleness under their tensor action, over an arbitrary field on a semiabelian group.
- dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-supplied-norm-ampleness.json: statement, unsplit; no Mathlib match. Relative ampleness of M tensor [-1]^*M for a supplied generically ample M; no extension assertion.
- citations.json: a verbatim statement quote for each citation of each item step.

## Attachments

None. Searched lean/WeilConjectures for the item tag, Raynaud and symmetrisation/symmetrization. Projective.lean:112 and :128 give generic symmetrisation properties for abelian varieties over fields, but neither gives a relative extension and both require proper abelian fibres. The item has no project declaration giving its conclusion.

## Wanted literature

WANTED: Raynaud, Faisceaux amples sur les schemas en groupes et les espaces homogenes, LNM 119 (1970), XI 1.13 and XI 1.16, and the Picard/cube arguments of IV, for this item and the three new nodes. The local PDF named by the imported source does not exist. The publisher table of contents and chapter XI landing page were read online, but show subscription content rather than the proof: https://link.springer.com/chapter/10.1007/BFb0059517 .

WANTED: Moret-Bailly, Pinceaux de varietes abeliennes, Asterisque 129 (1985), II 3.3.3, I 5, VI 3.1, for source verification of the decomposition. The local PDF is absent. The opening paragraph of II 3.3.3, printed p.53, was read through the online primary-source text indexed at https://www.numdam.org/item/AST_1985__129__1_0.pdf . It uses a generic difference of two ample modules and Raynaud to obtain a power extension. It does not itself prove the new Picard-class or nonproper ampleness inputs. These inputs are explicitly agent-formulated unsplit prerequisites; no claim is made that the missing Raynaud proof was read.

## What was wrong or incomplete

The starting node was statement-only with no proof. Its source already acknowledged a missing original and an agent formulation. The supplied-line ampleness and proper-generic ample-model nodes do not furnish the item: the latter assumes properness of the generic fibre, while the item explicitly permits a torus part. Citing them would fail C4. The existing symmetric-line prolongation depends on this item, so using it would make a cycle.

I considered and rejected unrestricted generic Picard lifting. Even for a constant abelian variety over a singular normal base, a rational point of its dual need not extend over the singularity, nor do its nonzero multiples necessarily extend. Thus lifting L itself after taking a power is not a justified intermediate lemma. The new input instead lifts its class modulo geometric algebraic equivalence. Symmetrization removes that discrepancy. This is a correction of a discarded proof idea, not a dispute or change to the imported statement.

## Work left

The three new nodes are deliberately unsplit and require their own stage-1 work. The original source proof remains WANTED. All four item steps are below 2000 characters and the total assembly is below 3000 characters. No Lean was written and no compiler/build tool was used.

## Not duplicates

lem-sfb-semiabelian-generic-picard-class-lifting vs lem-sfb-raynaud-generic-ample-symmetrization: no ampleness hypotheses or conclusions; lifts only a quotient Picard class, not a prescribed generic line or its symmetrization.
lem-sfb-semiabelian-generic-picard-class-lifting vs lem-sfb-raynaud-generic-ample-power-model: does not require generic properness, does not prescribe an exact generic isomorphism, and does not construct an ample model.
lem-sfb-semiabelian-generic-picard-class-lifting vs lem-sfb-symmetric-line-power-prolongation: starts from a generic quotient class without symmetry or positivity and does not extend a specified line on a dense open.
lem-sfb-semiabelian-generic-picard-class-lifting vs lem-sfb-rigidified-line-big-open-extension: its affine neighbourhood contains an arbitrary prescribed base point; the old node only reaches a big open. The new conclusion is modulo algebraic equivalence rather than an exact extension.
lem-sfb-semiabelian-algebraic-equivalence-norm vs lem-sfb-abelian-polarization-calculus: semiabelian, nonproper and arbitrary ground field; only Picard-zero inversion and ample twisting, not representability, a dual abelian variety or a polarization homomorphism.
lem-sfb-semiabelian-algebraic-equivalence-norm vs lem-sfb-algebraically-trivial-line-multiplicativity: the latter is a relative proper group algebraic-space theorem supplying multiplication structure; the new node concerns nonproper semiabelian varieties and ampleness.
lem-sfb-semiabelian-algebraic-equivalence-norm vs lem-sc-ample-tensor: latter tensors two ample lines and gives symmetrization only for an abelian variety; it says nothing about tensoring by a geometrically algebraically trivial line on a nonproper semiabelian group.
lem-sfb-semiabelian-supplied-norm-ampleness vs lem-sfb-raynaud-generic-ample-symmetrization: requires M already supplied on all of G and never constructs a line extending prescribed generic data.
lem-sfb-semiabelian-supplied-norm-ampleness vs lem-sfb-normal-cubical-generic-ampleness: no generic properness and no cubical line input; conclusion is for the inversion norm of M, not for M itself.
lem-sfb-semiabelian-supplied-norm-ampleness vs lem-sfb-regular-group-generic-ampleness: normal base suffices, generic fibre need not be proper, and the conclusion is for M tensor [-1]^*M rather than for a symmetric supplied M.
lem-sfb-semiabelian-supplied-norm-ampleness vs lem-sfb-symmetric-ample-power-extension: no dense abelian open or extension of a given line; requires a line on the whole group and proves positivity of its norm.

## Review by Q35

I read delivery-errors B to E in full, the stage-1 contract and three levels of SETUP, the chapter and unit records, the latest blueprint unit and its direct-image proof. The ancestor tool returns None; I preserved the inherited null ancestor and via chain, filled precise supporting places and searched the whole imported blueprint (Raynaud, generic ampleness, Picard, Neron-Severi, algebraic equivalence, algebraically trivial, symmetr, inversion). Searches of the entire DAG statements and source tags found the related nodes listed above; none supplies the three new statements under their stated hypotheses. I also searched the actual latest blueprint text for these notions. New nodes have statements only, empty proofs/dependencies, and honest Mathlib searches from msearch.py. The ring PicardGroup source explicitly concerns invertible modules over rings and does not supply this scheme-theoretic specialization theorem. Semantic hits about affine structure-sheaf sections, elliptic-curve point negation, convex ample sets and residue-field pullbacks were read and rejected; second phrasings were tried.

For the item source, I read Moret-Bailly II 3.3.3 online; Raynaud XI is unavailable locally and behind the publisher subscription page, so the proof_origin is agent. For each new node the report and source field explicitly distinguish the agent prerequisite from a verbatim source theorem. The first is the quotient-class part needed before norm cancellation, the second is the field-level Picard-zero calculation, and the third is supplied-line positivity. Their proof sketches are not inserted into their statements. Future workers must supply the missing literature proofs; stage 1 does not certify these nodes as proved.

Step 1 cites only the quotient-class lifting node. I checked its arbitrary point, affine neighbourhood, normal integral locally Noetherian base, smooth separated finite-presentation commutative group and semiabelian-fibre hypotheses. Its conclusion says exactly that the discrepancy T is geometrically algebraically trivial; the step claims no exact lifting. Nonempty opens in an integral base contain the generic point. The input group hypotheses are reproduced verbatim in the new node.

Step 2 cites positive-tensor-power ampleness and clause (ii) of the field-level node. The first says a positive tensor power of an ample line is ample. The second applies to G_eta over K, not to a proper abelian replacement: all its field and semiabelian hypotheses are present. Tensor evaluation identifies M_eta with L^n tensor T, so it proves M_eta ample. I did not infer ampleness from tensoring an ample line with an arbitrary line.

Step 3 cites the full tensor/pullback statement and clause (i) of the field-level node. The former explicitly gives invertibility, pullback of tensors, composition and tensor permutation. Inversion commutes with the generic-fibre map because it is over the base. These are exactly the facts needed in the displayed formula. The latter explicitly gives T tensor [-1]^*T trivial over K, rather than only after an algebraic closure. Interleaving the remaining n copies gives Sigma(L)^n. The dual and evaluation here are the defining inverse-line operations, not a hidden existence lemma.

Step 4 cites supplied-norm ampleness, whose statement explicitly has no generic-properness assumption and gives ampleness over every affine base open. M is actually supplied on G_W by step 1, and step 2 establishes its generic ampleness. Its output applies to the exact Q from step 3. The final affine cover is the collection of the neighbourhoods constructed around every base point; no global uniform exponent is asserted or needed.

Small cases: for a field base, class lifting can use M=L and n=1 and supplied-norm positivity becomes ordinary symmetrization. For split tori the geometric Picard group is zero and the trivial line is ample on the affine torus, consistent with all three conclusions. The statements allow non-split tori and imperfect fields explicitly, so the field calculus must include descent over K; a geometric isomorphism alone would not be silently substituted. Dimension-zero groups and characteristic two cause no division by 2; the final exponent is a positive integer, with no invertibility condition. Normal but nonfactorial bases do not give Cartier closures for free; no step invokes such an inference. The quotient-class formulation excludes the false exact lifting shortcut noted above. Neither new relative input is an ampleness-preserving extension of the prescribed symmetrized line by itself: existence modulo equivalence and positivity of a supplied line are separate, and their assembly computes an actual generic isomorphism.

Tool uses are the existing positive-power and invertible-pullback-tensor results: generic tools, not changes to the unit route. There are no SGA sources in this split. Verbatim citations were reread against every cited statement; all proof dependencies equal the union of the uses. Required server dry run and delivery follow this report.

Final reread: explicitly introduced X in the inline algebraic-equivalence convention and added the existing properness, finite-type, algebraic-closure and base-change definition nodes to all new statements. These are statement dependencies only. Rechecked all quotes after this clarification.
