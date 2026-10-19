# Worker report: lem-sfb-pullback-from-point-comp-monoidal

## Files written

- dag/nodes/sec-proetale-coefficients/lem-sfb-pullback-from-point-comp-monoidal.json: statement node, split, unchanged statement, no exact Mathlib match.
- citations.json: verbatim statements backing every proof-step citation.
- searches.jsonl: receipts written by msearch.py; all searches were actually run and their hits read.
- report.md: this report. prepare.py is a sandbox-only preparation script.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched the read-only slopmaster2 WeilConjectures source by the blueprint id, isMonoidal_upperStarFromPointComp, upperStarFromPointComp, and the pullback-from-point concept; no declaration of the item was found. The exact upstream master reference has AlgebraicGeometry.ProEtale.isMonoidal_upperStarFromPointComp at WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean:352, but its body at line 354 is sorry, so it is not an attachment. Its comparison definition at lines 344–348 agrees with the comparison in the item.

## WANTED

None. The current blueprint, the relevant existing DAG statements, and the generic monoidal and adjunction source files used for checking the computations are available locally.

## Problems found and changes

The imported proof had no actual citations in uses, no judgments for elementary, and an uncited assertion about mates of monoidal transformations. The split now cites the specific statements rather than the aggregate sk-def-sfb-finite-pushforward-pullback (which has no node file here), and writes the mate as three explicitly typed factors. The existing lem-sfb-pushforward-comp-monoidal supplies the geometric tensor calculation for pushforward composition; it is not duplicated. The two elementary equations for composition of monoidal transformations, the whiskering equations, and inversion are written in the item's proof, not made into nodes.

The imported new-blueprint item has no chapter or unit fields and there are no matching sec-proetale-coefficients chapter or sk-def-sfb-pullback-from-point-comp unit records in dag/chapters and dag/units. I read their actual current-blueprint _section.md sources. I did not change maintainer-owned metadata. The unit's route (construct the comparison from pullback composition and prove its monoidality) is preserved.

### Source error in a separate dependency

STATEMENT-DISPUTED: def-sfb-finite-upper-star-comp says that the comparison H=(a f)^* to L=f^* a^* is the conjugate of the *inverse* of c:a_* f_* to (a f)_*. Under the ordinary conjugation convention, Hom(L_2,L_1) corresponds to Hom(R_1,R_2), so c:R to K gives H to L, while c^{-1}:K to R gives L to H. The word "inverse" in that separate node's statement thus reverses the claimed type. Its own proof merely says to take conjugates and does not impose that incorrect direction. The item's current-blueprint proof correctly describes H to L as the mate of c; the comparison the item actually needs is its inverse.

This delivery changes no other worker's node and does not cite the incorrect statement of def-sfb-finite-upper-star-comp. It makes the intended comparison in this item's proof explicit: for H left adjoint to K and L left adjoint to R, b:L to H is v_{HF} composed with L(c^{-1}_{HF}) composed with L(u^H_F). It is exactly the inverse composition comparison whiskered by p^* in def-sfb-pullback-from-point-comp-iso. Thus the item's statement and every target statement remain unchanged. The separate definition needs the indicated maintainer correction.

## What could not be finished

Nothing in this item's split. No Lean was written and no compiler, Lake, or build tool was run. No delivery is pushed by this worker.

## Not duplicates

No new nodes. Whole-blueprint searches for monoidal, conjugate, mate of a monoidal, pullback-from-point-comp, and monoidal natural isomorphism were read, together with whole-DAG searches by these concepts. sk-def-sfb-pullback-from-point-comp is the aggregate definition plus this monoidality assertion, not a separate exact duplicate; def-sfb-alpha-bundled asserts compatibility of a component with ring structure, not the unit/tensor naturality assertion for all abelian sheaves. The existing general site-inverse-image coherence node lem-weil-pbc-left-exact-site-inverse-image-tensor was also read: it concerns a general left-exact continuous site functor and needs explicit site hypotheses/normalizations. It does not remove the need to identify this particular canonical comparison and is not used as a shortcut through another unit.

## Review by Q42

I read the item's current main-20261015 statement and both paragraphs of its .proof.md, the parent unit's _section.md and unit proof, and the chapter's _section.md. The item is not affected by a blueprint_update. I also read the actual master comparison and its sorry proof to distinguish a definition from a completed theorem. No SGA source is used. There is no new node needing a source or edge-case audit of its own.

Step 1 uses the full statements of def-sfb-finite-upper-star-monoidal, sk-def-sfb-sheaf-tensor, and lem-sfb-finite-monoidal-adjunction. The first explicitly says the specified inverse-image structure is strong monoidal and is the mate structure; the tensor node explicitly gives the sheafified integer tensor in Ab; the adjunction lemma explicitly supplies monoidal units and counits. I checked all three morphisms f, pi_Y, and pi_Y f are arbitrary scheme morphisms, which is exactly the generality of those statements. In particular the historical word "finite" in these ids adds no finiteness assumption. The coefficient category is Ab throughout and never a cartesian monoidal category or a category of modules with an unrelated coefficient ring.

Step 2 uses no node: its tensor and unit equations are the defining equations for a monoidal natural transformation. I checked the directions and composite structure maps, and wrote how naturality proves each whiskering operation and how multiplying by inverses proves inversion. It is a direct diagram computation, not an unproved appeal to a general mate theorem. For an independent source check I read Mathlib/CategoryTheory/Monoidal/NaturalTransformation.lean:45–95 and 120–125, which implements these same calculations, and the monoidal composite adjunction instance in Functor.lean:1045–1054. These are corroboration, not extra assertions hidden in a source citation.

Step 3 cites lem-sfb-finite-monoidal-adjunction again for the individual monoidal units/counits, and def-sfb-finite-upper-lower-star-adjunction for the two Hom bijections that define their composite. I checked the composite unit is U(u^B_A) u^A, and the counit is v^B B(v^A_V), so both are whiskered composites of exactly the monoidal maps provided by the cited lemma. This proves monoidality for the *composite* structures using the calculation already written in step 2. It does not infer a theorem from an adjunction definition alone.

Step 4 cites lem-sfb-pushforward-comp-monoidal, which explicitly states monoidality of the canonical fibre-product comparison for arbitrary f,g and closed braided Grothendieck abelian coefficients, including Ab. I opened its statement and proof; g=pi_Y satisfies its hypotheses. It also cites the monoidal adjunction lemma to supply the direct unit u^H and def-sfb-pullback-from-point-comp-iso to fix the particular comparison's direction. I checked every object in b_F: LF goes to L K H F, then to L R H F, then to H F. Thus it is the conjugate of c^{-1} and not of c. Its three natural-transformation factors are all monoidal by steps 1–3. This is the argument missing from the imported proof. As an independent check I read WeilConjectures/CategoryTheory/Monoidal/Conjugate.lean and the underlying unit/tensor conjugation lemmas in WeilConjectures/Mathlib/CategoryTheory/Monoidal/NaturalTransformation.lean, as well as Mathlib's conjugateEquiv convention in Adjunction/Mates.lean:264–281. I did not use those source theorems as an uncited black box. The calculation in the item proves the needed specialization itself. The incorrect direction in the separate definition was detected and corrected locally in this calculation, as explained above.

Step 5 cites lem-sfb-point-upper-star-braided, whose statement expressly includes that p^* is strong monoidal; def-sfb-upper-star-from-point, whose statement gives p_X^*=pi_X^* p^*; and def-sfb-pullback-from-point-comp-iso, whose statement gives the *specified* comparison as the inverse composition isomorphism precomposed with p^*. I checked these statements supply exactly the maps used. I wrote the tensor and unit comparisons after reassociation rather than asserting that an arbitrary identification transports monoidality. The equality pi_Y f=pi_X identifies the specified structures by substitution. This establishes both requested clauses: the unit and tensor diagrams.

For small cases I checked f=id, Y=Spec Z, and X empty. The formulas still have the same domains and codomains; no nonempty scheme, section, affine cover, point, or proper/finite morphism is assumed. On the identity case the mate formula reduces by the triangle identities to the identity comparison. On the tensor unit the proof is the unit equation, not an inference from the tensor equation alone. No exactness or flatness of a tensor product is needed. The split contains no clause-restating child, no new unsplit proof, no circular citation, and no hidden change of coefficients.

Mathlib searches were made only with the prescribed msearch.py and are recorded verbatim from its receipts. Both semantic phrasings were tried. I read the hits: generic monoidal-transformation calculus, adjunction composition, and module/site pullback comparisons do not directly state the pro-étale point comparison with these normalized structures. I also read their relevant local source signatures; the searches finding the generic calculus explain why it is elementary here, rather than warranting another node. All eight searches succeeded; none is falsely recorded as unavailable or absent without a run. citations.json copies verbatim the cited statements, one per step/node pair.

## Second reading by Q42

- Statement: checked against the current `main-20261015` blueprint node and the master Lean declaration `upperStarFromPointComp`; the objects, direction, tensor, and unit clauses agree, with no added finiteness or nonemptiness hypothesis. Verdict: pass.
- Step 1: checked against the verbatim statements of `def-sfb-finite-upper-star-monoidal`, `sk-def-sfb-sheaf-tensor`, and `lem-sfb-finite-monoidal-adjunction`; arbitrary scheme morphisms cover $f$, $\pi_Y$, and $\pi_Yf$, and the coefficient tensor is $\otimes_{\mathbf Z}$. Verdict: pass.
- Step 2: checked the displayed lax-monoidal natural-transformation equations directly, including composition, whiskering, and inversion; the calculation is elementary and has no hidden citation. Verdict: pass.
- Step 3: checked the composite-adjunction unit $U(u^B_A)u^A$ and counit $v^B B(v^A_V)$ against `def-sfb-finite-upper-lower-star-adjunction` and the monoidal-adjunction statement; the marked elementary calculation is the defining two Hom-bijection composite. Verdict: pass.
- Step 4: checked `lem-sfb-pushforward-comp-monoidal` gives $c:UV\to K$, while the required comparison is its inverse mate $b:L\to H$; the three displayed factors have the stated domains and are monoidal by Steps 1–3. Verdict: pass.
- Step 5: checked `lem-sfb-point-upper-star-braided`, `def-sfb-upper-star-from-point`, and `def-sfb-pullback-from-point-comp-iso`; whiskering by $p^*$, reassociation, and the terminal equality preserve both unit and tensor diagrams. Verdict: pass.
- New nodes: none; consequently there were no new statements, sources, or Mathlib leaves to audit. Existing-node searches covered the monoidal comparison, mate, whiskering, and point-pullback terms. Verdict: pass.

I changed only this report section. I rechecked the zero/empty scheme, $f=\mathrm{id}$, and $Y=\operatorname{Spec}\mathbf Z$ cases: all comparison domains and codomains remain defined, and the identity case reduces by the adjunction triangle identities. The separate imported `def-sfb-finite-upper-star-comp` inverse-direction typo remains reported as a source error; this item does not cite that node.
