# Q18 — lem-sfb-algebraically-trivial-line-multiplicativity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-algebraically-trivial-line-multiplicativity.json: the existing statement, unchanged, split into eight proof steps. No Mathlib match.
- citations.json: thirteen verbatim statement quotations, one for each cited node in each proof step.
- report.md: this report and direct-delivery self-review.

There are no new nodes and no Mathlib leaves. The local searches.jsonl contains the actual five Q18 msearch.py results; those queries were appended to the item's inherited search record. The sandbox also contains the PDF text extract and the item-specific writing script; neither is a delivered project file.

## Attachments

None. I searched the project's WeilConjectures/ for the exact blueprint tag and for algebraic triviality, square/multiplicativity, Picard and abelian-variety terminology. The abelian-variety source covers geometric integrality and field constructions, but gives no declaration of this arbitrary-parameter, relative algebraic-space statement. I read AbelianVariety/Basic.lean: its geometricallyIntegral declaration belongs to the existing lem-sc-abelian-variety-characterization, which is reused rather than reattached. A full relative statement was not inferred from a field declaration or from a declaration with sorry.

## WANTED

WANTED: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, Chapter 6, section 2, for the item's inherited relative theorem-of-cube/Picard-kernel reference. The PDF is absent and I do not claim to have read it. This delivery supplies an agent-written assembly using available Stacks sources and existing DAG nodes; the unavailable text is not an uncited black box.

## What was wrong and what changed

The live item was a statement-only prerequisite created by Q140 for lem-sfb-abelian-picard-infinitesimal-lift. The sandbox contained only dispatcher markers, with no earlier item, split, report or search log. I copied the current node and retained its statement, source, lineage and existing Mathlib searches. There is no statement dispute and no hypothesis change.

Milne I Proposition 8.4(c), printed p.36, is a field assertion about Pic0, and cannot itself supply multiplicativity over nonreduced or non-Noetherian parameter schemes. Also, calling equality on geometric points equality of morphisms would lose nilpotents. The proof supplies both missing arguments: the field statement follows along the very chains defining algebraic equivalence by the theorem of the cube, and finite-image factorization plus canonical global functions proves vanishing of the actual relative Picard-class map. It uses the full rigidified Picard space P, not the dual abelian space. In particular it does not cite lem-sfb-abelian-space-poincare-calculus, its neutral-component conclusions, or the infinitesimal lifting theorem that depends on this item.

I read the chapter and unit DAG records and the current sk-thm-sf-ctf-stability statement/proof through literature/blueprint/latest (main-20261023-1620, 7284bb09). The newest unit uses perfect local models and compactification for direct images. This inherited ancillary Picard prerequisite does not alter that unit or the chapter. blueprint_refs.py ancestor returns None; the item's null ancestor and existing via chain are retained. Whole-blueprint searches for the exact multiplicativity phrase, rigidified, algebraically and multiplicative, together with searches in latest/, found no equivalent statement, so same_as remains empty.

## Not duplicates

No new node was created. The whole-DAG searches found existing inputs for every non-elementary step. In particular:

- lem-sc-general-theorem-of-cube states exactly the field product theorem needed for the algebraic-equivalence parameter. I did not create another field multiplicativity clause.
- lem-sfb-rigidified-space-picard supplies both full rigidified representation and the universal structure-sheaf isomorphism. I did not create another Picard or universal-functions node.
- lem-sfb-proper-space-finite-image-neighbourhood supplies an actual closed finite factor, not merely finite image of points; lem-sfb-space-affine-target-global-functions supplies the required affine-target injectivity. I did not create a product-slice or relative rigidity node.
- lem-trf-scheme-etale-invertible-comparison is the existing ordinary/etale line-module equivalence. The operation comparisons needed here are written as elementary transition-unit calculations.

## Review by Q18

I read Milne, Abelian Varieties I Proposition 8.4 and Remark 8.5, printed pp.36–37. The proposition proves translation-invariance equivalent to the displayed field multiplicativity, rather than proving the relative assertion in this item. I therefore read Stacks more-morphisms.tex, theorem-of-the-cube (Tag 0BF4), including its statement and proof. Its two slices and one fibre hypothesis are precisely what the normalized difference of an algebraic-equivalence family supplies in Step 4. The parameter variety needs connectedness, not properness. There is no appeal to an unspecified identification of algebraic equivalence with Pic0.

For the relative argument I read quot.tex, lemma-flat-geometrically-connected-fibres-with-section (0D28), the rigidified functor/stack discussion (0D2B), and proposition-pic-functor (0D2C); spaces-perfect.tex, lemma-proper-flat-geom-red-connected (0E0S); spaces-more-morphisms.tex, lemma-flat-proper-family-cannot-collapse-fibre (0AEJ), including its proof by scheme-theoretic image; and spaces-properties.tex, lemma-morphism-to-affine-scheme (05Z1). These are the available sources for the existing generic prerequisites. No SGA source is used.

Step 1: I opened the statements of lem-pc-smooth-flat, lem-sc-abelian-variety-characterization and lem-sfb-rigidified-space-picard. The first is applied on scheme charts only. Each geometric fibre is a scheme satisfying the second's proper, smooth, connected group hypotheses. The residue-field formulation is checked by passing to an algebraic closure, descending reducedness on etale charts and irreducibility through the surjective point map. Thus the third's locally Noetherian base, properness, flatness, finite presentation, geometrically integral fibres and section hypotheses all hold. Its statement explicitly supplies a separated locally finitely presented P and the canonical structure-sheaf isomorphism for EVERY scheme parameter; no hidden claim from its proof is used.

Step 2: I opened lem-trf-scheme-etale-invertible-comparison. Its statement gives the equivalence and the trivial-object identification, but explicitly writes pullback compatibility only for etale maps. I corrected that potential C4 issue by writing the tensor/dual/arbitrary-pullback comparisons out on frames: product, inverse and pullback of transition units are identical for the ordinary and etale constructions, so the local comparisons glue. The step is elementary relative to the quoted equivalence and does not pretend the cited node states the stronger pullback clause.

Step 3 is the formula for N(L). I checked both axes, including the e-line factor and agreement at (e,e). This extra factor is necessary when L is not rigidified and is essential for applying the construction to an arbitrary generating family. Cancelling the indicated evaluation pairs, and base-changing the formula, are elementary. I did not replace a real construction with an unspecified Picard object.

Step 4: I opened the FULL statement of lem-sc-general-theorem-of-cube. Its X,Y are proper geometrically integral schemes over a field; these are B=A_Omega from Step 1. Its x,y are the identity rational points. Its Z is exactly the connected smooth parameter variety of one generating pair. Step 3 supplies both entire slice trivializations, and the induction hypothesis supplies the trivial residue-field fibre at one endpoint. The theorem trivializes N(F) on the entire product; restricting at the other endpoint is elementary. The reverse implication uses the same theorem with endpoints exchanged. The finite-chain induction starts at the trivial line and is stable under isomorphism. Thus all geometric-fibre hypotheses in the item's own definition of algebraic triviality are used, and the field multiplicativity argument remains in the proof instead of being moved to a restatement node.

Step 5: I opened the algebraic-space-parameter and base-change clauses of lem-sfb-rigidified-space-picard. They apply to the parameter C=A_T, even if C is not a scheme and T is not locally Noetherian: the base to which the node was applied is still the original locally Noetherian S. The line N(M) on C times_T C, rigidified in its first coordinate, therefore defines h:C to P_T. The other axis makes h(e)=0. Step 4 trivializes the whole difference on each geometric fibre, not just its geometric point restrictions. A trivialization can be normalized along e times B by the explicitly written parameter-unit rescaling, so the corresponding rigidified class is zero and h_Omega=0 as a morphism.

Step 6: I opened all three cited statements. lem-sfb-space-flat-proper-fp-locality supplies properness of C over the original arbitrary T. The separated target condition is checked directly from the diagonal: on tests the base change of R to R/I is the quotient by the extended ideal. lem-sfb-stack-chartwise-smooth-etale-calculus explicitly preserves local finite presentation under base change and states that it implies local finite type; it is used for P, not to assume P smooth. The finite-image node requires proper source, separated locally finite type target, and finite geometric-fibre image, with NO Noetherian, reducedness or flatness restriction on T. Those hypotheses have just been checked. Its statement gives an actual factorization through an affine finite scheme Z after an affine open shrink around each point. I checked 0AEJ case (3)(a), rather than replacing factorization by set-theoretic containment.

Step 7: I reopened the universal-functions clause of the Picard node and the full statement of lem-sfb-space-affine-target-global-functions. The functions isomorphism is specifically p-pullback, not an abstract ring isomorphism, so the identity section induces its inverse. Both maps a and bp have the same pullback of functions, as the displayed equation shows, and 05Z1 gives equality because Z is affine. Composing with j and using h(e)=0 gives h_V=0. This equation is checked in the full rings, so it proves the nilpotent assertion rather than discarding it.

Step 8: I opened def-trf-algebraic-space, which makes P_T a sheaf, and the Picard classification for space parameters again. Equality is local on the open cover of T and can be checked on every scheme test of C. The zero morphism classifies the trivial rigidified family, so N(M) is trivial globally. Finally r removes its base factor and tensor evaluation gives exactly the isomorphism in the item. This is elementary assembly from the preceding assertions.

I checked sections B–E against the files. There are no new statements to leave with incomplete hypotheses, unrun searches, or hidden proofs. Every proof use has an exact statement quote in citations.json. No step exceeds 2000 characters (lengths: 1058, 724, 707, 999, 859, 979, 636, 681), and each is one argument described above; there is no long step concealing an uncited lemma. The off-unit generic tools (the cube and ordinary/etale comparison) are explicitly declared in split_report.tool_uses. The latter is foundational line-module descent, not an appeal to the trace formula, so the chapter name alone does not create a route through that theorem.

Small cases checked: T empty is vacuous and the sheaf/classification conclusion remains valid; the zero-dimensional abelian family is the identity group and N(M) cancels directly; the trivial module is the induction base; a nontrivial base line factor is cancelled by q*e*L in N(L). Characteristic 2 and positive characteristic introduce no divisions or sign arguments. For T=Spec(k[epsilon]/epsilon^2), Step 7 is still an equality in rings with epsilon, so the argument controls infinitesimal parameters. Arbitrary non-Noetherian T enters only through base change and the unrestricted finite-image and global-functions statements. The proof never assumes that A_T is a scheme or projective, or that the relative dual is already constructed.

## Unfinished work

The item is split using existing DAG prerequisites. No new nodes remain to split. No Lean file was written and no compiler, Lake or build command was run. The required server dry run and direct push are the only delivery operations.
