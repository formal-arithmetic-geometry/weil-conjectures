# Stage 1 delivery: lem-sfb-finite-cover-stack-algebraic

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-cover-stack-algebraic.json: item, statement, split by the multiplication-table / smooth-groupoid route of Stacks 05YQ. Its statement and statement dependencies are unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-unit-framed-algebra-smooth-groupoid.json: new statement-only lemma, unsplit, no Mathlib match. It states the explicit scheme of algebra laws with unit e_1 and its smooth scheme of arrows, including the point-groupoid identification. It does not assert algebraicity of any stack or a comparison with covers.
- citations.json: one literal statement quote for each node in every proof step's uses list.
- searches.jsonl: actual search-command log; required searches were run for the item and new node, with alternative semantic phrasings.

One new node; zero Mathlib leaves.

## Attachments

None. Project-source searches under lean/WeilConjectures for the blueprint id, finite-cover stack, finite Hilbert stack, representFAd and algebraic-stack notions found no declaration stating this item. Broad finite-cover hits concern ordinary covers and sheaf cohomology, not a moduli stack. No sorry declaration is counted as completed.

## WANTED

None. All sources used are present under literature/stacks-project.

## Corrections and scope

No statement dispute, source correction, changed target, changed unit route, or change of the item's mathematical statement. This sandbox initially had only dispatcher brief markers and no node, report or search log; the live unsplit item was the starting copy.

The point-groupoid convention is made explicit to avoid an arrow-direction ambiguity in the source prose: an arrow m to m' labelled g obeys m'=g^{-1}m(g tensor g), so g is an algebra isomorphism from m' to m. Relative Spec reverses this algebra map and therefore gives the desired scheme arrow from Spec(m) to Spec(m'). Successive labels g,h compose as gh. The new statement writes composition as c((h,m'),(g,m))=(gh,m); this agrees with c(a,b)=a composed with b in the existing groupoid definition.

The new node is not split. Its future proof follows the equations in criteria.tex: associativity, commutativity and the chosen unit are precisely the displayed polynomial relations; the principal-open matrix scheme represents invertible matrices fixing e_1. Its coordinate scheme is a determinant principal open in affine space, not an arbitrary closed subgroup of GL_d, so smoothness does not follow merely from closedness. Matrix inverse entries are cofactors divided by the determinant; substitution in g^{-1}m(g tensor g) therefore defines a regular morphism. Composition and inverse satisfy the groupoid laws by matrix multiplication. Source is a base change of the smooth matrix scheme and target differs from source by groupoid inversion. These are the contents isolated in the new node, not hidden assumptions of the item's assembly.

## Not duplicates

The whole current DAG and latest blueprint were searched by 05YQ, 05YP, represent-FAd, free d-dimensional algebra, multiplication table, unit-framed, first basis vector, algebra structures, commutative algebra laws and unit stabilizer. No existing node cites 05YP or states this explicit unit-framed algebra-law groupoid. Whole-blueprint searches using tools/blueprint_refs.py for 05YP, 05YQ, multiplication table, finite locally free algebra, unit stabilizer and commutative algebra laws found no equivalent statement. The latest blueprint's unrelated multiplication-table occurrences concern descent of function fields and normalization. The item is the only existing statement with source tag 05YQ. No existing/new pair shares the new source tag 05YP.

lem-sfb-unit-framed-algebra-smooth-groupoid vs lem-sfb-smooth-groupoid-fppf-quotient: the existing theorem assumes a smooth groupoid and proves algebraicity of its stackification; the new lemma constructs a particular smooth groupoid by equations and identifies its points with algebra laws. It does not form the stackification.

lem-sfb-unit-framed-algebra-smooth-groupoid vs lem-sfb-affine-action-stack-presentation: the existing statement is about a given smooth affine finite-type group over a field acting on a given affine finite-type scheme, and properties of its quotient; the new statement is the explicit unit-stabilizer/multiplication-table construction over arbitrary base schemes, before any quotient.

lem-sfb-unit-framed-algebra-smooth-groupoid vs lem-sfb-finite-cover-stack-algebraic: the new lemma says nothing about finite covers, effective descent, or stack algebraicity. The item still proves the relative-Spec comparison, full faithfulness, local essential surjectivity with a unit-adapted basis, and the stack equivalence.

lem-sfb-unit-framed-algebra-smooth-groupoid vs lem-pc-finite-free-map-residue-localization: the existing lemma concerns local splitting of module maps, not representability of algebra laws or a groupoid. That lemma is unnecessary here: the unit-adapted basis follows directly from a unit coordinate and its determinant, written in the item's step 4.

## Review by N6

I read criteria.tex section-hilbert-point, including all multiplication-table equations, the group scheme/action construction, Lemma 05YP and Proposition 05YQ with its complete proof. For the new lemma the same source supplies each part of its statement; I used its equations directly over S so no separate algebraic-stack base-change theorem is silently needed. I also read algebraic.tex 04TK (the smooth-groupoid theorem), morphisms.tex 01SA (the affine-scheme / quasi-coherent-algebra anti-equivalence), constructions.tex 01LX (relative Spec base change), morphisms.tex definition-finite-locally-free and lemma-finite-flat (02KB), examples-stacks.tex 05WB (finite-Hilbert stack descent), and stacks.tex 02ZP/0436 (stackification properties/universal property).

For step 1 I opened lem-sfb-smooth-groupoid-fppf-quotient and checked its actual hypotheses: its base can be any S, U is a scheme and R an algebraic space, and both s and t must be smooth. The new lemma supplies exactly these for U=X and R=G times_S X. This does not use the flat-groupoid theorem, which would lead back to the parent algebraicity argument. I checked the existing smooth-groupoid theorem's dependency list for that circularity.

For step 2 I opened lem-weil-pbc-affine-morphism-relative-spec and read clauses (2) and (3), which supply the object and reverse direction on arrows. lem-weil-pbc-finite-free-algebra-spectrum supplies finiteness, flatness and local finite presentation on affine opens without Noetherian hypotheses. The degree is checked from the d-dimensional residue algebra using def-pc-finite-locally-free; it is not incorrectly attributed to a node that states only finiteness. lem-weil-pbc-relative-spec-base-change gives the algebra-compatible comparison for arbitrary scheme base changes. The free module pulls back to the free module and the coefficients pull back entrywise, giving the functor on restrictions and the stated contravariant arrow direction.

For step 3 the anti-equivalence node's clause (3) gives every T-isomorphism, not merely an injection from matrix arrows. I wrote the elementary matrix argument for Hom(O_T^d,O_T^d): a module map is determined by the images of the standard global sections. This works on nonaffine T and preserves composition. Unit and multiplication conditions give precisely the displayed algebra-law arrows. This step is elementary relative to the cited anti-equivalence, not a new lemma.

For step 4 I opened lem-pc-flf-properties: its statement supplies both the rank-d locally free pushforward and the identification of its residue algebra with the fibre algebra. Positive d is used exactly to show the unit is nonzero on the residue fibre. I wrote the determinant of (1,e_1,...,omit e_j,...,e_d) as plus or minus u_j, so no uncited basis-extension theorem is used. The definition node def-weil-finite-integral-morphism explicitly includes that a finite morphism is affine; the anti-equivalence therefore reconstructs the original cover, and def-pc-fppf-site includes Zariski open coverings as the applicable fppf coverings. I do not claim a map factors through an open merely from its point-set image: the neighbourhood used is the actual principal open on which u_j is invertible.

For step 5 I opened lem-sfb-finite-hilbert-stack-descent, which states stack descent for every F; identity of the terminal represented stack meets its hypotheses. I opened lem-sfb-groupoid-stackification-local-description: it states the isomorphism-sheaf comparison, local origin of objects, and extension to any stack. The proof uses exactly these, and writes the extra descent argument that proves an equivalence; it does not pretend that the node's statement already asserts that equivalence criterion. On a common cover the relevant Hom presheaves are sheaves by step 3 and the cover-stack descent result. Full faithfulness is then local; unique lifted comparisons satisfy the cocycle condition, so Q's effective descent glues local object lifts. The last algebraicity transfer is through the resulting equivalence and the definition of algebraic moduli stack, whose representable diagonal and atlas predicates I read.

I checked every citations.json quote against the actual statement string. The item and all new statements are self-contained, and every cited step node is present and unmerged. The four off-unit scheme tools are declared in split_report.tool_uses, with reasons; they do not replace any six-functor unit step. The source provenance's null nearest blueprint ancestor and via chain are preserved, as tools/blueprint_refs.py ancestor reports None. I read latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md: this is a supporting finite-cover-moduli fact on the already-recorded alteration/moduli chain, not a new compactification route. No chapter/unit record is changed.

Small cases: d=1 makes X and G equal to S, as the unit fixes the unique rank-one multiplication, and the cover stack is terminal. For empty S or T the statements are vacuous on points and the relative constructions are empty as expected. The matrix inverse and coefficient construction work over rings with nilpotents and in every characteristic, without dividing by d or inverting any characteristic. The only division in the local basis argument is by u_j after restricting to D(u_j). No d=0 case is asserted; positivity is needed by the proof. No step exceeds 2000 characters. I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the written nodes: one smaller coordinate lemma, no copied clause of the item, no proof in a new unsplit node, no unrun searches, no hidden standard comparison, no SGA source.

## Unfinished work

No part of this one-level split remains unfinished. The new coordinate-groupoid lemma is intentionally statement-only and joins the normal stage-1 queue.
