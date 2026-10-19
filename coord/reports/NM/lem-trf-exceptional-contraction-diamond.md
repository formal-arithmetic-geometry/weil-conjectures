# Stage-1 report: lem-trf-exceptional-contraction-diamond

## Files written

- dag/nodes/sec-trace-formula/lem-trf-exceptional-contraction-diamond.json — corrected statement and eight-step split.
- dag/nodes/sec-trace-formula/lem-trf-closed-union-pushout.json — statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-relative-nodal-point-pinching.json — statement, unsplit; no Mathlib match.
- citations.json — verbatim statement quotations for every proof-step citation.

## Attachments

None. I searched WeilConjectures/ in the supplied slopmaster2 checkout for the item tag, exceptional contractions, diamonds, pinching and closed-union pushouts. No declaration states this item or either new node. The project Gluing.lean results found concern open immersions, not these closed intersections. No Lean was written or compiled.

## Wanted literature

WANTED: Michael Temkin, Stable modification of relative curves, arXiv:0707.3953v3, Appendix B, printed p. 58, for lem-trf-exceptional-contraction-diamond. The archival path literature/temkin-stable-modification-arXiv-0707.3953v3.pdf is absent. I read the primary PDF online at https://arxiv.org/pdf/0707.3953 (PDF page 58); the original HUJI URL timed out. The local diamond argument is agent-written, not represented as a quoted proof of B.3. All Stacks sources below are present locally.

## Statement correction — STATEMENT-DISPUTED

The original item claimed properness of every elementary pushout even for an arbitrary reference morphism r. This is false when the curve is not separated over k.

Let Q be the affine line with doubled origin o_1,o_2, obtained by gluing two copies of Spec k[t] along D(t). Attach A=P^1 to Q by identifying 0 in A with o_1 and infinity in A with o_2. These attachments are ordinary nodes; P is a finite-type semistable curve, with empty marking, and A is a closed exceptional component with exactly two special points. Let r:P→A^1 be t on both copies in Q and zero on A. P is connected and r(P)=A^1, so the imported noncollapse condition holds.

Its pushout along A→Spec k is A^1. Indeed a map from P constant on A gives maps from the two copies of A^1 in Q agreeing on D(t) and with the same value at their origins. Near that common value take an affine target neighbourhood. The two induced ring maps agree after inverting t and hence agree before localization, since k[t] has no t-torsion; their maps consequently agree near zero as well as on D(t). They define a unique map from A^1. Thus this is a scheme pushout, the quotient is smooth, marking transport is vacuous, and r factors. But P→A^1 is not separated: the two maps A^1→P through the two copies in Q agree away from zero and have distinct values o_1,o_2 at zero. Their equalizer D(t) is not closed. Therefore this supplied elementary contraction is not proper.

I restored **r proper**, the standing assumption in Temkin's paragraph immediately preceding B.3 (proper surjective morphism of connected curves). Surjectivity onto C, connectedness, and separatedness or properness over k are unnecessary for this local argument and have not been added. The conclusion now explicitly records properness of the remaining reference morphism, needed to repeat the construction. The old statement and the reason are preserved in split_report.statement_correction.

DOWNSTREAM: lem-trf-valuation-stable-blowdown-uniqueness currently invokes this item under an arbitrary-reference-map statement. That invocation must now justify properness of its reference map, or its own statement must be reformulated. It is outside this delivery and was not edited. In the original Temkin application the reference morphism is proper. This is a correction of an overgeneralized imported auxiliary statement, not a change of the chapter/unit route.

## Review by NM

I read the chapter and unit records, the current main-20261015 local-term-locality proof, and the item's recorded ancestry. This item supplies the elementary-contraction part of the Temkin semistable-alteration branch; it does not alter the trace-class route or use SGA. I read Temkin Appendix B, especially the proper-reference hypothesis, the elementary pushout paragraph and B.3. The reference-map hypothesis was the substantive error I corrected. I also compared the existing stable-blowdown caller and explicitly flagged its now-missing hypothesis above.

For the new closed-union node I read morphisms.tex Tag 0C4J (lemma-scheme-theoretic-union), including its affine-local proof. I checked that the existing lem-weil-pbc-scheme-theoretic-union only constructs the union, describes its support and supplies its closed inclusions: its statement does NOT supply the cocartesian property needed here. That is why I did not cite its proof as if it were its statement. The new node gives the missing general universal property and does not restate a rational-component contraction or any diamond clause. It remains statement-only.

For the new pinching node I read more-morphisms.tex Tags 0E25 and 0E26, curves.tex Tag 0E36 and the glueing-points example 0C1J, varieties.tex Tag 09NN, and morphisms.tex Tag 03GN. Over an affine neighbourhood in S, properness makes X separated over that affine neighbourhood and hence over k. The finitely many boundary points then have a common affine neighbourhood by 09NN. Thus the affine-neighbourhood condition of 0E25 is available without assuming global separatedness over k. The fibre-product sheaf gives the displayed completed local ring and cartesian boundary square. Finite pinching is an isomorphism away from E. Restricting to a reduced subcurve meeting each pair at most once gives the one-branch quotient at a pinched point, so the restriction is a closed immersion, not merely injective on points. The resulting quotient is separated over S by 0E26, finite type over k, therefore locally finite type over the arbitrary k-scheme S; universal closedness descends from X by 03GN. This checks the properness clause without imposing a Noetherian hypothesis on S. These are geometric pinching inputs, strictly below the rational-component calculation, and this new node also remains statement-only.

For Step 1 I opened the statements of lem-trf-nodal-geometric-fibres-reduced, lem-trf-nodal-subcurve-boundary, the new closed-union pushout, and lem-weil-pbc-closed-immersion-proper. The first applies to the finite-type geometric nodal fibres in the semistable definition. The boundary lemma really gives reduced finite boundary, nodality of Q, and smoothness on both sides; it does not assume properness over k. The last gives Q proper over C because it is a closed subcurve of P proper over C. The intersection of the two closed-subcurve ideals is zero by reducedness. Noncollapse excludes empty boundary. These verify d=1 or 2 and m+d≤2 before any contraction is used.

For Step 2 the pinching node is applied to Q proper over C with its reduced smooth boundary and the constant morphism Spec k→C. I wrote out the Laurent-polynomial argument from the two charts in def-sc-p1-standard to justify that a singleton-image morphism from P^1 really factors through Spec k. The previous step has already established P=Q amalg_E A; the two universal properties now explicitly give the contraction pushout. Uniqueness of a colimit identifies an arbitrary supplied contraction with this constructed one, so subsequent statements apply to the supplied maps, not just a chosen model.

For Step 3 the pinching statement supplies the complement isomorphism, the smooth or nodal local model, and properness of Y→C. I checked the local pullback maximal ideal is the complementary-branch ideal (x), so the fibre is A itself, not an unspecified thickening. The cited lem-weil-pbc-proper-to-separated says precisely that a map from a scheme proper over C to a C-separated target is proper; both hypotheses were established. The definition of semistable pointed pair supplies the smooth-marking condition, and the cases d=1,m≤1 and d=2,m=0 are written separately. No hidden marking collision is allowed.

For Step 4 I used only the already-proved properness, surjectivity and connected fibres, the pinching properness clause, and the definitions of proper and connected. I wrote the finite clopen-component argument: properness makes images closed, connected fibres make them disjoint, and finite union makes them open. This proves connected-component noncollapse on the quotient rather than assuming it.

For Step 5 the boundary node gives actual reduced intersections and rules out a third branch at a node. Two common nodes would use all boundary points on A and B, making their union a whole connected component with singleton reference image, contrary to the hypothesis. Thus each pinching fibre meets B at most once, exactly the hypothesis of the pinching node's subcurve-embedding clause. I verified this yields a closed embedding and an irreducible component, not just an abstract normalization or bijection.

For Step 6 the pinching node's one-point and two-point descriptions give all three possibilities at the old common node: smooth unmarked, smooth marked, or node unmarked. I checked the special-point count in each case, including a marked tail. The two intermediate reference maps have already been proved proper and componentwise nonconstant in Step 4, so repeating the construction on B_A and A_B is legitimate. This is an application of the argument already written in this item's earlier steps, not a citation of an unstated contraction-existence theorem.

Steps 7 and 8 use only the pushout definition, read in def-weil-pbc-category-colimit. I constructed both comparison maps by their successive universal properties. I checked cancellation directly, using a k-point section of the contracted projective line to recover the point leg from the curve leg. This proves epimorphism and the two inverse identities; it avoids assuming that arbitrary surjective scheme morphisms are epimorphisms. Marking and reference compatibilities follow from the same uniqueness equations, and the final j_B is explicitly transported through the resulting isomorphism.

I tested the statement and new inputs with empty marking, disconnected curves, a single marked tail, two disjoint tails, an adjacent tail and bridge, two adjacent bridges and a triangle with a third noncontracted component. Two components meeting twice are excluded by noncollapse, not treated as a valid exceptional chain. Empty E=F in the pinching node gives the identity; a one-point fibre leaves its smooth point unchanged; a two-point fibre on the same remaining component creates a self-node and is allowed (the subcurve-embedding clause appropriately does not apply to that entire component). The doubled-origin example above tests precisely the removed arbitrary-reference generalization. No properness over k is used in the corrected proof.

For the B–E audit: the two new files have self-contained statements only, no proof sketches or dependencies on their parent's theorem; their definitions are cited, their TeX is singly escaped in JSON, and their sources name actual Stacks tags and labels. Mathlib searches were made through msearch.py only and read as returned; all are available and none is a match. Natural-language queries were rephrased, and closed intersections were distinguished from the open-gluing hits. I searched the full DAG, blueprint and supplied Lean checkout before creating them. citations.json contains exact quotations from each cited statement; there is no reliance on an existing node's proof or a definition for a theorem it does not state. No step is over 2000 characters; the closed-gluing and pinching comparisons were extracted instead of concealed in a long step. Tool uses from other units are declared in split_report. Neither unit realizations nor another worker's files were changed.

## Not duplicates

lem-trf-closed-union-pushout vs lem-trf-nodal-contraction-euler-defect: This new statement supplies the universal property of the union, whereas the existing statement concerns Euler defect of contracting a nodal subcurve to a smooth point. In particular the existing union-construction node gives support and closed inclusions only, not a pushout.

lem-trf-closed-union-pushout vs lem-weil-pbc-scheme-theoretic-union: This new statement supplies the universal property of the union, whereas the existing statement concerns Scheme-theoretic union of two closed subschemes. In particular the existing union-construction node gives support and closed inclusions only, not a pushout.

lem-trf-closed-union-pushout vs lem-weil-pbc-closed-subset-proper-over-base-properties: This new statement supplies the universal property of the union, whereas the existing statement concerns Closed subsets proper over a base: any scheme structure, closed subsets, images. In particular the existing union-construction node gives support and closed inclusions only, not a pushout.

lem-trf-relative-nodal-point-pinching vs lem-sc-dual-number-scheme-pushout: The new statement constructs the finite nodal point-identification quotient and specifies its branch local rings and subcurve embeddings; the existing statement concerns Spec of the square-zero algebra $K[\epsilon_1,\dots,\epsilon_n]$ is the pushout of $n$ copies of the dual-number scheme and does not construct this quotient.

lem-trf-relative-nodal-point-pinching vs lem-weil-pbc-proper-closed-in-proper-fp: The new statement constructs the finite nodal point-identification quotient and specifies its branch local rings and subcurve embeddings; the existing statement concerns A proper scheme over a qcqs base is a limit of proper finitely presented schemes along closed immersions and does not construct this quotient.

lem-trf-relative-nodal-point-pinching vs sk-thm-picard-main: The new statement constructs the finite nodal point-identification quotient and specifies its branch local rings and subcurve embeddings; the existing statement concerns The Picard scheme and Jacobian of a geometric curve and does not construct this quotient.

lem-trf-relative-nodal-point-pinching vs lem-weil-pbc-closed-subset-proper-over-base-universally-closed-image: The new statement constructs the finite nodal point-identification quotient and specifies its branch local rings and subcurve embeddings; the existing statement concerns Image of a closed subset proper over a base under a universally closed morphism and does not construct this quotient.

lem-trf-relative-nodal-point-pinching vs lem-pc-bounded-complex-tensor-proper-support-bound: The new statement constructs the finite nodal point-identification quotient and specifies its branch local rings and subcurve embeddings; the existing statement concerns Proper closed bound for supports of a bounded tensor and does not construct this quotient.

lem-trf-relative-nodal-point-pinching vs lem-weil-pbc-proper-closed-in-proper-fp-envelope-part: The new statement constructs the finite nodal point-identification quotient and specifies its branch local rings and subcurve embeddings; the existing statement concerns Proper finitely presented closed envelope and does not construct this quotient.

lem-trf-relative-nodal-point-pinching vs thm-sc-theorem-of-the-base: The new statement constructs the finite nodal point-identification quotient and specifies its branch local rings and subcurve embeddings; the existing statement concerns The theorem of the base and does not construct this quotient.

lem-trf-relative-nodal-point-pinching vs thm-pc-hilb-curves: The new statement constructs the finite nodal point-identification quotient and specifies its branch local rings and subcurve embeddings; the existing statement concerns Hilbert schemes of smooth projective curves and does not construct this quotient.

lem-trf-relative-nodal-point-pinching vs lem-sc-picg-geometrically-integral: The new statement constructs the finite nodal point-identification quotient and specifies its branch local rings and subcurve embeddings; the existing statement concerns The degree-$g$ part of the Picard scheme is geometrically integral and does not construct this quotient.

lem-trf-relative-nodal-point-pinching vs lem-weil-pbc-closed-subset-proper-over-base-properties: The new statement constructs the finite nodal point-identification quotient and specifies its branch local rings and subcurve embeddings; the existing statement concerns Closed subsets proper over a base: any scheme structure, closed subsets, images and does not construct this quotient.

lem-trf-relative-nodal-point-pinching vs lem-weil-pbc-eventually-proper: The new statement constructs the finite nodal point-identification quotient and specifies its branch local rings and subcurve embeddings; the existing statement concerns Properness descends to a finite stage of a limit and does not construct this quotient.

lem-trf-relative-nodal-point-pinching vs lem-weil-pbc-image-universally-closed: The new statement constructs the finite nodal point-identification quotient and specifies its branch local rings and subcurve embeddings; the existing statement concerns The image of a universally closed scheme under a surjection is universally closed and does not construct this quotient.

lem-trf-relative-nodal-point-pinching vs lem-weil-pbc-scheme-theoretic-image-proper: The new statement constructs the finite nodal point-identification quotient and specifies its branch local rings and subcurve embeddings; the existing statement concerns Scheme-theoretic image of a proper scheme in a separated one is proper and does not construct this quotient.

## Unfinished work

No unresolved proof gap in this one-level split. The two new inputs are deliberately unsplit for subsequent workers. The downstream reference-properness requirement is explicitly reported above. Server dry run and push follow.
