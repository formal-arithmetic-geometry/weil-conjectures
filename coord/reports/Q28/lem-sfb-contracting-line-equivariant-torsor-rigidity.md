# Stage 1 report: lem-sfb-contracting-line-equivariant-torsor-rigidity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-contracting-line-equivariant-torsor-rigidity.json: split; statement, statement dependencies, inherited blueprint lineage and earlier searches retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-affine-torsor-isom-scheme.json: new statement-only general representability/smoothness lemma; unsplit, no Mathlib match.
- citations.json: verbatim statement evidence for every use in the five proof steps.
- searches.jsonl: actual msearch.py results; includes exploratory graded-lifting searches which did not lead to new nodes.

## Attachments

None. Searches of lean/WeilConjectures by the item tag, contracting line, equivariant torsor and Isom/smoothness found no project declaration stating the item or the new lemma. The torsor isomorphisms in CategoryTheory/Sites/Torsor concern sheaves, not the representing smooth affine scheme required here.

## WANTED

WANTED: Alper, Halpern-Leistner, Heinloth, Cartan--Iwahori--Matsumoto decompositions for reductive groups, Lemma 3.6, printed p.6 and Section 2 Claim 3, printed p.3, for this item and lem-sfb-smooth-affine-torsor-isom-scheme. Not present locally. I read the author-hosted PDF https://sites.math.washington.edu/~jarod/papers/iwahori.pdf online; no download or repository write was made. The proof is marked agent-written because its explicit weight projection is my expansion of the source's smooth lifting argument.

## Findings and corrections

No statement dispute. The given isomorphism at zero is retained, rather than replacing it by some isomorphism or assuming either torsor is trivial. The original item had no proof. Its blueprint ancestor is null in the inherited long created-item lineage; tools/blueprint_refs.py ancestor confirms this. I retained that lineage and gave the new node the item followed by the inherited via list. The current latest blueprint's ctf-stability section and direct-images proof were read; the contraction lemma is a supporting prerequisite down the existing alteration/Cartan branch, and is not a replacement for a unit step. This item is not the unit's key statement, so no unit realization file is changed.

The only genuine black box newly introduced is the geometry of Isom for smooth affine group torsors. The other work is explicit coefficient algebra. In particular no new lemma simply restates fullness of the restriction functor. A prospective graded-lifting lemma was omitted: after an ordinary square-zero lift, projecting each homogeneous input to its matching weight gives a multiplicative lift by the two-line calculation in step 3. This is exactly the elementary-node exclusion in the brief.

## Not duplicates

lem-sfb-smooth-affine-torsor-isom-scheme vs lem-sfb-nodal-equivariant-torsor-rigidity: the former represents an isomorphism functor for arbitrary torsors over arbitrary base schemes and states its geometric properties; the latter extends specified equivariant isomorphisms over a particular complete-DVR node. Neither implies the former by specialization.

lem-sfb-smooth-affine-torsor-isom-scheme vs det-pe-torsor-comparison-affine: the latter descends a pro-etale sheaf torsor to an etale model; it does not represent Isom of scheme torsors or establish smoothness.

lem-sfb-smooth-affine-torsor-isom-scheme vs lem-sfb-space-module-isom-affine: that result represents isomorphisms of finitely presented quasi-coherent modules flat over the base with proper support, not torsors under arbitrary smooth affine groups; no representation/reduction argument giving the present result is supplied by its statement.

Whole-DAG searches for Isom/torsor, isomorphism functor and tag 04AG, together with whole-blueprint searches for equivariant torsor, isomorphism torsor, affine torsor and isomorphism functor, found no same assertion. There was no existing node with source tag 04AG. The inherited complete-DVR/node rigidity result is not applicable to the affine line by a one-line substitution.

## Review by Q28

I read the source's Lemma 3.6 argument on the contracting line and Section 2 Claim 3's explicit homogeneous algebraization. I also read Stacks examples.tex Tag 04AG, section-not-algebraic-stack, at its paragraph about the affine diagonal and Isom(P_1,P_2). It identifies affineness of Isom. For the new statement, the extension to arbitrary bases and its smoothness use the same torsor-local descent argument: on a simultaneous fppf trivializing cover the Isom functor is H, its changes of trivialization are translations on the left and right, and their cocycle is effective for affine schemes. Smoothness is local for that cover. Base-change compatibility follows from the represented functor on test schemes. These arguments are material for the new unsplit node, not an extra asserted proof inside its statement. No algebraic closure, chosen global trivialization or reductivity is needed for this geometry. The new node defines the general-base group object inline and cites the actual torsor, scheme, smoothness and affine-morphism definitions; it has no proof or proof dependencies.

For step 1 I read the whole new statement: it supplies an affine representing scheme, smoothness, the test-scheme functor and compatibility with origin/thickening pullbacks. Its hypotheses hold with S=Spec(k), Y=L, and the original smooth affine H and represented torsors. The conjugation action is constructed on test points with its formula, not assumed from a definition node.

For step 2 I read def-weil-affine-spectrum: its contravariant equivalence and global-section characterization supply the ring maps. The grading and the criterion for equivariance are proved by coefficient comparison in the Laurent coaction, including finite homogeneous support. This is a group-scheme calculation and works over finite fields as well; checking rational points alone would not suffice.

For step 3 I read def-sbc-smooth-morphisms. Its statement explicitly gives lifting on every first-order thickening of affine schemes, so it does say precisely what is used here; there is no covert invocation of a flatness or obstruction theorem from a definition. I checked J squared is zero even for the initial step n=0. I checked the matching-weight projection on products: apart from the desired pair of degrees, both factors of every contributing pair lie in J, and their product is zero. The lift still fixes the homogeneous image of the base A. def-weil-affine-spectrum supplies the conversion of the section lift to an algebra map. The induction starts at the prescribed f_0 and preserves compatibility, not merely existence at each level.

Step 4 uses no black box. For negative weight the target is zero at every stage; weight zero stabilizes from the start; for positive d it stabilizes at n=d. Finite homogeneous sums give polynomials, and the intersection of all powers of u is zero by the finite degree of a nonzero polynomial. This proves the algebra identities and base section condition without claiming the polynomial ring equals its ungraded completion.

For step 5 I reread the affine-spectrum and Isom statements: they give a section and exactly a torsor isomorphism whose reduction is the original alpha_0. The equation for the conjugation action gives the required left equivariance explicitly. This finishes every clause, including no need to trivialize either fibre and no uniqueness assertion.

Small cases checked: H trivial; P=Q with identity alpha_0; nontrivial fibre torsors; fields in positive characteristic; negative and zero weights; the first square-zero step; and empty Y for the new lemma. For a nonuniqueness test, on the trivial additive-group torsor with coordinate v of weight one, v maps to v+c u, so different extensions can agree at zero. None of these cases introduces connectedness, reductivity, an algebraically closed field, or a rational-point criterion. No proof step exceeds 2000 characters; their actual lengths are below 1000. Each citation is backed by the complete verbatim relevant statement in citations.json. Source tags and labels were checked in Stacks tags/tags. All Mathlib searches recorded on the new node were run with msearch.py and their hits read: topological/additive torsor results and ordinary affine-scheme isomorphism results do not give this lemma. The smooth graded-lifting search did find ordinary Algebra.FormallySmooth.exists_lift; I read Smooth/Basic.lean, but it does not assert the equivariant conclusion, and no redundant leaf was created for a lifting property already stated in the cited smoothness definition.

## Unfinished work

The new Isom geometry lemma is intentionally statement-only and remains available for a later one-level split. No other required work is left beyond the delivery checks and push.
