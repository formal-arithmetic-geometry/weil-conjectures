# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-segal-composition-equivalences.json`: statement unchanged; split into nine proof steps. Mathlib search verdict: no match.
- `citations.json`: verbatim excerpts for every citation in every proof step.
- `report.md`: this report.

## New nodes

None; zero Mathlib leaves. Two provisional children were removed because their content is a short lifting argument or follows directly from the item's composition homotopies. Neither is part of the delivery.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint id, Segal, Rezk, and composition-equivalence terminology found no declaration of the item. The upstream master reference does not furnish a completed attachment either.

## WANTED:

WANTED: archival copy of Charles Rezk, *A model for the homotopy theory of homotopy theory*, Sections 2.4–2.5, 5.1–5.5, and 11.2, for this item. I read the referenced PDF online at the node's existing Rochester URL, in particular printed pp. 12–13 and 25. No Stacks tag states this Segal-space theorem. The endpoint-cylinder lifting argument is also the argument of Stacks Tag 08NS, `lemma-trivial-kan-homotopy`, but the proof here derives it directly from the cited boundary/cell characterization and does not rely on that tag as an uncited theorem.

## Not duplicates

No new nodes. The whole-DAG and blueprint searches found only the existing Segal infrastructure. In particular the existing `lem-weil-pbc-trivial-kan-homotopy-equivalence` gives one section/homotopy inverse, so it cannot be cited for a homotopy between arbitrary prescribed sections; step 3 writes that endpoint lift explicitly instead.

## What was wrong or corrected

The imported item had no proof. Its statement is correct with the strict-fiber and Reedy-fibrant conventions already given, and is preserved in full. I expanded Rezk's homotopy-category zigzags into actual simplicial sections and cylinder homotopies, rather than silently treating an equality in the homotopy category as the required cylinder map. The inverse equations must read `c(f,g) ~ id_x` and `c(g,f) ~ id_y` because `c(a,b) = b ∘ a`; steps 7–8 keep this order throughout all four composites.

The ancestor is `prop-coef-integral-exceptional-adjoint`, whose second proof paragraph motivates the mapping-space chain; the item is additional Segal infrastructure rather than a literal restatement of that paragraph. The existing ancestry metadata already explains this. I read the chapter and `sk-prop-sf-biduality-general` unit; this is a subsidiary node, so no realized fields of the unit are changed. No SGA source is used.

The outer-horn item's step 2 cites this item. This is a dependency direction to preserve, not a cycle in the final delivery: the new proof does not cite the outer-horn item, the equivalence classifier, the completion theorem, or the cartesian Segal-exponent theorem. The elementary homotopy arguments are proved directly from the lower Reedy mapping lemma.

## Unfinished work

None in the one-level split. The report's archival-copy request does not prevent the online source from being read. The generic Kan functor-space and simplicial-homotopy-equivalence nodes are declared in `split_report.tool_uses`, because they are tools from the compact-support base-change unit and do not replace a step of the present unit's route.

## Review by Q05

I read Rezk Section 5.1's fixed-vertex trivial fibrations, Section 5.3's composition choices, Proposition 5.4's degree-three/degeneracy proof, Section 5.5's inverse convention, and Section 11.2 (Propositions 11.3–11.4 and Corollary 11.5). The final proof is marked agent-written because its parameterized lifts and full homotopies are expanded here; the source only writes zigzags for part of that argument. I also read the full statements of every cited node, not their proofs as substitute interfaces.

For step 1 the Reedy cartesian lemma defines exactly `F(n)`, `cK`, and `Map`; evaluation at the identity simplex and mapping out of the spine union give the required strict identifications degree by degree. In step 2 that lemma's mapping-fibration clause is applied with the Reedy fibration `V → *` and monomorphisms of shapes, and the Kan model node supplies the trivial-fibration criterion. I checked the pullback carefully: fixing vertices is a pullback of an already trivial fibration, so I use boundary lifting, not an unjustified pullback of a bare weak equivalence. No base-change fibrancy hypothesis is missing.

Step 3 uses the Kan model node's boundary-lifting and boundary-cell statements to extend over an arbitrary monomorphism. Its endpoint inclusion is degreewise injective. The two endpoint maps have exactly the same base map, both for arbitrary sections and for `id` versus `s θ`, so postcomposition gives precisely the homotopies claimed in the item. Step 4 uses the existing Kan functor-space node and the internal-functor definition. I checked both dimension-two horn constructions for composition and reversal of edges. Thus a finite homotopy chain into a Kan mapping fiber becomes one simplicial cylinder map, and equality of components really supplies the inverse paths used later.

In step 5 the shapes are the pairs of triangles `012/023` and `123/013`. On each pair, forgetting the second triangle is the pullback of the degree-two trivial Segal fibration along its two known edges. Its projection to the three consecutive edges is therefore trivial by successive lifts. Restriction from the tetrahedron is a Kan fibration; the Reedy node explicitly states the two-out-of-three model axiom needed to make it trivial. Both constructed tetrahedron maps are sections over the same three-edge product. Their long-edge restrictions are exactly the two selected composites, and their homotopy therefore proves associativity on the entire product, rather than just on vertices.

Step 6 compares each chosen section with the correct degeneracy (`s_0` for the left identity and `s_1` for the right identity). The existing homotopy-category node states explicitly that triangle lifting followed by `d_1` is its composition, so its citation supports the component calculation. In step 7 I verified that the inverse representative `g:y→x` comes from that node's Hom-set description. The path `α` lies in `M(x,x)` and the path `β` in `M(y,y)`; the precomposition formulas use `β` for `GF` and `α` for `FG`. Step 8 uses `α` for the postcomposition composite `RU` and `β` for `UR`. The displayed maps with the path parameter give the intermediate homotopies explicitly. Every remaining homotopy is either an earlier whole-product homotopy restricted along fixed vertices or its composition with a simplicial map.

Step 9 cites a node whose statement says exactly that a pair of simplicial homotopy inverse maps induces realization weak equivalences, without Kan or nonemptiness assumptions. Its final invertibility assertion is checked by multiplying by `[g]` on the indicated side. I tested a discrete nerve of an ordinary category (where all formulas become literal composition), the empty simplicial space, empty mapping fibers, repeated vertices, and disconnected object/mapping spaces. No argument requires completeness, a nonempty object space, or connectedness. Finally I checked C1/C4 by copying literal statement excerpts into `citations.json` for every use. The item itself was searched anew with two LeanFinder phrasings, Loogle, grep, and LeanSearch; I read the strict Segal source hits and rejected them because they concern bijective spines of one simplicial set, not this Reedy fibrant simplicial-space statement. The sole grep hit is a bibliographic Rezk reference, not a theorem match.

## Second reading by Q05

- Item statement: checked clause by clause against Rezk §§5.1, 5.3–5.5 and 11.2, including the strict fibers, section-defined composition, associativity/unit homotopies, and both composition maps; verdict: agrees, with no hypothesis added or dropped.
- Step 1: checked the representable, spine, vertex, and strict-fiber identifications against the mapping-space definitions in the Reedy-cartesian node and Rezk §5.1; verdict: correct and elementary.
- Step 2: checked monomorphisms, mapping fibrations, Kan fibers, the Segal weak equivalence, and the vertex-fixed pullback lifting against the two cited node statements; verdict: correct, with the pullback boundary argument supplying the fixed-vertex trivial fibrations.
- Step 3: checked transfinite boundary-cell lifting and the endpoint-cylinder construction against the Kan model node and Rezk §§5.1–5.3; verdict: correct and elementary.
- Step 4: checked Kan functor-space horn compression and the passage from equal Kan components to simplicial paths against the cited internal-functor and Kan-functor statements; verdict: correct and sufficiently explicit.
- Step 5: checked the 012/023 and 123/013 triangle unions, their pullback projections, two-out-of-three, and long-edge comparison against Rezk Proposition 5.4 and the Reedy/Segal statements; verdict: correct on the full parameter product.
- Step 6: checked both degeneracy comparisons and the componentwise composition convention against Rezk §§5.4–5.5 and the homotopy-category node; verdict: correct.
- Step 7: checked the inverse representative, the order `c(f,g)=g ∘ f`, the α/β paths, and the precomposition homotopies against Rezk §5.5 and Proposition 11.3/Corollary 11.5; verdict: correct.
- Step 8: checked the postcomposition inverse formulas and right-unit restrictions against Rezk §11.2 and the associativity/unit steps; verdict: correct.
- Step 9: checked the simplicial homotopy-equivalence criterion and the preservation/reflection calculation in the homotopy category against Corollary 11.5 and the cited weak-equivalence node; verdict: correct, including empty mapping fibers.
- New nodes: none; there were no new statements requiring B1–B7 or duplicate-node searches.
- Edge cases: checked the empty simplicial space, empty mapping fibers, a discrete nerve of an ordinary category, repeated vertices, and n=2; all constructions remain defined and the claimed implications are vacuous or literal as appropriate.

Changes made: corrected the imported creation metadata so `created.item` is `lem-coef-segal-composition-equivalences` and `created.group` is `Q05`; no mathematical statement or proof step required correction.
