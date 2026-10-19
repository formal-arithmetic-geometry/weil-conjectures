# Q96: lem-coef-spaces-homotopy-fiber-detection

## Files written

- `dag/nodes/sec-six-functors/lem-coef-spaces-homotopy-fiber-detection.json`: statement, split. Retains the complete existing proof route and all original hypotheses; the old step 1 is replaced by four shorter steps, and old steps 2–6 are retained as steps 5–9, with internal step references renumbered.
- `dag/nodes/sec-six-functors/lem-coef-mapping-path-square-rectification.json`: statement, unsplit; no Mathlib match. Extracts the parameterized comparison between a specified homotopy square and a strict square of the two fixed mapping-path objects, together with the endpoint-relative independence needed for the prescribed homotopy-fiber maps.
- `citations.json`: one verbatim statement quotation for each item step/node pair.
- `searches.jsonl`: actual msearch results; retained without alteration. `revise.py` is sandbox-local preparation code, not a delivery node.

One new node; zero Mathlib leaves. No unit record changes, no Lean edits, no compiler or Lake commands, and no live-repository writes.

## Attachments

None. Searches of `WeilConjectures/` in the supplied slopmaster2 source for the exact blueprint id, homotopy fibers, mapping-path squares and strictification found no declaration proving this item or the new comparison. Master was checked as reference material only. Both audited item states are `none`. The inherited Mathlib searches were read and retained: `FibrantObject.weakEquivalence_homMk_iff` merely unfolds a subcategory structure, and homological-complex homotopy fibers have different objects.

## Wanted literature

WANTED: archival copy of Lurie, Higher Topos Theory, Corollaries 2.3.2.2 and 2.3.2.4 (printed pp. 100–101; online PDF pp. 117–118), for lem-coef-mapping-path-square-rectification. Read online at https://www.math.ias.edu/~lurie/papers/HTT.pdf; no download or literature write made.

WANTED: archival copies of Kerodon Proposition 3.2.8.1 (00XC), Example 3.1.8.10 (0101), and Corollaries 3.2.6.3, 3.2.6.5, 3.2.6.7 (00WP, 00WR, 00WT), for the item's retained equivalence-detection and component arguments. These are Kerodon identifiers, not Stacks tags. Read online.

WANTED: archival copy of Hovey, Model Categories, Lemma 2.4.16, Lemma 3.2.4 and Corollary 3.6.2, for the existing realization and Serre inputs used by this item. Read the cited passages online at the source URL already recorded in those nodes. There is no Stacks tag for this Kan/Serre comparison. No SGA source is used.

## What needed correction

The current repository already preserves a reviewed six-step proof, but its status is now unsplit. The sandbox initially contained only dispatcher markers; there was no earlier local report, split or search log to overwrite. I copied the current node, retaining its statements, citations, searches, historical review and split-report material. Its first step was 3921 characters and contained a separate comparison construction: an actual strict map between mapping-path objects, with relative uniqueness of coherent concatenation. This is now a named, statement-only auxiliary lemma. Its statement explicitly specifies the entire parameterized horn and the two projection equations; it assumes neither horizontal equivalence nor any vertical fibration. In particular it does not restate either implication of the item's equivalence test.

The remaining realization and basepoint discussion is written as short applications of existing nodes. I also updated the inherited internal references to the new step numbering (basepoint transport in step 4, forward components in step 5, and the concluding references to steps 6–8). All non-elementary steps are now below 2000 characters (longest 1188). I did not replace the finite-stage/integral blueprint route: this is the same mapping-space tool under the coefficient adjunction's paragraph 2. The current main-20261015 blueprint proof was read at `sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`; the historical `sk-prop-sf-biduality-general` ancestry and maintainer-owned unit metadata remain intact.

No statement dispute was found; the item statement and Lean records are unchanged.

## Not duplicates

lem-coef-mapping-path-square-rectification vs lem-coef-spaces-homotopy-fiber-detection: the new node constructs and compares fixed mapping-path squares without any weak-equivalence assumption; it proves neither direction of detection on fibers. The orbit/stabilizer and positive-degree diagram chases remain in the item.

lem-coef-mapping-path-square-rectification vs lem-coef-space-path-fibration-replacement: the latter factors a single map and states its fibration, equivalence and fiber properties; it says nothing about a square specified only up to homotopy, coherent concatenation, or endpoint-relative independence of fillers.

lem-coef-mapping-path-square-rectification vs lem-cbc-kan-fibration-fiber-criterion: the latter gives trivial-fibration/contractible-fiber tests and the factorization of a single map. The new node constructs a map between two fixed factorizations from a homotopy square; no contractibility or equivalence test is asserted.

lem-coef-mapping-path-square-rectification vs lem-coef-inner-anodyne-pushout-product: the latter is the general lifting-class theorem, already a Mathlib leaf. It does not state the actual comparison map on the fixed path objects or the homotopies of its fiber maps. The extracted comparison applies that theorem twice, builds the maps by the specified internal-Hom pullbacks, and identifies the realized composite relative to endpoints. Its proof plan is given below, not in the new statement-only node.

lem-coef-mapping-path-square-rectification vs lem-coef-infinity-parameter-cone-extension: the latter concerns relative colimit/limit cones and isofibrations of diagram categories; it has no mapping-path square comparison.

lem-coef-mapping-path-square-rectification vs lem-coef-infinity-edge-pullback-mapping-fiber: the latter identifies mapping spaces of diagrams in a pullback over one base edge, for an inner fibration. The new node has arbitrary maps of Kan complexes and a specified homotopy square, and compares their mapping-path replacements.

lem-coef-mapping-path-square-rectification vs lem-coef-joyal-homotopy-exponentials: the latter states exponential adjunctions in the Joyal homotopy category, not strict simplicial maps on these path replacements with relative homotopies on every fiber.

Whole-DAG searches covered mapping paths, strictification, homotopy-commutative squares, parameterized horns, and the two HTT corollary numbers; the other same-source hits concern marked categorical patterns, relative limit cones, sequential spines, categorification and filtered sections, with different statements. Whole-blueprint searches for path fibration, homotopy commutative, strictification, mapping path, path and rectification found no statement of this auxiliary lemma or the item. Both `same_as` lists remain empty. The new id did not previously exist.

## Review by Q96

I read the item and the full statements of all six original citations before extracting anything. I read Kerodon 00XC for the actual two directions: it uses the action on fiber components and its stabilizers, then an exact-sequence chase. This agrees with the retained route. I also checked its linked 00WP/00WR/00WT component and stabilizer results. Hovey 2.4.16 supplies the natural sequence for strict squares of Serre fibrations; Hovey 3.2.4 gives preservation of pullbacks in k-spaces; 3.6.2 gives realization of Kan fibrations. These are used through the existing nodes, whose statements explicitly include the required naturality and low-degree clauses; I have not treated the references alone as dependency nodes.

For step 1, `def-cbc-enhanced-diagrams-cones` fixes the actual homotopy-fiber model and weak-equivalence convention, and `lem-coef-space-path-fibration-replacement` states exactly the endpoint fibration, constant-path weak equivalence and strict-fiber identification used. The projections are weak equivalences because their composites with those sections are identities on components and based groups. Kan-ness of the total spaces and fibers is the two-stage horn lift written there; it does not impose a fibration hypothesis on r or q.

For the new node, I read HTT 2.3.2.2 and 2.3.2.4 and the existing pushout-product leaf, including its pinned Mathlib declaration at Inner/PushoutProduct.lean:103–109. The comparison is between fixed path models, not an abstract replacement: the map on the horn has 01 edge H after projection and 12 edge v applied to the universal path. Filling its product with E_r gives edge 02. The endpoints verify e_q U = u e_r and Q U = v R. Independence requires a second, relative lifting problem with the monomorphism E_r times boundary(Delta^1) into E_r times Delta^1, giving a homotopy fixed on the given horn. This retains all higher simplices and restricts to homotopies on every fiber. Finally, the realized 2-simplex contracts the broken 01–12 path to 02 with its endpoints fixed. This is the concrete proof plan of the extracted lemma; no proof has been placed in its unsplit node. It is a comparison with its own data and relative compatibility, not a new name for a clause of fiber detection.

Step 2 uses precisely those projection equations, coherent fiber-map assertion and relative-independence clause of the new node. Step 3 uses only the fibration clause of `lem-coef-kan-realization-serre`, the natural pullback clause of `lem-coef-realization-finite-limits`, and the sequence/action/naturality clauses of `lem-coef-serre-homotopy-exact-sequence`. All hypotheses hold: R and Q are Kan fibrations; their realizations and fibers are k-spaces; and U gives an actual commutative square. No implicit strictification is left in that application.

Step 4 uses path lifting from the Serre node to show that an empty fiber has no total-space component above that base component. For the based comparison, evaluation of the universal path gives precisely the homotopy whose boundary trace is gamma; the new node identifies the other trace with H_x followed by v gamma relative to endpoints. The cubical definition fixes what basepoint transport means, so these are the based maps needed by the following chases. The nontrivial simplicial comparison itself is now cited, not proved implicitly here.

Steps 5 and 7 are the original component arguments: the Serre node explicitly says that the orbit set is the component preimage and identifies stabilizers with the image of pi_1 of the total space. In step 5 the total and base isomorphisms identify those stabilizers; the equivariant map on each orbit is bijective by the displayed coset argument. In step 7 an equivariant component bijection gives orbit bijections, and the base-component bijection assembles them. These statements are actually present in the quoted node; a definition of fibration would not suffice.

Steps 6 and 8 retain the exact sequences from that same node and spell out all four diagram chases. I checked the orders of multiplication, so no commutativity is used for pi_1. In step 8, when n=1 the boundary lands in pi_0 of the fiber: injectivity of the fiber-component bijection, rather than a fictitious group structure on pi_0, detects the distinguished point. Step 9 uses only the weak-equivalence definition and ordinary change of basepoint along a path within a simplex. It separately treats S empty, forcing X, T and Y empty. The other arguments permit empty fibers, empty total spaces and disconnected bases.

The small cases tested include all-empty spaces, an empty source over a nonempty base, discrete Kan complexes, a point base, identity squares with nonconstant H, and disconnected fibers with a nontrivial fundamental-group action. In the identity/nonconstant-H case it is important that the comparison retains H; replacing it by a square made only from u and v would lose the required fiber map. The new lemma and step 2 expressly retain H. With empty E_r the extension and its uniqueness are the unique maps out of an empty product; with discrete T any composable paths are constant on each component. None of these checks requires connectedness or a choice of a point in an empty fiber.

I checked delivery-errors B–E against these files: the new node is self-contained and statement-only, has its definition dependency, honest logged searches and correct blueprint ancestry; its Mathlib candidates were read at their actual types and ruled out. Each item use has a verbatim quote in citations.json. The new node depends only on the existing enhanced-diagram definition, so it cannot introduce a cycle back to the item. No other unit's proof route is used as a replacement. No assumptions were added and no definition or target was weakened.

## What remains

No part of the item's natural-language argument is left unfinished. The one new auxiliary node is intentionally unsplit, as required for a one-level split. Mechanical delivery validation is performed by the required server dry run; the final response records the pushed delivery only after success.
