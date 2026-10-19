# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-generic-fibre-component-lower-bound.json`: statement item, split into eight proof steps; no Mathlib match. Step 7 was repaired to cite the finite dense-open intersection theorem.
- `dag/nodes/sec-trace-formula/lem-trf-finite-dense-open-intersection.json`: Mathlib leaf for finite intersections of open dense sets.
- `citations.json`: exact statement quotations for all step/node citations, including the repaired Step 7 citation.
- `searches.jsonl`: actual additional searches, with semantic phrasings. The item also retains its inherited search records. `prepare.py` and `node.json` are sandbox-only preparation material.

## Attachments

No item attachment. Searched the full `WeilConjectures/` tree of `/home/ubuntu/weil-src-slopmaster2` for the blueprint id, generic fibre/component language, and `irreducibleComponents`. The closest generic irreducibility theorem in `RingTheory/GenericIrreducibility.lean` assumes geometric generic irreducibility and is an algebraic irreducibility result, not this ordinary-component lower bound for arbitrary finite-type schemes. Other hits concern group schemes, component loci, and Noetherian compactifications. None states every clause here. The upstream master checkout is reference material only, not proof evidence.

## WANTED

None. The Stacks `.tex` sources needed here are present.

## Findings and changes

The imported statement agrees exactly with Stacks more-morphisms Tag 0554, label `lemma-irreducible-components-in-neighbourhood`. In particular, the component count is ordinary, not geometric, and there is no hidden Noetherian, separatedness, flatness, or reducedness assumption. No statement correction or dispute is necessary.

The item had no proof. I supplied the closed-closure proof of 0554, expressing its 054X nowhere-dense assertion by the existing ordinary-fibre open-density theorem. The existing nonempty-closed-subset theorem packages the source's generic-flatness/open-image argument. Those two inputs already allow a nonreduced irreducible base, so the item's proof does not repeat a reduction argument. The returned version incorrectly treated finite intersections of dense opens as an elementary step with no cited support; Step 7 now explicitly cites `Set.Finite.dense_sInter` through the new Mathlib leaf and checks that the complements are open as well as dense.

The binary closed-cover theorem really has only two closed subsets in its statement. Step 5 applies it to the finite union of all component closures and the empty second subset. It does not claim an unrecorded finite-family generalization. The final sentence of 0554 is expanded: dense open complements give an exclusive point in each covering piece, and the components through these points are distinct.

I read the chapter and unit records, the three-level route rules, GOAL.md and dag-sync.md, and the ancestry of this item through the 055A lower-bound invocation to `lem-trf-local-term-locality`. This is a generic algebraic-geometric input within that recorded Noetherian-approximation branch; it replaces no unit step. Four generic statement tools are declared in `split_report.tool_uses`: the reduced induced closed subscheme construction, ordinary open-fibre density, closed-cover spreading, and closed-subset fibre nonemptiness. The topology component-cover result is already a Mathlib leaf.

Mathlib searches through the required command returned finite-component, finite-fibre, dominant-map, generic-point, and open-map/irreducible-fibre correspondence results. I read the three Loogle signatures and their source at `Mathlib/Topology/Irreducible.lean:463,493,506`; they presuppose a map with irreducible fibres and do not prove this component-count bound. The two semantic phrasings likewise gave no exact result or one-line specialization. All five services/queries succeeded, and only actual log records were appended to the item. Existing search records were preserved. No search result was promoted to a leaf on similarity alone.

## Not duplicates

The new node is not a duplicate: searches of the whole DAG and blueprint for finite intersections of dense opens, 0554, 054X, nowhere-dense generic fibres, and generic component counts found no existing node stating this finite-topology fact. The item keeps `same_as: []`; the new leaf's `same_as` is also `[]`.

## Unfinished work

None in the one-level split. The existing cited theorems remain their own DAG items; no proof has been smuggled into a new statement-only node. No Lean was written or compiled, no agents were started, and all writes are in the assigned sandbox.

## Review by Q119

I read Stacks more-morphisms 0554 in full (statement and proof), 054X (`lemma-nowhere-dense-generic-fibre`), the discussion before 054Y and 054Y (`lemma-cover-generic-fibre-neighbourhood`), 05F5 (`lemma-nonempty-generic-fibre`), and the flatness/open-image paragraph of 055G. The tag-to-label map confirms these identifiers. I also read schemes 01J3 (`lemma-reduced-closed-subscheme`) with its ideal-sheaf construction, and topology 004W (`lemma-irreducible`) including the component existence and covering clauses. The new Mathlib leaf was checked against `Set.Finite.dense_sInter` in `Mathlib/Topology/Baire/Lemmas.lean:50`; its statement is exactly the finite open-dense intersection theorem.

For Step 1 I opened `def-weil-irreducible-components` and `lem-sc-irreducible-components-cover`: the definition supplies nonempty closed components and the theorem explicitly supplies their covering. The case n=0 requires no assertion that a nonempty scheme has zero components; it simply takes the whole nonempty base, because the requested lower bound is zero.

For Step 2 I opened `def-pc-scheme-fibre`, which actually states the homeomorphism onto the set-theoretic fibre, and `lem-weil-pbc-reduced-induced-closed-subscheme`, whose clause (2) gives a closed scheme with precisely the prescribed support. The closure identity is the elementary subspace-closure formula, since each generic component is already closed in that fibre. We use only underlying spaces of the other fibres, not a false claim that a reduced closed scheme has reduced fibres. Step 3 cites the finite-type definition and the closed-immersion definition; the latter includes the affine quotient description. Images of the original finite algebra generating sets generate the quotients, and a finite affine cover stays finite. No finiteness of the defining ideals, quasi-separatedness, or Noetherian assumption is used.

For Step 4 I opened the complete statement of `lem-sbc-generic-open-fibre-density`. It accepts an arbitrary finite-type scheme morphism, an open in its source, and a point whose closure is the entire base; geometric irreducibility is explicitly not required. Step 3 supplies finite type of each component closure. Distinct generic components are maximal irreducible sets, so their intersections are proper closed subsets and the complementary opens are dense. The theorem gives precisely the ordinary-fibre density used later. This checks both the hypotheses and the conclusion rather than relying on its proof or its name.

For Step 5 I opened the complete binary statement of `lem-sbc-generic-fibre-closed-cover-spread`; its hypothesis is a closed covering of the single specified fibre and its output is a covering above an ambient open intersected with the closure of that point. With the first closed set the finite union of the D_i, the second empty, and closure(eta)=Y, it gives exactly the claimed covering. The fibre-definition node provides the conversion from set-theoretic to scheme fibres. For Step 6 I opened `lem-sbc-generic-closed-subset-fibre-nonempty`. It permits any closed subset of a finite-type source that meets the generic fibre and explicitly imposes no reducedness, Noetherianity, or separatedness; it gives an open containing eta on which that subset meets every fibre. Each D_i meets the generic fibre because C_i is nonempty. Thus no unproved constructibility or arbitrary-open finite-type assertion is used.

For Step 7 I checked the returned gap directly. Step 2 identifies each specialized $D_{i,t}$ with the underlying space of $(X_i)_t$, and each $D_{i,t}\setminus D_{j,t}$ is open because $D_{j,t}$ is closed. Step 4 supplies density of every one of these opens, and Step 6 supplies nonemptiness of $D_{i,t}$. The new leaf states exactly that a finite family of open dense subsets has dense intersection (Mathlib `Set.Finite.dense_sInter`, `Mathlib/Topology/Baire/Lemmas.lean:50`), so the intersection is nonempty without assuming that $D_{i,t}$ is irreducible or invoking an unsupported generic point. The chosen $x_i$ therefore exists. For Step 8 I reopened the component-cover statement: it explicitly puts every point in a component of an arbitrary topological space, with no finiteness hypothesis. An irreducible component contained in a finite union of closed pieces lies in one piece by induction on that finite union. The exclusive point forces which piece it is, and the written contradiction proves distinctness. We do not assert that D_i itself remains irreducible.

I tested n=0 (including an empty generic fibre), n=1, disjoint constant points over a base (the bound is sharp), two generic components that meet (the proof uses dense complements rather than disjointness), a vertical extra component (removed or absorbed by the covering shrinking), and nonreduced bases/fibres (all relevant comparisons are topological). I also tested the Step 7 topology on a reducible union of two lines: openness permits successive intersections of dense opens, exactly as `Set.Finite.dense_sInter` formalizes. No irreducibility of a specialized $D_{i,t}$ is used. Empty individual specialized pieces are excluded exactly by Step 6. These tests required no statement correction.

Against delivery-errors B--E: the new node is a Mathlib leaf rather than an elementary restatement, and it does not repackage a clause of the item. All substantive assertions are supplied by opened cited statements. The only elementary step remains the affine quotient finite-type check; Step 7 now has an explicit cited theorem. Every citation has a verbatim quotation in citations.json; proof_deps is the union of uses. All eight steps are below 2000 characters, and none hides an extra comparison or standard lemma. There are no SGA sources. The repair was to expose the openness and cite the finite dense-open intersection theorem; no source statement error was found.
