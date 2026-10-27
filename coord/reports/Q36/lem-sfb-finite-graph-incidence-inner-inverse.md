# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-graph-incidence-inner-inverse.json`: existing statement, now split into four elementary steps; not a Mathlib match.
- `citations.json`: verbatim basis-definition quotes for the citations in steps 3 and 4.
- `report.md`: this report. `searches.jsonl` is produced by the required search command.

There are 0 new nodes and 0 new Mathlib leaves. The statement, statement dependency, inherited citations, original search records, and creation metadata are retained. No Lean or repository file was written and no compiler was run.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, incidence, spanning-tree/forest, generalized-inverse and inner-inverse terminology. No declaration gives the graph statement. Read `AlgebraicGeometry.alternatingCechSheaf_restrict_differential_inner_inverse` at `AlgebraicGeometry/AlternatingCechSheafDifferentialInnerInverse.lean:98`: its domain is a restricted alternating Cech sheaf differential, with a chosen cover index, not an arbitrary integral graph incidence map. It is not an attachment.

## Wanted sources

None. This is an agent-written elementary auxiliary, as its original source record already says, rather than a theorem attributed to an unavailable paper.

## Findings and corrections

The imported item had an empty proof. Its statement is correct and unchanged. I supplied a direct construction, without invoking the image-of-incidence characterization, a spanning forest, freeness of subgroups, projectivity, or a rational-to-integral argument. Define u equivalent to v when there is an integer edge vector with boundary b_v-b_u; show the relation is an equivalence by explicit witnesses 0, -c and c+d. Its classes need not be identified with connected components. Select one representative per class and witnessed lifts of every vertex-minus-representative difference. The finite-sum formula r(x)=sum_v x(v)p_v is linear, and the two representative terms cancel on every edge. This proves the required identity by the standard-basis expansion.

Read the current blueprint unit and direct-images proof in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, as well as the DAG chapter and unit records. The current blueprint passage (3) gives the direct-image route, not this elementary graph lemma. Its supporting nodal Picard argument motivates the auxiliary through `lem-sfb-finite-graph-cycle-character-quotient`. `tools/blueprint_refs.py ancestor` reports `None` for the inherited creation chain; I preserved that value and the existing detailed provenance. Whole-blueprint searches for `incidence`, `graph` and `inner inverse` found no equivalent blueprint statement, so `same_as` remains empty.

All eight original search records were preserved. New searches were run only through `batch2/msearch.py`, with two distinct semantic phrasings and two Loogle queries, plus source greps. Their exact query strings and logged answers are in the item. The first semantic search completed during the transport interruption; I read its existing log and the returned transvection source rather than launching it again. Matrix/Transvection.lean:154-192 concerns invertible square transvection matrices. SimpleGraph/IncMatrix.lean:13-58 defines an unoriented incidence matrix and explicitly lists oriented incidence as TODO. The other hits concern free-group lift properties, partially defined linear maps, graph darts, complex-shape boundaries, or splittings assumed surjective. In particular the boundary need not be surjective, so `LinearMap.leftInverse_splittingOfFunOnFintypeSurjective` is not a one-line match. Read Finsupp/Pi.lean:160-191 and LinearPMap.lean:990-1015. None gives this item over the integers.

## Unfinished work

None in the split. The server dry run passed; its outcome is recorded below.

## Review by Q36

I read Stacks `literature/stacks-project/curves.tex`, Tag 0C1M, label `lemma-glue-points`, including the exact units sequence and the cokernel description in its proof (lines 3106-3147). It motivates graph gluing scalars but asserts no integral incidence inverse. Accordingly every step and the proof origin explicitly identify the argument as agent-written; I have not attributed the construction to Stacks. No new node needs a separate source review.

For step 1, I checked each proposed witness directly under the linearity of the given boundary: boundary(0)=0, boundary(-c)=-(b_v-b_u), and boundary(c+d)=(b_v-b_u)+(b_w-b_v). These establish reflexivity, symmetry and transitivity, without a theorem about graph paths or connected components. Each edge witnesses the relation between its own endpoints from the statement's formula. This step has no cited node because it uses only data and elementary identities already in the statement.

For step 2, each class is nonempty by the definition of an equivalence class, so one representative can be chosen per class. Since a_C and v are in the same class, the existence of p_v is exactly the defining existential condition proved in step 1. The selections use ordinary classical choice, without assuming any unproved graph fact or a splitting theorem. Both endpoints have the same representative because the representative is selected for the class, not independently for each vertex. This is the only coherence required. No node is cited or needed here.

For steps 3 and 4 I opened `def-weil-pbc-free-module` and read its complete statement. It defines a basis by unique finite linear combinations, which is exactly what these steps use for the standard vertex and edge vectors already specified in the item. It does not assert an arbitrary linear splitting; none is taken from it. The finite-sum formula itself proves linearity by distributivity, and its value at a basis vector is obtained by substituting the delta-function coordinates. Step 4 then writes the full endpoint computation, including both signs, and expands an arbitrary edge vector to extend the identity. `citations.json` contains the verbatim basis sentence for each of these two uses. This existing definition is a Mathlib leaf, so its other-unit placement is not a route departure.

I checked the hypotheses and small cases: if V is empty the specified maps E to V force E empty, no representatives or lifts are selected and both linear maps are the unique zero maps. If E is empty and V is nonempty, the relation is equality, each p_v can be zero, and r=0 works. Isolated vertices likewise form singleton classes with a zero lift available. A single oriented edge 0 to 1 permits p_0=0 and p_1=b_e; reversing the orientation changes the required sign. With parallel edges one can choose either edge as the lift and the identity still holds on every edge separately; no edge injectivity is used. For disconnected graphs the selections are made class by class and require no single global root. On a directed triangle the lift for the third vertex may be the sum of two edge vectors; the calculation still verifies all three edges, without asserting r boundary is the identity on edge cycles. The integers are retained throughout and no division occurs. The proof even handles loops, although the original loopless hypothesis is retained.

Against delivery-errors B: no new nodes or sketches were introduced, TeX is singly escaped, and all sources and exact searches are recorded honestly. Against C: every step's cited statement was read, the two needed quotes are verbatim, and all remaining operations are displayed elementary calculations; no source tag stands for an uncited theorem. Against D: no content is moved into a new node and no step is circular; the existential lifts are supplied by the definition of an equivalence relation already established, not by the desired conclusion. Against E: all objects and domains are the ones in the statement, the sign and class dependence are explicit, and no extra hypothesis is used. Each step is under 500 characters, so there are no long non-elementary steps hiding further lemmas. The only correction was filling the previously empty proof; no statement dispute was found.

## Not duplicates

No new nodes were created. The related graph homology-rigidity and Euler-trace nodes give rational invariants or automorphism conclusions, not this integral linear map; the parent cycle-character quotient is a user of this item, not a permissible dependency. The split cites neither parent nor siblings and adds no cycle.

## Delivery checks

The required `deliver.py Q36 lem-sfb-finite-graph-incidence-inner-inverse --no-push` exited 0 and printed `OK (not pushed)` at commit `58bf2f8c953`; server preflight passed, including the DAG and split review checks. The worker will return the final push result and commit in its final delivery response. No new nodes or Mathlib leaves are added.
