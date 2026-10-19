# Q127: marked cocartesian lifting, dedicated long-step repair

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-marked-cocartesian-lifting.json`: existing statement node, repaired eight-step split; inherited Mathlib verdict remains no match.
- `citations.json`: sixteen citations, each with the verbatim statement of the existing node used by that step.

There are zero new nodes and zero new Mathlib leaves. The existing saturation Mathlib leaf is reused, not delivered again. `repair.py` is a sandbox-only editing/checking script, not a project change.

## Attachments

None. I searched the permitted `WeilConjectures/` source for the item id, its blueprint tag, marked terminology, and cocartesian terminology. No project declaration states this theorem. The inherited stage-2 record names a theorem in `Sheaf.AlgebraicTopology.MarkedCocartesianLifting`, not a completed declaration under `WeilConjectures/`. Its record is preserved verbatim; no source or Lean file was changed. The exact upstream master is reference only, not proof-completion evidence.

## WANTED

WANTED: archived Lurie, Higher Topos Theory, Definition 3.1.1.1, Proposition 3.1.1.6 and Remark 3.1.1.10, for this item. Also Propositions 1.2.5.1, 1.2.5.3, 2.4.1.5 and 2.4.1.7 for the reused generic tools. I read these in the online IAS PDF; HTT is not archived in the permitted literature tree. The inherited `proof_origin.by = agent` remains appropriate.

WANTED: archived Kerodon Tags 01EZ, 019D and 01H0 for the already existing core and relative outer-horn tools. The web reader failed for 01EZ; I independently checked the point-case consequence actually used here against HTT 1.2.5.3. The other Kerodon pages opened, although their formulas were not fully exposed by the text reader; HTT 1.2.5.1 and 2.4.1.5 give the two consequences used in the retained converse. No Stacks tag states this quasicategorical theorem; the Kerodon tags are not Stacks tags. No SGA source is used.

## Returned point and repair

The dedicated return in `coord/returns/Q127.md` identifies old Step 2 (2209 characters), requires retaining the statement and Lean record, and permits existing nodes or Mathlib leaves for its hidden arguments. I began from the current repository JSON. No prior item node, report or search log was present in this item's sandbox. I read the earlier Q41 repair report as history; this delivery does not revive its removed horn-test helper or redo its completed saturation searches.

Old Step 2 contained four separate operations. The new Steps 2–5 expose them:

1. Step 2 translates the first two marked generators into inner lifting, cocartesianness of marked edges, and marked lifts from specified sources. This is the definition-level calculation, now marked elementary, just as the preserved converse horn calculation is elementary.
2. Step 3 cites `lem-coef-infinity-cocartesian-composition-initiality` for the non-elementary comparison triangle between the given cocartesian edge and a chosen marked lift, including the equivalence in the actual fibre. This already exists as an explicit statement, so creating a comparison lemma would duplicate it.
3. Step 4 cites `lem-coef-infinity-core-kan-fibration` for the non-elementary Kan-core conclusion. It explicitly checks the fibre quasicategory and isofibration hypotheses before applying that statement. Creating a fibre-core lemma would add only a two-line specialization of this existing theorem and the horn definition.
4. Step 5 performs the two marking-only lifts against (iv) and (iii), using the stated generators. This is a definition-level application of the lifting property, with both underlying identity maps specified.

This is a dependency repair, not merely a cut at the character limit: the two formerly nested non-elementary arguments now occupy their own steps, each citing the exact existing theorem that supplies it. No new theorem hides either argument. The remaining steps are retained verbatim: old 1 is new 1, and old 3–5 are new 6–8. The proof dependencies remain the same union of cited ids. All eight texts are below 1000 characters (357, 720, 594, 652, 672, 817, 385, 938).

The statement, statement dependencies, source, proof origin, every Lean field, audit field, imported field, and maintainer-owned field are retained. Only the proof, its recomputed dependency union, status, and split report are updated. There is no statement dispute and no new hypothesis.

## Blueprint, route and searches

I read the chapter and assigned `sk-prop-sf-biduality-general` unit records, the three-level restrictions in SETUP.md, GOAL.md and `coord/dag-sync.md`. I also read the current main-20261015 ancestor `sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.md`. Its historical mapping-complex/coherent-diagram ancestry is preserved; this generic marked-lifting input does not replace a geometric unit step. `blueprint_refs.py ancestor` confirms `prop-coef-integral-exceptional-adjoint`; whole-blueprint searches for marked, cocartesian and core find no blueprint statement of this recognition theorem. The inherited `from.place` is specific and `same_as` remains empty. No chapter/unit record or route binding is changed.

I searched the current DAG for fibre/core/quasicategory and marked-lifting assertions and opened all six existing cited statements in full. In particular, the comparison and core results already state the substantive arguments of old Step 2; no new node is warranted. The accepted generic outer-horn tool use is retained in `split_report.tool_uses`, with its step number updated to 8. The maintainer-owned `tool_uses` field is unchanged.

The item statement and search question are unchanged. I read the inherited Mathlib search results and keep them instead of repeating them: the two semantic phrasings returned ordinary-category cocartesian morphisms or unmarked Quillen fibrations; the Loogle quasicategory/cocartesian query and grep found no marked recognition theorem. The additional independent-search records likewise concern unmarked simplicial sets. These are not matches for a marked map to a sharp quasicategorical base with an exact marking conclusion. No new search is asserted to have run in this repair, and no new node requires a search log.

## Not duplicates

No new nodes. The comparison is precisely the existing composition/initiality statement; the Kan-core conclusion is a specialization of the existing core-fibration statement. Both are cited directly. The existing marked saturation leaf and relative equivalence outer-horn theorem are also reused. No clause of the item has been moved into a new statement.

## Review by Q127

I read delivery-errors B–E in full and checked the repaired proof against the current node statements and HTT 3.1.1.6, with the initial-horn convention obtained by reversing vertex order. The item's sharp base makes every base edge marked. Neither E nor B is assumed Kan. There are no new nodes whose form or source needs independent checking.

Step 1 uses exactly the existing saturation leaf's equivalence between the generator RLP and the closure RLP, and the definition's four generating families. The leaf is for arbitrary marked maps, so there is no fibrancy hypothesis to establish here.

Step 2 cites the generator definition and horn definitions. I checked the only dimension distinction: for n=1 the initial horn is the source vertex; for n at least two it already contains the initial edge. Minimal markings impose only degeneracies. This proves the chosen-lift conditions by expanding the definitions, rather than invoking a missing horn-test theorem.

Step 3 uses the existing composition/initiality statement, which explicitly provides initiality in L(x,alpha), the comparison morphism with its triangle, and the equivalence of targets in E_b. Both t and e are cocartesian before the application; they have the same specified source and the same base edge. The triangle's ordered edges are (t,u,e), and its base is s_1(alpha), making u vertical in E_b. I take this from the statement, not from a construction in that node's proof.

Step 4 cites the fibre definition and the full core-fibration statement. An inner horn in E_b fills over the constant simplex at b by the already established inner-fibration condition, so E_b is a quasicategory. Its map to the point lifts inner horns and lifts the only base equivalence by a degenerate edge at the given source. This is exactly the stated isofibration hypothesis. The induced core map to the point is therefore Kan, and u belongs to that core because it is an equivalence in this fibre. The core is small as a simplicial subset of small E. No comparison between distinct fibres is used.

Step 5 uses the actual marking-only generators. Inclusion K-flat into (E,T) is marked since T contains degeneracies; its composite is constant at b. Lifting (iv) fixes that same underlying inclusion and therefore marks u. The triangle has t and u marked, so the top map for (iii) is marked. Its diagonal also has the same underlying triangle, hence marks the original e, not just an edge homotopic to it. This gives the reverse inclusion of markings. These are the two direct lifting applications, without a hidden saturation/comparison assertion.

Step 6 is the unchanged converse horn calculation: inner lifting handles (i), prescribed-source cocartesian lifts handle n=1 in (ii), and the defining outer-horn condition handles n at least two with its initial edge already marked. Step 7 applies precisely the composition clause of the existing composition/initiality statement to the given two consecutive cocartesian edges; the underlying 2-simplex is retained. Step 8 uses the core node's explicit Kan-edges-are-equivalences clause, preserves the inverse and its witnessing triangles under the given simplicial map, and invokes the relative initial outer-horn theorem. That theorem's assumptions (small quasicategories, inner fibration, n at least two, equivalence on the initial edge, fixed base simplex) all hold. The resulting fillers are exactly the cocartesian-edge definition. The unchanged sharp marking then makes the original map the required marked diagonal.

I tested the low-dimensional cases n=1 and n=2, empty total category, empty Kan parameter, the identity map with sharp marking, and the nerve of the walking isomorphism over a point with only degenerate edges marked. The latter passes the chosen-lift tests but fails (iv); the repaired argument correctly needs (iv) and then (iii) to recover exactness of marking. Thus no inference identifies a selected set of lifts with all cocartesian edges prematurely. The identity map requires every edge marked. An empty total category has no specified sources, so the forward existence condition is vacuous as required.

All sixteen citations were regenerated with literal current statements and checked for their mathematical use above. I verified that `proof_deps` equals their union, every proof step has an explicit boolean `elementary`, no step exceeds 2000 characters, and the retained statement and Lean record compare equal to the repository. No source download, Lean writing, compilation, Lake/build command, agent launch or direct git command was performed.

## Remaining work and validation

No mathematical repair remains. The required server dry run and push are performed with the delivery tool; their final results are recorded below after completion. This is direct delivery under the present brief, with independent review reserved for the maintainer.
