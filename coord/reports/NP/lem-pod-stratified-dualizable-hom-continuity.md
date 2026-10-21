# Stage-1 delivery: lem-pod-stratified-dualizable-hom-continuity

## Files written

- `dag/nodes/sec-poincare-duality/lem-pod-stratified-dualizable-hom-continuity.json`: statement, split into eleven proof steps; no Mathlib match.
- `citations.json`: one certificate for each step/node citation; quotes copied verbatim from the live statements.
- `report.md`: this report.

No new nodes and no Mathlib leaves. The sandbox initially contained only dispatcher brief markers, with no node, report, or old search log. All inherited fields and the original five searches on the item were retained. Five actual searches made in this sandbox were appended from searches.jsonl. The original statement, title, source, created record, chapter/unit and blueprint ancestry are unchanged. No repository or launcher file was written, no git command was run, and no Lean or compiler was invoked.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the blueprint tag, stratified dualizability, and Hom continuity. The perfect-Hom continuity declarations concern quasi-coherent scheme limits, and the condensed sheaf Ext statements only cover special sources or coefficient fields; no project declaration gives this item. The old upstream TwoColimit path named in other nodes is not present at that exact path in the live checkout, and was not treated as attachment evidence.

## WANTED

None. The complete Hemo--Richarz--Scholbach paper is available locally.

## Corrections and scope

The imported statement is correct as a specialization of HRS Lemma 5.3(2) and its final global-Hom assertion. No statement dispute or unit-route departure arose. Its finite stratified-dualizable condition is exactly Definition 3.3 on qcqs schemes. The argument uses the ordinary uncompleted module derived category throughout.

A tempting shortcut would be to cite the existing Noetherian closed-costalk or constructible Ext-continuity nodes; their hypotheses do not cover this item. The split instead derives the required costalk continuity in Steps 5--6 from the existing qcqs pushforward theorem and the support triangle. Likewise the HRS Theorem 4.13 local scalar model requires locally finitely many irreducible components, so it is not invoked. The dualizable case is proved directly by the duality identities and a K-flat tensor model.

The finite partition is refined by `lem-fix-constructible-open-closed-refinement`, which gives actual maps of leaves to original immersed strata. This avoids an unjustified factorization from image containment and avoids using the Noetherian good-stratification lemma. Induction is on that finite binary tree; the leaf argument, both child-extension arguments and the parent triangle are all written out.

## Not duplicates

No new node is created. Whole-DAG key-word searches and blueprint_refs searches for stratified dualizable, Hom continuity, dualizable, filtered colimit and constructible filtration were read. Existing qcqs pushforward, internal-Hom lower-bound, open--closed internal-Hom formula, exact-colimit ladder, and finite refinement nodes are reused. The Noetherian or finite-coefficient continuity statements are not claimed equal to the item.

## Review by NP

I read HRS Definition 3.3 and equations (3.3)--(3.4) on printed pp. 6--7, Lemma 4.10 and Corollary 4.11 on p. 11, and the full statement and proof of Lemma 5.3 on p. 14, together with the Proposition 5.5 application on p. 15. The paper's proof first proves internal-Hom continuity for a dualizable source, uses extension from constructible locally closed strata and the support triangle, and then applies bounded-below global-sections continuity. The delivered proof follows exactly that route. Its blueprint ancestor is sk-def-perfect, whose present main-20261015 unit text I read; this is the auxiliary HRS continuity input for the rational local scalar-localization comparison. The unit has no proof steps and this item is not its key definition, so no unit record is changed.

I opened the statement of every cited node. Step 1 uses the exact-colimit/cohomology assertion of lem-sfb-rhom-colimit-cohomology-ladder and the explicit good-truncation definition. The truncation projections are quasi-isomorphisms under the common cohomological bound, so strict representatives really preserve the given cocone. This is used whenever a derived functor produces only a cohomologically bounded-below diagram.

Step 2 uses the finite refinement theorem for qcqs schemes, not the separate Noetherian theorem: its statement supplies both qcqs vertices and actual stratum-factorization morphisms. Pullback preserves duals by lem-zl-condensed-lisse-proetale-locality; the constructible-preimage theorem applies to all scheme morphisms; the boundedness node requires only qcqs and the stated stratified dualizability. Thus b_T exists at each vertex with no irreducible-component, regularity or dimension assumption. The scheme-theoretic pullback partition is used for arbitrary vertices, rather than only their underlying images.

In Step 3 the sole nontrivial infrastructure is the closed symmetric monoidal ringed derived category. I wrote the two inverse maps from evaluation and coevaluation explicitly; their inverse equations are precisely the two given triangle identities. This is a direct elementary calculation, not a new duality lemma assumed without a citation. Step 4 uses the K-flat resolution theorem and the sheaf-complex tensor/filtered-colimit theorem, whose statements apply to an arbitrary small ringed site. A fixed K-flat P computes the whole target diagram. The lower-bound theorem states exactly RHom(D^{≤b},D^{≥c}) ⊆ D^{≥c-b}, with no Noetherian condition, and supplies the uniform bound needed later.

Steps 5--6 use the exact support triangle and adjunctions of the condensed open--closed recollement statement. Its hypotheses require the open complement to be quasi-compact, which is supplied at each refinement-tree split. That open immersion is separated, hence qcqs, so the qcqs pushforward theorem applies to j and the exact inverse-image diagram. The cohomology ladder node supplies the connecting squares and the five-lemma node applies at the five terms explicitly listed. The general ringed pro-etale open--closed node supplies exactness and filtered-colimit preservation of i_* on qcqs T; i^*i_* = id reflects the resulting cohomology isomorphisms. Recollement also gives the uniform bound for Ri^!, so there is no unproved bound hidden in the use of the induction hypothesis.

Steps 7--8 cite lem-sfb-open-closed-internal-hom-formulas for exactly its two natural derived sheaf-Hom formulas. The formulas are unbounded and allow arbitrary condensed rings. For the open child the inner Hom has lower bound c-b_U, so the qcqs pushforward theorem applies; for the closed child the costalk diagram has lower bound c and its colimit is already identified in Steps 5--6, and exact filtered-colimit preservation of i_* applies. Both formula statements specify their evaluation/adjunction normalization, which fixes the comparison as the original cocone map rather than an arbitrary isomorphism.

Step 9 uses the other recollement triangle, the exact internal-Hom ladder and the five lemma in the positions explicitly written. The cohomology-isomorphism criterion then gives the derived isomorphism. This completes, rather than merely invokes, the finite tree induction. Step 10 applies the global-sections clause of the qcqs pushforward theorem with common bound a-b; the internal-Hom lower-bound theorem supplies that bound. The ringed-site global-Hom identification and the target-shift comparison identify its cohomology groups with the exact shifted Hom groups of the item. Step 11 writes both naturality equations and scalar linearity using module morphisms and the pulled-back central coefficient action. A bijective linear map is a module isomorphism, so the abelian-group-valued continuity statement supplies every module-valued clause.

Small cases checked: empty Y and zero K give zero groups; a one-leaf tree gives the dualizable tensor calculation; a split two-stratum partition gives the two extension formulas; a constant diagram gives the identity comparison; K=B[m] gives the expected shifted global-cohomology comparison. Negative r changes only the shift, and common target bounds remain independent of the diagram index. Arbitrary condensed rings, non-Noetherian qcqs schemes, and nonconstructible targets are retained. No claim of unbounded-target continuity or finite cohomological dimension is made.

For delivery-errors B--E: no new node or hollow definition; all object notions in the statement retain their definition references; no unattested Mathlib searches; every proof-step citation has a verbatim statement certificate; every non-elementary supporting result is cited; neither the item nor its clauses is moved into a new node; no unproved assertion is borrowed from a cited proof; the finite induction has a base and both child and parent steps. Generic off-unit statements are declared individually in split_report.tool_uses. Every step has fewer than 1100 characters, and none hides a source-called-standard comparison: duality, costalk continuity, internal-Hom extension and global-Hom normalization are explicit. No SGA source is used.

## Unfinished work

None for the one-level stage-1 split. Existing unsplit supporting nodes remain their owners' work.
