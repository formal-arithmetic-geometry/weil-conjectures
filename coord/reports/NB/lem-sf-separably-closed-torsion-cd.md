# Stage 1 repair: lem-sf-separably-closed-torsion-cd

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-separably-closed-torsion-cd.json`: repaired split; no new nodes, no Mathlib leaves.
- `citations.json`: current verbatim statements for every proof citation.
- `report.md`: replacement report matching the repaired proof.

## Attachments

No exact project declaration found by the blueprint id or point-cohomology keyword searches in the read-only slopmaster2 source. PointCohomology.lean:206 proves positive-degree vanishing only for the constant integer sheaf. Its section-exactness instances are useful partial results, but are not declarations stating every clause of this item. No compiler was run.

## WANTED

None.

## What was wrong or corrected

The landing return says that `def-sc-etale-torsion-cd` changed since review. I reread its current statement: torsion means every local section is locally annihilated by a positive integer, without a single annihilator for the entire sheaf; cohomology is ordinary derived global sections. The item statement already has exactly that meaning through its definition dependency and remains unchanged. The delivered proof incorrectly used `lem-exc-field-discrete-modules` for all torsion sheaves, although that statement assumes a finite commutative coefficient ring. An abelian torsion group such as Q/Z need not admit such a coefficient ring. The repair removes that citation and uses the existing arbitrary-abelian-sheaf equivalence and section formula. The earlier report contradicted the delivered proof about its citation route; this replacement describes only the repaired route.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches found the stronger `lem-kun-0ezp` and `lem-kun-03qu-sep-closed`, and the equivalent torsion-dimension formulation `lem-kun-cd-sep-closed-point`. The latter remains in same_as. The proof retains the blueprint equivalence route using existing tools rather than creating another point-vanishing node. The two cross-unit equivalence/section tools are declared in split_report.tool_uses; no new maintainer tool_uses field is set.

## Review by NB

I read the item's master blueprint source, its chapter and unit records, the revised definition source and current `def-sc-etale-torsion-cd`, and the statements of every dependency of the delivered item. The unit uses this point bound before the finite-type bound; nothing in the chapter or unit route is changed. I read Stacks etale-cohomology.tex, Tag 04JQ (`lemma-equivalence-abelian-sheaves-point`) and Tag 04JM (`lemma-global-sections-point`), including their proofs, and the resolution definition `def-weil-pbc-etale-cohomology`. No new-node source needs review.

Step 1 takes exactly the additive equivalence for arbitrary abelian sheaves from `lem-exc-abelian-sheaves-gmodules`. Its hypotheses hold with K^sep=K, Omega an algebraic closure containing K, and the induced geometric point; K is separably closed, so its absolute Galois group is trivial. Exactness is spelled out by preservation of kernel and cokernel universal properties. Step 2 uses `lem-exc-field-sections-stalk-invariants` at the finite separable intermediate extension L=K of degree one. Its bijection is restriction to germs and is natural in sheaves, so on abelian sheaves it respects group operations. For trivial G the invariant subgroup is the entire stalk; thus sections is the exact equivalence, without any coefficient-finiteness hypothesis. Step 3 uses the displayed K-injective resolution formula from `def-weil-pbc-etale-cohomology`; its existence is part of that statement. The elementary kernel/image calculation is written explicitly and shows vanishing in positive degrees. Its last inference uses the entire current definition of `def-sc-etale-torsion-cd`, including its field abbreviation and local torsion quantifier. All citation quotes are verbatim current statements, not facts taken from their proofs.

I checked zero sheaves, constant Z/n, constant Q/Z (no uniform annihilator), and a non-torsion constant Z sheaf: the argument proves vanishing for all of them and then restricts to the required class. It also works in positive characteristic for separably closed fields that are not algebraically closed: the geometric point uses Omega but G=Gal(K/K) is still trivial. Degree zero is not asserted to vanish; the proof uses q>0 throughout. B--E checks found no new statement, duplicate node, unsourced non-elementary step, coefficient narrowing, or cycle introduced by the cited tools. Existing Mathlib search records and their search log are retained unchanged; no new searches are claimed. The return is repaired by substantive proof and citation changes, and the required delivery command rebases packaging onto current origin/newtargets-dag.

## Unfinished

Nothing mathematical remains in this one-level split. A fresh second reader must review the repair and deliver it; this worker only dry-runs.

## Second reading by NB

- Item statement: checked every quantifier against the master blueprint `lem-sf-separably-closed-torsion-cd.md`, the current `def-sc-etale-torsion-cd` and its original blueprint definition; PASS. The sheaf is abelian, torsion is local with no uniform annihilator, and only positive cohomological degrees vanish. The unit and chapter sources were read; this proves the point bound on their prescribed route.
- Step 1: checked the full statement of `lem-exc-abelian-sheaves-gmodules` against Stacks Tag 04JQ, `lemma-equivalence-abelian-sheaves-point` (etale-cohomology.tex:9078); PASS. K is its own separable closure, Omega is an algebraic closure (also for imperfect K), and Gal(K/K) is trivial. A discrete action of the trivial group has no additional data. The additive equivalence preserves kernel/cokernel universal properties because its inverse gives the inverse bijections of morphism sets, so exactness is a few-line categorical consequence, not an uncited theorem about torsion coefficients.
- Step 2: checked the full statement of `lem-exc-field-sections-stalk-invariants` against Stacks Tag 04JM, `lemma-global-sections-point` (etale-cohomology.tex:8668), including its restriction-to-germs map and naturality; PASS. L=K is a finite separable extension of degree one, H_L is trivial, and the germ map preserves the abelian operations since restriction maps do. This identifies global sections naturally with the exact stalk equivalence of step 1; no finite coefficient ring is required.
- Step 3: checked both cited statements, `def-weil-pbc-etale-cohomology` and `def-sc-etale-torsion-cd`, and the resolution definition `def-weil-pbc-kinjective-resolutions`; PASS. The cited cohomology statement explicitly includes existence of a K-injective resolution. Its quasi-isomorphism with F in degree zero implies zero positive cohomology sheaves. Preserving kernels, cokernels and their kernel-defined images identifies cycles, boundaries and their quotient after sections, which is the elementary calculation written in the step. It proves exactly the required ordinary derived-section vanishing.
- New nodes: none; B1--B7 and the independent new-node Mathlib-search requirement have no new node to check. Existing equivalents `lem-kun-cd-sep-closed-point`, `lem-kun-03qu-sep-closed` and `lem-kun-0ezp` were opened; no duplicate is introduced. The two existing cross-unit statements are generic tools realizing the blueprint equivalence argument, and are requested only in `split_report.tool_uses`, not the maintainer-owned field.
- Edge cases and attachments: PASS for the zero sheaf, constant Z/n with n=1, constant Q/Z, non-torsion constant Z, q=1 and arbitrary positive q. q=0 is deliberately not a vanishing conclusion; the empty scheme is not Spec of a field and does not enter the hypotheses. Read slopmaster2 `WeilConjectures/AlgebraicGeometry/Sites/PointCohomology.lean`: its theorem at line 206 is only for the constant integer sheaf, and its section-epimorphism instances do not state this item. Name searches in slopmaster2, upstream master and `dag/lean_names_upstream.json` found no exact attachment; upstream sorry declarations were not used as finished proofs.
- Citations: PASS; independently compared all four quotes in `citations.json` byte-for-byte with the full current cited node statements. Every non-elementary input in the repaired proof is supplied by those statements; no cited node's internal proof is used.

Changes: appended this independent source, step, edge-case and citation audit. No mathematical repair was needed, so the item statement, three proof steps, citation quotes, original worker sections (including `## Review by NB`) and search records are preserved. No new searches or Mathlib leaves are claimed.
