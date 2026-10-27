# Q106: lem-sfb-stack-minimal-versal-power-series

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-stack-minimal-versal-power-series.json: item split in five steps; statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-versal-formal-object-quasi-initial.json: statement, unsplit; no Mathlib match after LeanFinder twice, LeanSearch, Loogle and grep.
- dag/nodes/sec-six-functors-basics/lem-sfb-versal-minimal-subring-descent.json: statement, unsplit; no Mathlib match after the same search families and a second semantic phrasing.
- dag/nodes/sec-six-functors-basics/lem-sfb-versal-descended-base-power-series.json: statement, unsplit; no Mathlib match after the same search families and a second semantic phrasing.
- citations.json: ten entries with verbatim statement quotations for every node used by every step.

## Attachments

None. I searched lean/WeilConjectures by the item tag and by the words versal, miniversal and predeformation. There is no project declaration giving the assertion. Mathlib's occurrences of versal concern generic weak universal properties or a comment in cotangent modules, not formal deformations.

## WANTED

None. The proof sources are available in literature/stacks-project.

## Problems found and corrected

The imported item had no proof. Its source Tag 06T5 works with a finite base-to-residue-field map, whereas the item assumes only finite type. I used the existing lem-sfb-artin-local-test-algebra, whose statement explicitly supplies the localization at the kernel, the finite residue extension, and equivalences of both test and complete-local categories. This does not change the item or add a hypothesis. The preservation of formal objects and the specified-isomorphism lifting condition under this identification is written in step 1.

The inherited blueprint ancestor is null, as printed by tools/blueprint_refs.py ancestor. I preserved it and its full provenance chain, extending the chain through the item on each new node, and named the supporting source lemma in from.place. Whole-blueprint searches for minimal versal, smallest-where-descends, 06HT, 06T2 and 06T3 found no duplicate. The latest blueprint proof was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This is a supporting comparison in the recorded alteration/moduli prerequisite chain, not a replacement of the unit's direct-image route. No unit or chapter record was edited.

## Not duplicates

lem-sfb-versal-formal-object-quasi-initial vs lem-sfb-versal-unobstructed-adic-criterion: both mention Tag 06HT, but the existing node states equivalence of unobstructedness and adic formal smoothness, and its proof establishes essential surjectivity only on Artinian objects; the new node states existence of a compatible morphism to any complete-local formal object, which is needed between the two minimal bases.

The whole DAG was also searched for the three supporting Stacks labels/tags and for versal, minimal subring and incoming formal-object maps. The nodes stack-versal-ring-existence, artin-rs-versal-formal-object and schlessinger-groupoid-hull-criterion assert existence with stronger deformation hypotheses, not minimal descent of an already specified versal formal object. The parent stack-versal-ring-smooth-span compares different residue fields on algebraic stacks; it depends on this item and is neither an available proof of it nor a duplicate of the three new nodes.

## Review by Q106

I read the statements and proofs in formal-defos.tex at Tags 06HT (lemma-versal-object-quasi-initial), 06SY (lemma-versal-object-S1), 06T2 (lemma-smallest-where-descends-versal), 06T3 (lemma-descends-versal), 06T4 (definition-minimal-versal) and 06T5 (lemma-minimal-versal), as well as Tag 0DQX in stacks-geometry.tex. I checked the base convention at Tags 06GC and the discussion in artin.tex explaining the finite-field base choice. The new nodes are respectively exactly the quasi-initiality result, the two minimal-descent properties, and the power-series presentation plus versality of that descent, with the hypotheses on descent stated explicitly. They are genuine earlier arguments in the source, not a renamed pairwise comparison and not clauses of the item. Each remains statement-only with empty proof and proof_deps.

For step 1 I opened lem-sfb-artin-local-test-algebra and checked its last sentence. It gives all three facts used: Noetherian local base, finite residue-field map, and identification of the test and complete-local categories. Thus the finite-map hypotheses of all new nodes are available after localization. For step 2 I checked the quasi-initiality node supplies a map to the object over A1; an Artinian local algebra is itself complete, as its maximal ideal is nilpotent by the cited local-test-algebra node. The definition node's versality supplies a lift over A2 with the prescribed isomorphism, and its pseudofunctor constraints supply the comparison at the fibre product. The local-test-algebra statement explicitly guarantees that fibre product is a test object. This proves (S1), not the stronger (RS), so no unjustified full-faithfulness assumption enters.

For step 3 I checked both hypotheses of the descended-base node against the two conclusions of the minimal-subring node. Both rings and residue markings remain the same as those supplied by those statements. The descended object is then versal, so quasi-initiality can be applied in both directions in step 4. The incoming-map surjectivity is the second property of the minimal-subring node, and is applied to exactly the descended object constructed there. I wrote out the kernel-stabilization proof for the needed surjective-endomorphism fact, directly using finite generation of ideals from the cited Noetherian definition. This avoids treating a ring endomorphism as linear over its source ring: the Mathlib module-endomorphism search hits do not give that specialization. This short elementary calculation is retained in the step. Coefficient regrouping in step 5 is explicitly proved by its coefficient bijection and the identical finite convolution sums from the power-series definition. It is a routine calculation, not a black-box cancellation theorem for power-series rings.

I checked edge cases: constant groupoid, base equal to the residue field, a versal base already minimal, zero formal variables, equal variable counts, and either order of the variable counts. The minimality condition concerns every incoming formal-object morphism, including those not surjective beforehand; it does not assert unique minimal subrings as embedded subrings. The two minimal rings are only isomorphic. All maps and the regrouping preserve the specified identity on the residue field. No claim of canonical isomorphism, no (S2), no (RS), no representability of the deformation category, and no equality of the two variable counts is used.

I checked B--E of delivery-errors against the actual JSON: new statements introduce all objects and explain cross-base formal morphisms inline; their source places are verified labels and tags; their proof fields are empty; searches are actual command outputs, retained in search-results.json and individual search files, with the original log preserved. I read the search hits: ordinary smoothness, Weierstrass factorization, coefficient-subring operations, and categorical universal properties do not state these deformation results. There is no Mathlib leaf. Every proof citation has a verbatim statement quote in citations.json. The proof-dependency union agrees with the uses lists; elementary calculations are written out; no step exceeds 2000 characters. No Lean file, compiler, repository file, or launcher file was written or run as a compiler.

## Unfinished work

None for this one-level split. The three new statement-only nodes are the remaining stage-1 items. The maintainer's independent review remains required.
