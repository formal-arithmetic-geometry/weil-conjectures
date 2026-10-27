# Q53: lem-sfb-stack-qcqs-module-adjunction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-stack-qcqs-module-adjunction.json: item, statement, split into four steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-stack-lqc-coherator.json: new statement-only lemma, unsplit; no Mathlib match. This is Stacks 0778 on a single algebraic stack, for all locally quasi-coherent modules with flat comparison maps.
- citations.json: verbatim statements supporting every cited node in every proof step.
- searches.jsonl and search-result-0.txt through search-result-8.txt: actual msearch queries and their returned hits, retained for continuation. The two semantic phrasings for the new lemma both ran, alongside LeanSearch, Loogle and source grep.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag/id, stack adjunctions, algebraic stacks, quasi-coherent adjunctions and coherators. The coherators found there are derived coherators for schemes, not the underived LQCoh flat-comparison functor on arbitrary algebraic stacks. There is no finished project declaration stating this item. No Lean was written or compiled.

## Wanted sources

None. All sources used are present in literature/stacks-project. No SGA source is used.

## Audit and corrections

There was no earlier node, proof, report, search log or delivery result in this item's sandbox on resumption: only dispatcher brief markers. No deliver.py or srvcheck.py process for Q53 was running. The live node was unsplit. Its existing searches and statement were retained; the actual new search outputs are saved as well.

The imported statement is correct. In particular its refusal to assert quasi-coherence of naive big-fppf direct image is necessary. Stacks 077A explicitly constructs the right adjoint as Q composed with ordinary direct image, using the locally quasi-coherent flat-compatible intermediate category. The ordinary module adjunction alone is insufficient. The split supplies this intermediate category and the counit, rather than incorrectly identifying the two direct images.

The existing DAG already has the non-elementary pushforward result as lem-sfb-stack-higher-images-flat-comparison (0765/0771), and the scheme-test and pullback identifications as lem-sfb-stack-quasi-coherent-scheme-restriction. I reused both. Ordinary module adjunction on arbitrary ringed topoi is lem-weil-pbc-ringed-topoi-module-adjunction, not lem-pc-module-pullback-adjunction, whose statement is only about schemes and locally ringed spaces. The fibred-fppf ringed-topos hypotheses are supplied by lem-sfb-fibred-fppf-ringed-inverse-image; no hypothesis on the existence of a continuous functor in a chosen direction is assumed without justification.

Read dag/chapters/sec-six-functors-basics.json and dag/units/sk-thm-sf-ctf-stability.json. Also read the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md (the former source path recorded by the unit is historical). The current proof still assembles direct images. This item is the inherited underived stack-module support input, not the unit's key statement. No realized fields or unit/chapter route were changed. tools/blueprint_refs.py ancestor returns None for this existing created-node chain; the new node inherits node=null and prepends this item to the exact inherited via chain. Its place identifies the coherator input to the module adjunction. Searches of the whole DAG and blueprint for coherator, locally quasi-coherent modules, flat base change property, 0778 and quasi-coherent right adjoints found no existing node stating the new lemma.

## Not duplicates

lem-sfb-stack-lqc-coherator vs lem-sfb-stack-qcqs-module-adjunction: the new lemma has no morphism f and no qcqs hypothesis; it coreflects arbitrary locally quasi-coherent flat-compatible modules H on one stack. The item must first prove that ordinary f_*F lies in that category, apply the ordinary module adjunction, then compose its Hom bijection with the coherator bijection and verify the named comparison. Thus the new lemma is neither the item nor an individual clause of it.

lem-sfb-stack-lqc-coherator vs lem-pc-dq-coherator-adjunction: the latter is a derived coherator for quasi-coherent cohomology on schemes; it does not state underived coreflection from locally quasi-coherent modules with flat comparison maps on algebraic stacks.

lem-sfb-stack-lqc-coherator vs lem-sfb-stack-higher-images-flat-comparison: the existing lemma proves preservation of local quasi-coherence and flat comparisons under qcqs higher direct image. It constructs no right adjoint to the inclusion of QCoh. No existing node has Stacks 0778 as an actual source tag (incidental search text and the decimal source line 40778 are not that tag).

## Review by Q53

I read stacks-cohomology.tex, proposition-direct-image-quasi-coherent (077A), through its degree-zero Hom calculation, and lemma-adjoint (0778), including its presentation/descent proof. I checked the definition-flat-base-change and proposition-loc-qcoh-flat-base-change (0771) for the intermediate category. The new statement specifies local quasi-coherence using each small etale restriction and specifies flat compatibility using the tensor comparison for arrows over flat scheme maps. These are exactly the hypotheses of 0778. The fppf formulation is legitimate because the intermediate objects are fppf sheaves, and the existing 0771 node explicitly identifies the etale and fppf computations. The counit formula in the new statement is the defining Hom formula of this adjunction, not an extra geometric assertion. The new node is deliberately unsplit, with empty proof and proof_deps; the smooth-presentation argument remains its source for a later worker.

For step 1 I opened the full statements of lem-sfb-stack-quasi-coherent-scheme-restriction and lem-sfb-stack-higher-images-flat-comparison. The former really gives quasi-coherent scheme restrictions, tensor comparisons for every arrow, and preservation by precomposition. Hence it implies the local and flat conditions required by the latter. The latter really states the higher-image result for arbitrary qcqs stack morphisms, in both topologies, and explicitly identifies degree zero and its section formula. It requires neither representability nor finite type. The item has precisely its stack, universe and qcqs hypotheses. I use only i=0, so no derived-category assertion is silently needed in the assembly.

For step 2 I opened lem-sfb-fibred-fppf-ringed-inverse-image and lem-weil-pbc-ringed-topoi-module-adjunction, and read stacks-sheaves.tex equation-functoriality-sheaves-modules (06WE) and sites-modules.tex lemma-adjoint-pullback-pushforward-modules (03D7). The first node really provides the ringed-topos morphism and identifies module tensor pullback with precomposition. The second really gives natural Hom bijections for arbitrary ringed topoi, not merely scheme module sheaves. Together they justify every functor in this step. Passing to the displayed full subcategories does not alter either Hom set. The generic adjunction is declared in split_report.tool_uses because it belongs to a different unit; it does not replace a geometric step of the stability route.

For step 3 the new coherator statement gives both the functor Q and its natural Hom bijection with the explicit map a to q_H a. The preceding step already supplies ordinary direct image, and step 1 places its values in Q's domain. Therefore Q(f_*F) is a functor into QCoh, and composing the two natural bijections proves the required adjunction. Taking q at H=f_*F constructs the actual comparison map and proves its naturality. There is no appeal to quasi-coherence of ordinary f_*F.

For step 4 I checked the directions of both bijections: A sends bar h to its ordinary adjunct, whereas B sends h to q_H h. The equation h=B^{-1}A(bar h) therefore gives precisely i_f h=A(bar h). This is a formal substitution into the two cited statements, so this step is elementary. It does not invoke a projection formula, flat base change on arbitrary tests, or a hidden compatibility theorem. citations.json copies the cited statements verbatim; no citation is borrowed from a cited node's proof. All four proof steps are below 600 characters and hide no long subsidiary argument.

I tested the new statement and the assembly on the identity morphism: Qj is the identity up to the adjunction unit, and the comparison on a quasi-coherent module is invertible by the triangle identity. For a morphism from the empty stack the output is the zero module and both Hom sets are singletons. For the punctured-plane open immersion in the discussion preceding 077A, naive f_*O cannot be quasi-coherent: its value at the missing origin is zero, whereas its global sections are k[x,y]. Our comparison is a map, not an asserted isomorphism on all tests, so this example causes no false conclusion. The coherator needs no qcqs hypothesis on the stack; qcqs is used exactly once, for preservation of the intermediate category under the morphism. I checked delivery-errors B–E: self-contained definitions and hypotheses, real source tags, actual logged searches with candidates read, no duplicate, no relabelled clause, no circular citation, and explicit computation of the comparison.

## Unfinished work

No part of the item's natural-language proof remains unfinished. The one new lemma is intentionally statement-only, to enter the stage-1 queue. Required server checks and delivery follow this report.
