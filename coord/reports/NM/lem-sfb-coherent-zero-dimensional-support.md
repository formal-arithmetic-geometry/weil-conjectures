# Stage-1 delivery: lem-sfb-coherent-zero-dimensional-support

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-coherent-zero-dimensional-support.json: item split into six steps; unchanged statement; no Mathlib match for the item.
- dag/nodes/sec-six-functors-basics/lem-sfb-locally-noetherian-zero-dimensional-discrete.json: statement, Mathlib leaf. AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero, Mathlib/AlgebraicGeometry/Artinian.lean:66, with AlgebraicGeometry.IsLocallyArtinian.discreteTopology at line 95.
- citations.json: twelve verbatim statement quotations, one for every step/node citation.
- searches.jsonl: actual msearch log. The earlier item searches remain in its JSON; fresh searches for the item and the leaf are also recorded.

## Attachments

None. Searching WeilConjectures for the blueprint tag, 0B3J, coherent support and zero-dimensional support found no declaration giving the entire item. Related closed-support and zero-dimensional cohomology files have different statements. Mathlib results are leaves, not project attachments.

## WANTED

None. All mathematical sources used here were read locally in literature/stacks-project/.

## Problems found and corrected

The imported item had no proof. Its statement agrees with coherent.tex Tag 0B3J, lemma-coherent-support-dimension-0, and adds only its immediate consequence that zero global sections force the sheaf to be zero. No statement dispute or statement change is needed.

The existing support-construction node does not itself say that the coherent sheaf descends to the support. The proof therefore separately cites clause (1) of lem-weil-pbc-closed-immersion-coherent-equivalence, after establishing local Noetherianity of the support with the two exact permanence nodes. This repairs the tempting but invalid C4 shortcut of taking coherent descent from the support definition alone.

The usual abbreviated proof says that a disjoint union of affines is generated and acyclic. Here the support is discrete, so zero extension is written out directly: this avoids an uncited cohomology-of-infinite-disjoint-unions result. It also avoids adding global quasi-compactness or finiteness of support, neither of which the item assumes. The module-flasque acyclicity node has a stale source label 01E1 (which actually concerns cohomology on an open); the fact used is exactly its statement, and the correct source was read in cohomology.tex Tag 09SY, lemma-flasque-acyclic. I did not edit that other node.

The inherited blueprint.from.node is null. The required ancestor command also prints None, because the old created.item chain has a broken ancestor, although the inherited place explicitly identifies det-thm-sf-ctf-stability-direct-images, proof (3). The delivery preserves this metadata and its via chain and gives the new leaf the same ancestor returned by the tool, with the item prepended to via. I read the current latest sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3); this small Zariski estimate is below the unit route and changes no unit or chapter assertion.

## Not duplicates

lem-sfb-locally-noetherian-zero-dimensional-discrete vs lem-sc-zero-dim-noetherian-finite-discrete: the existing node assumes a globally Noetherian (quasi-compact) scheme and concludes finite discreteness; the new Mathlib leaf assumes only locally Noetherian and gives discreteness for possibly infinitely many points. Its intended use has no quasi-compactness hypothesis.

lem-sfb-locally-noetherian-zero-dimensional-discrete vs lem-sc-zero-dim-noetherian-affine: the existing node assumes Noetherian and separated and concludes affineness and ampleness; the new leaf needs neither global quasi-compactness nor separation and concludes only discreteness.

lem-sfb-locally-noetherian-zero-dimensional-discrete vs lem-sc-zero-dim-noetherian-closed-finite: the existing node concerns a closed subspace of a globally Noetherian T0 topological space, concluding finiteness and closed points in that ambient space; the new leaf concerns a locally Noetherian scheme, whose whole space can be infinite.

lem-sfb-locally-noetherian-zero-dimensional-discrete vs lem-sfb-coefficient-heart-curve-complement: the existing node concerns a generic-point-containing open of a globally Noetherian curve, its finite complement, and condensed coefficient-module recollement; the new leaf has no curve, complement or coefficient hypothesis and is the general scheme-topology tool.

The blueprint searches for support dimension, scheme theoretic support, discrete support, dimension zero, locally Noetherian, Artinian and 0AAX found no blueprint statement giving the new general result. Whole-DAG statement/title/tag searches were checked as well. The leaf is neither a clause of the item (it says nothing about sheaves) nor a relocation of its proof. It is a direct Mathlib specialization; no artificial node for zero extension or gluing is introduced.

## Review by NM

I read coherent.tex Tag 0B3J with its full proof, Tag 01Y5 (the support/descent lemma it invokes), properties.tex Tag 0AAX with its proof, morphisms.tex Tags 01T5 and 01T6, and cohomology.tex Tag 09SY. For the new leaf I also read Mathlib/AlgebraicGeometry/Artinian.lean:66 and :95: installing the locally-Artinian instance from the dimension bound lets Lean infer discrete topology in one line. Both semantic phrasings returned that result; Loogle returned its exact declaration and the recorded grep gave the lines. The item searches returned only Artinian scheme criteria, ideal support facts, generator predicates, skyscraper constructions and complex truncations, none stating the whole coherent-support assertion.

For step 1 I opened pqf-lem-coherent-ft-locnoeth and lem-weil-pbc-scheme-theoretic-support: the first supplies precisely quasi-coherence and finite type, and the latter supplies the annihilating closed immersion and equality of its image with the nonzero-stalk support. The closed-immersion definition gives the homeomorphism to that closed subspace, so the assumed dimension bound is transported without imposing a new condition.

For step 2 I opened lem-weil-pbc-immersion-base-change-lft and used only its clause (2), not its base-change clause. The closed support inclusion is an immersion, so pqf-lem-locnoeth-lft applies with locally Noetherian target X. I opened the coherent-equivalence node: its clause (1) requires both schemes locally Noetherian and annihilation by the defining ideal, exactly what steps 1 and 2 establish. It therefore gives G coherent and F isomorphic to i_*G. The new discrete-topology leaf applies to this Z with the transported dimension bound.

For step 3 I opened the module-stalk definition and closed-pushforward-stalks node. The definition says every germ is locally represented and equality of germs is equality after shrinking. The pushforward node identifies the stalk at i(z) with G_z and explicitly makes other stalks zero. Because singleton opens are smallest neighbourhoods on discrete Z, a stalk element is a section on that singleton; gluing it with zero produces the global section asserted, not merely a generating family over a different ring. Its germ is the desired element, so the section's summand with coefficient 1 locally hits any target element of the evaluation map. Sheaf surjectivity is local; no surjectivity of global sections of O_X onto O_Z is asserted.

For step 4 I checked the flasque definition node: it requires exactly surjectivity for every open restriction. The displayed construction extends any section across i^{-1}U subset i^{-1}V by zero on the open complement in discrete Z. This is ordinary disjoint-open sheaf gluing, and works for infinitely many points with no product/cohomology exactness assumption. Step 5 cites the module-flasque acyclicity statement, not merely abelian-sheaf acyclicity, so its conclusion is the ringed-space module cohomology of the item. Step 6 uses the germ-equality criterion already quoted and sheaf uniqueness to get the zero sheaf, spelling out the final consequence.

I checked B1--B10: the new leaf has a self-contained statement, definition dependencies, empty proof/dependency fields, exact Stacks tag/label, actual searches and precise Mathlib declaration lines; no fake searches or source-only citations. I checked C1--C8 against each opened cited statement and wrote twelve verbatim citations. All cross-unit tools are explicitly declared in split_report.tool_uses with their purpose; they are support/descent/stalk/acyclicity tools, not a replacement of the stability-unit route. I checked D1--D5: the six steps carry the actual proof, and the only new result is a genuine, more general topology lemma already in Mathlib. I checked E1--E7 on the actual hypotheses and objects; neither a finite-support assumption nor ambient separatedness nor reducedness is used.

Edge cases: F=0 and X empty give empty support and zero sheaf immediately; a skyscraper on a closed point gives the expected arbitrary supported stalk; infinitely many disjoint spectra of fields show why global Noetherianity cannot be inserted; a nonreduced Artinian local support remains one discrete point and its module elements extend just as above. These tests validate both the leaf and the assembly. All steps are shorter than 2000 characters, with the longest 708 characters; the gluing/germ arguments are elementary consequences written in full and hide no new non-elementary lemma.

## Unfinished work

None in the stage-1 split. The existing dependency nodes retain their own states; no Lean was written and no compiler, Lake or build was run.
