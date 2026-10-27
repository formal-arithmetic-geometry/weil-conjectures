# Stage-1 delivery: lem-sfb-space-integral-extension-qc-open

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-integral-extension-qc-open.json: split into five steps, following Stacks 0G2D; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-integral-factorization.json: statement, unsplit; no Mathlib match for algebraic spaces.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-integral-factorization-etale-base-change.json: statement, unsplit; no Mathlib match for algebraic spaces.
- citations.json: seven verbatim statement excerpts, one for each step/node citation.

## Attachments

None. I searched the whole lean/WeilConjectures tree for the item tag and for algebraic-space and integral-extension terminology. The relevant project normalization files, including NormalizationCover and NormalizationCoverIn, state results for schemes with additional hypotheses, not this statement for arbitrary algebraic spaces.

## WANTED

None. All mathematical sources used are in literature/stacks-project.

## Findings and changes

The imported item was statement-only. I retained the statement, its definition dependencies, and the recorded searches. The existing six searches were rechecked against the actual outputs: the fresh commands ran the same query texts and all their query/tool pairs now occur in this sandbox's searches.jsonl. Fresh results are saved in search-results; I read the declaration signatures, then read Mathlib/AlgebraicGeometry/Normalization.lean at lines 377, 403, 418 and 588–611. Mathlib gives the construction and base-change theorem for schemes, not algebraic spaces, so neither new node is a Mathlib leaf.

The source proof uses relative normalization, but no existing node supplies its universal factorization or etale base-change property for arbitrary algebraic spaces. I created these two inputs rather than copying the item or its open-extension conclusion into another node. No extra node is created for normalization in an integral morphism: the final step proves it directly by the universal property. Likewise quasi-compact composition is a two-line fibre-product calculation, and the diagonal of a monomorphism and base change of an open immersion are written out.

Before creating the nodes I searched all DAG nodes by tags 0822, 0823, 0825, 0ABP, 0G2D, by relative normalization, and by initial/universal integral factorization; I also read scheme-only normalization nodes and the moduli-chart predicates. tools/blueprint_refs.py searches for normalization, relative normalization, 0823, 0ABP, integral factorization, etale normalization, and normalization of algebraic found no blueprint node stating either proposed result. The exact item has no blueprint match. The ancestor command returns None, consistently with the item's existing blueprint.from.node=null; the new nodes retain that computed ancestry and prepend the item to the inherited via chain. The place explains the dependency chain through the current latest det-thm-sf-ctf-stability-direct-images proof (3), not an obsolete snapshot. I read that latest proof and the chapter and unit records; the current work is the Tag 0G2D prerequisite inside the existing alteration route and does not replace the unit route.

The split_report.tool_uses declares the existing generic tools explicitly. lem-a1-space-open-chart-tests comes from another unit and is used only for etaleness of an open immersion. The other permanence and compactness nodes supply general properties before forming normalization; none substitutes for the unit's geometric argument.

## Not duplicates

lem-sfb-space-integral-factorization-etale-base-change vs lem-sfb-dm-finite-normalization-charts: the existing node starts with a smooth finite-type DM stack over a field and a finite etale cover of a dense open, and asserts finite normalization and special additional compatibilities; the new node treats an arbitrary quasi-compact separated morphism of algebraic spaces over any scheme and the universal property under etale base change, without smoothness, normality, finite type, density or finite-cover hypotheses.

lem-sfb-space-integral-factorization-etale-base-change vs lem-sfb-stable-abelian-level-normalization: the existing node concerns a particular level cover of the stable-curve moduli stack and finite scheme representability, not etale base change of an arbitrary universal integral factorization.

lem-sfb-space-integral-factorization-etale-base-change vs def-sfb-moduli-normalization-tests: the existing node defines a scalar-compatibility predicate on specified maps and normal finite-type charts; it does not prove that a normalization exists or that its universal property survives an arbitrary etale pullback.

The factorization node has no existing node sharing its source tags. The scheme nodes lem-weil-pbc-relative-normalization and lem-sbc-relative-normalization-universal-property cannot be applied to algebraic spaces by a one-line specialization. def-sfb-moduli-chart-normalization is a predicate on chart data and explicitly disclaims existence; it is not the new existence theorem.

## Review by Q35

I read Stacks decent-spaces.tex, lemma-extend-integral-morphism (0G2D), including its full proof. For the first new node I read spaces-morphisms.tex, definition-normalization-X-in-Y (0822) and lemma-characterize-normalization (0823), including the integral-closure construction and the uniqueness characterization. For the second I read lemma-properties-normalization (0ABP), whose first clause allows etale algebraic-space base change, together with 0823 to express the result without introducing a hollow normalization definition. Both new nodes introduce their own base scheme, spaces, morphisms, representable integral predicate, separated diagonal, compactness tests, and quantifiers; their proofs are empty and they contain no proof sketches.

Step 1 uses exactly the first assertion of lem-sfb-space-integral-qcqs-permanence for the integral map pi, and the separated-composition clause of lem-sfb-space-separated-fp-composition. I opened both nodes and checked that their assertions concern arbitrary algebraic spaces over a scheme, not only fields. For j, the proof of monicity on scheme tests and its isomorphism diagonal supplies separatedness directly; no quasi-separatedness of B is assumed.

Step 2 takes the all-quasi-compact-space test definition from lem-sfb-space-quasicompact-fppf-local, not its descent theorem. With T quasi-compact, j gives V_T quasi-compact and pi gives Z times_V V_T quasi-compact. The equality with Z times_B T is fibre-product associativity. I read spaces-morphisms.tex lemma-composition-quasi-compact (03HG), whose proof is precisely this transitivity calculation. This is elementary and needs no new node.

Step 3 applies the full statement of the new factorization node only after steps 1–2 establish its quasi-compact and separated hypotheses. Its universal property quantifies over every integral B-space, which is exactly what later restriction and uniqueness use. I did not cite a definition as though it established existence.

Step 4 uses the explicit etaleness clause of lem-a1-space-open-chart-tests (I read its scheme-test statement), then the new base-change node with W=V. Its representable-etale hypothesis holds because j is a representable open immersion. The isomorphism Z times_B V = Z is justified on sections by the inverse z maps to (z,pi(z)); j's monicity ensures uniqueness. This is not an identification requiring B or Z to be schemes.

Step 5 uses the base-change node's full unique factorization conclusion, quoted verbatim in citations.json. Since pi is integral, it is a permissible target and gives h with ha=id. To prove the other composite is the identity I compare ah and id as maps into the integral V-space E_V; each has the required source and base composites, so uniqueness applies. I read lemma-normalization-in-integral (0825) as a check, but do not invoke it without a node: the proof writes out that consequence itself. Finally a scheme test of E_V to E is the open subscheme T times_B V of T, so the final open immersion follows directly from the meaning already fixed in the item.

I checked empty V (then Z is empty and normalization in the empty object may be empty), empty Z, V=B, and integral maps with non-injective coordinate-ring maps. The universal-property statements do not impose dominance, reducedness, normality, noetherianity or surjectivity and remain valid in these cases. In particular no false claim that the normalization map must be surjective is made. Only separated morphisms are used in the new existence node, a valid specialization of the source's qcqs hypothesis. I checked each proof use against the cited statement and verified every citations.json quote is an exact substring. The proof steps are 443, 419, 303, 534 and 748 characters, so none exceeds 2000 characters and the full assembly is under 3000 characters. B–E of delivery-errors were checked against the open sources and node statements: no hidden non-elementary comparison, new restatement clause, uncited descent, stronger missing hypothesis, or cycle is introduced.

## Unfinished work

The two new statement-only normalization inputs remain stage-1 items, as required for a one-level split. No Lean was written and no compiler, Lake or build was run. No repository or launcher file was modified.
