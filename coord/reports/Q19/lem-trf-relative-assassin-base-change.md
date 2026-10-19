# Stage-1 delivery: lem-trf-relative-assassin-base-change

## Files written

- dag/nodes/sec-trace-formula/lem-trf-relative-assassin-base-change.json: statement, split into nine complete steps; original statement preserved verbatim.
- dag/nodes/sec-trace-formula/lem-trf-flat-pullback-associated-points.json: new statement-only lemma, Stacks 05DB specialized to the structure sheaf on the source; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-tensor-fields-cohen-macaulay.json: new statement-only lemma, Stacks 045M; no Mathlib match.
- citations.json: one verbatim statement quotation for each citation of every numbered step.
- searches.jsonl: actual msearch.py queries, results summaries and digests. prepare.py is a sandbox-only preparation script, not a delivery file.

## Attachments

None. I searched WeilConjectures in /home/ubuntu/weil-src-slopmaster2 by the exact blueprint tag and item id, and by relative assassin, associatedPoints, associatedPrimes, IsAssociatedPrime, associated, and Cohen–Macaulay terminology. No project declaration supplies this item or either new lemma. The upstream master checkout is not used as evidence of a finished proof.

## WANTED

None. All sources used are present in literature/stacks-project/.

## Problems found and corrected

The imported item was a statement with an empty proof and no proof origin. Its 05DC statement is correct and is unchanged, including the locally finite type assumption, arbitrary quasi-coherent module, arbitrary base change, and the generic-component condition in the residual fibre. There is no STATEMENT-DISPUTED finding.

I made explicit two hypotheses easily lost in paraphrasing the source: the original fibre is locally Noetherian even though S need not be, and kappa(z)/kappa(r) is finitely generated as a field even though z need not be closed. The source's no-embedded-primes sentence is realized through the existing local Cohen–Macaulay associated-prime lemma and the localization prime correspondence. I did not turn that sentence or the tensor-fibre identification into additional nodes: the remaining deductions are given in the item's steps.

The current blueprint main-20261015 does not have a separate node for either new statement. Its retained unit sk-i-curve-zero and the inherited ancestry bind the item to the flat-family component-closure input in the normal-cone/nearby-cycle branch of lem-trf-local-term-locality. This split expands the existing 05DC input used by the 0GSI relative-specialization argument; it does not alter the unit or chapter route. No unit realization fields need modification because this is not the unit's key node.

## Not duplicates

The DAG was searched by tags 05DB and 045M, source labels lemma-bourbaki and lemma-tensor-fields-CM, and flat/associated/field-tensor/Cohen–Macaulay terminology. blueprint_refs.py searches for Bourbaki, tensor fields, associated points, Cohen-Macaulay, 05DB and 045M found no matching blueprint node. No existing node carries 05DB or 045M.

lem-trf-flat-pullback-associated-points vs lem-weil-pbc-associated-primes-flat-base-change: the existing node is a formula for associated prime ideals of M tensor N over a ring map; the new node is the scheme-level flat pullback formula, with stalk-defined associated points and fibre structure sheaves, including the locally Noetherian base hypothesis. The scheme-level passage is substantial, as the proof of 05DB shows; this is not a one-line specialization of the algebraic node.

lem-trf-flat-pullback-associated-points vs lem-trf-relative-assassin-base-change: the new node is an arbitrary flat-morphism formula for ordinary associated points; it says nothing about field extension, relative assassins, or generic points of the residual tensor spectrum. The item still proves the field-tensor generic-point criterion in steps 5–9.

lem-trf-tensor-fields-cohen-macaulay vs lem-pur-cohen-macaulay-field-extension: the existing node concerns Cohen–Macaulay loci of locally finite-type schemes over a field. A field extension finitely generated as a field, such as k(t), need not have Spec locally of finite type over k. The new ring-theoretic tensor theorem is the input used in that field-extension source as well, not a specialization obtained from its hypotheses.

lem-trf-tensor-fields-cohen-macaulay vs lem-trf-relative-assassin-base-change: the new statement concerns arbitrary pairs of field extensions and only their tensor ring's local depth and dimension. It contains no associated-point or relative-assassin conclusion.

## Mathlib searches

I read the item's inherited Q95 search results and retained them. I also ran fresh msearch searches for the item. For each new statement I ran LeanFinder, LeanSearch, Loogle and Mathlib grep, with another phrasing before deciding no match; their actual queries and summaries are recorded in the JSON. Loogle's unknown identifier IsCohenMacaulay is recorded explicitly; the alternate query TensorProduct, IsNoetherianRing returned Rees-algebra and adic-completion results, not 045M. The semantic searches returned flatness/stalk/base-change declarations for the scheme formula, and linear-disjointness, essentially finite-type base change, and finite-module declarations for the tensor theorem. None supplies either full statement. Targeted grep found no associated-point theory in Mathlib/AlgebraicGeometry and no Cohen–Macaulay theorem. The new nodes therefore remain unsplit, not Mathlib leaves. No unavailable service has been recorded as a successful absence result.

## Tool uses

The item's split_report.tool_uses declares three generic off-unit tools: quasi-coherence under pullback, residue-field comparison for fibre-ring primes, and minimality of associated primes of Cohen–Macaulay local rings. They supply exactly the general module, fibre-algebra, and local-algebra inputs that the source uses; they do not replace a unit argument. All other off-unit theorem citations are existing Mathlib leaves. The two new nodes are in this item's unit.

## Review by Q19

I read Divisors 05DC (lemma-base-change-relative-assassin) in divisors.tex, statement and full proof; Divisors 05DB (lemma-bourbaki), statement and proof, for the flat-pullback lemma; and Algebra 045M (lemma-tensor-fields-CM), statement and proof, for the field-tensor lemma. I verified their tags against tags/tags. For 05DB I checked the specialization F=O_Y: flatness of h is exactly flatness of this sheaf over the base, its fibre restriction is O_{Y_z}, and the tensor on the left is h^*G. The source imposes no finite-type condition on G and requires local Noetherianity only of the base. For 045M I checked that finite type means finite generation as a field, not a finite algebraic extension, and wrote the local meaning of Cohen–Macaulay explicitly with the existing depth, dimension and localization definitions.

I opened and read the statement of every node cited by the nine proof steps. citations.json copies those statements verbatim, including their hypotheses; the steps use the following clauses.

1. The fibre-of-base-change node states the exact cartesian square and commuting projection equality. The module-pullback definition explicitly includes the composition isomorphism. Thus the coefficient comparison is a two-line application of these statements, correctly marked elementary, with no assertion about a different module.
2. The field-extension-flat node states flatness of Spec(k') -> Spec(k), and the flat-morphism-base-change node states stability under arbitrary scheme base change. These apply to the square of step 1; neither requires flatness of f or g.
3. The locally-finite-type-base-change node makes X_r locally finite type over k. The locally-Noetherian/lft node requires only a locally Noetherian target, supplied because a field's ideals are 0 and 1. The quasi-coherent-pullback node applies to the arbitrary fibre inclusion and the given F. Its statement does not demand finite generation. These establish all hypotheses of the new flat-pullback node.
4. The new node's displayed equality is precisely the ordinary associated-point formula used here, for h and F_r. The interpretation at z' uses the image of each fibre lying over its indexing point; it is not an unsupported global statement about the relative assassin.
5. Clause (2) of the fibre-ring-primes-residue-fields node gives the required residue-field isomorphism. The affine-spectrum fibre-product node gives Spec(k' tensor_k kappa(z)) together with its projections. The finite-type-morphism definition supplies an actual finite-type affine chart at z, and the finite-type-residue-field node then gives finite generation as a field for kappa(z)/kappa(r). This is valid at a generic point and on a non-Noetherian base. The remaining base-change reassociation is the universal property of the already identified cartesian square.
6. The new field-tensor node requires just one finitely generated field extension. Step 5 provides that extension, so k'/k remains arbitrary. Its statement supplies Noetherianity of T and Noetherian Cohen–Macaulay local rings T_q explicitly.
7. The affine-stalk node's clause (c) identifies the stalk with T_q. Associated-point membership means its maximal ideal is an associated prime, exactly the hypothesis of the existing local Cohen–Macaulay lemma. That lemma says it is minimal. The localization node gives an inclusion-preserving bijection on primes below q, so any smaller prime in T would contradict this local minimality. This proves the no-embedded-points direction without claiming the tensor ring is reduced.
8. The Noetherian-minimal-prime-associated node supplies an annihilator element for every minimal prime of T, using step 6's Noetherianity. The associated-prime-localization node supplies association of its maximal extension in T_q. The affine-stalk node then gives associated-point membership. No finiteness of the original sheaf is used in either direction.
9. The dimension definition node explicitly states the reverse-inclusion correspondence between primes and irreducible closed subsets V(q); the generic-point definition identifies V(q) with the closure of q. Maximality of V(q) is therefore exactly minimality of q. The relative-assassin definition explicitly identifies membership with association in the own fibre. These are the elementary substitutions completing the equivalence.

I checked B1–B10: new nodes have statements only and no embedded proof sketches; all objects and hypotheses are introduced; each specialized notion cites its definition or is written out; TeX uses single logical backslashes; both sources give verified tags and labels; no unjustified Mathlib match or project attachment is claimed; blueprint fields preserve the inherited nearest ancestor and complete via chain. C1–C8 were checked by the step-by-step reading above, including the exact clauses quoted and the three declared tool uses. D1–D5 were checked by keeping the tensor-fibre, finiteness, two association directions and final generic-point argument in the item, rather than restating its conclusion as a child. The two children are independent reusable inputs of the source's proof. No child depends on the item or a later step. All non-elementary steps are shorter than 2000 characters and there is no hidden long lemma.

For E1–E6 I tested the following cases. Empty X and F=0 give empty relative assassins and the equivalence is vacuous. Identity base change gives a field as the residual tensor ring. With X=A^1_k, F=O_X, z its generic point and k'=k(t), the ring k(t) tensor_k k(u) has the nonminimal diagonal prime (u-t): the corresponding closed point upstairs is not associated, so the generic-component condition cannot be omitted. A finite separable tensor that splits into a product of fields has all its points minimal and associated. For an inseparable extension K=k(a^(1/p)) with a not a p-th power, K tensor_k K is K[epsilon]/(epsilon^p): it is nonreduced but its sole prime is minimal and associated. These check both absence of an illicit reducedness/separability assumption and the role of arbitrary field extension. For the flat-pullback lemma, a base field and an arbitrary nonzero vector space G reduce the formula to association of direct sums of O_Y; the zero vector space gives the empty set. I found no false statement, missing hypothesis, wrong fibre, or ambiguous association notion. No SGA source is used.

## Unfinished work

None for this one-level split. The two new statement-only nodes are intentionally queued for their own stage-1 work. No Lean was written, compiled or built; no live-project or launcher file was modified and no agents were started.
