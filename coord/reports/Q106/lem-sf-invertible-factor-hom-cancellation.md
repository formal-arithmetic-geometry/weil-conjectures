# Q106 — lem-sf-invertible-factor-hom-cancellation

## Files written

- dag/nodes/sec-six-functors/lem-sf-invertible-factor-hom-cancellation.json: item, statement unchanged, complete nine-step proof; status split.
- dag/nodes/sec-six-functors/lem-sf-quasi-inverse-hom-bijection.json: new statement, Mathlib leaf. A functor with a specified quasi-inverse induces bijections on Hom sets, even without triangle identities for the supplied isomorphisms.
- citations.json: a verbatim statement quotation for every step/node citation.
- searches.jsonl: actual msearch.py output log. write_split.py is sandbox-only preparation, not a delivered project file.

## Attachments

None for the whole item. The search of WeilConjectures by blueprint tag and by invertible/Hom/cancellation concepts found CategoryTheory.MonoidalClosed.isIso_ihomTensorToIhom in WeilConjectures/Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean:311, with its defining evaluation equation at :290–300. Its proof contains no sorry, but this only proves the target-twist comparison, with Mathlib's left-tensor adjunction convention. It does not state simultaneous cancellation, all the requested naturalities, or both evaluation normalizations. ihomTensorObjWhiskerRightIso in Rigid/Braided.lean:193 has a different source and target and assumes an exact pairing. Neither is an attachment for this whole item. For the new generic lemma no matching project declaration was found; the three matching declarations are Mathlib declarations.

## WANTED

None. The source is present locally; this is an agent-written categorical consequence of it.

## Defects and corrections

No statement dispute. The original item was unsplit, with a complete statement and search history but no proof. I retained its statement, sources, creation metadata, ancestry and recorded searches. Those existing searches record no exact Mathlib match and correctly distinguish rigid Hom-set bijections from the internal-Hom comparisons. I read their results and the corresponding categorical-core source rather than rerunning the same questions.

The new proof makes two easily missed details explicit: arbitrary two-sided inverse-object isomorphisms need not satisfy triangle identities, and an isomorphism J -> J' acts with its inverse in the contravariant internal-Hom slot for simultaneous cancellation. The new Mathlib leaf expressly accepts arbitrary quasi-inverse data via Equivalence.mk. The comparison maps themselves depend only on evaluation and symmetry, not on a chosen inverse object, so their canonicity does not require coherence of the supplied inverse-factor isomorphisms.

The unit and chapter records were read and left unchanged. This item is not a unit key statement. It is the formal cancellation argument inside the ancestor's geometric generic-fibre step, not a replacement of a geometric or coefficient route. No SGA source is used. All edits are in the assigned sandbox; no git command, Lean writing, compiler or Lake/build invocation was used.

## Unfinished work

None in this one-level split. The new child is a Mathlib leaf with no proof or hidden sublemma in its statement. No new unsplit child is introduced.

## Not duplicates

lem-sf-quasi-inverse-hom-bijection vs lem-trf-fully-faithful-ess-surj-equivalence: both concern Tag 02C3, but the existing statement goes from bijective Hom maps and essential surjectivity to existence of a quasi-inverse. The new statement goes from given quasi-inverse functors and arbitrary natural isomorphisms to bijectivity of the actual Hom map. The existing node does not assert this direction.

lem-sf-quasi-inverse-hom-bijection vs lem-trf-right-fraction-dense-subcategory: the existing node proves an equivalence between two specified right-fraction localizations under Ore and density hypotheses, not the general full-faithfulness consequence of arbitrary quasi-inverse data.

The full DAG was searched by quasi-inverse, full faithfulness, equivalence, tensor and Stacks tags; blueprint_refs.py searches included 'invertible factor', 'tensor equivalence', 'internal hom', 'fully faithful equivalence', '02C3', 'quasi inverse' and 'equivalence of categories'. No blueprint node states the new lemma. The item also is not lem-sf-twist-interchange: that node has scheme/coefficient/perfectness hypotheses and only the target-twist conclusion; the item proves both comparisons for arbitrary objects of an abstract closed symmetric monoidal category. lem-pc-dualizable-tensor-hom-equivalences assumes an exact dual pair in a particular derived category and gives different Hom-set bijections, so cannot supply full faithfulness from the item's two unnormalized inverse isomorphisms.

## Review by Q106

I read categories.tex at categories-lemma-invertible (Tag 0FFM), including the quasi-inverse argument, and categories-remark-internal-hom-monoidal (Tag 0GWJ), including the definitions of evaluation and transposed tensor maps. These are ingredients, not a claim that Stacks states the whole item verbatim. I also read the project's categorical-core proof isIso_ihomTensorToIhom and the related braided cancellation isomorphism, and read the statements of the ancestor, its twisted-bidual transport child, and lem-sf-twist-interchange. The proof_origin therefore correctly says agent. For the new lemma I read Tag 02C3 with the preceding definition of equivalence, Mathlib/CategoryTheory/Equivalence.lean:349–354 and :542–552, and Mathlib/CategoryTheory/Functor/FullyFaithful.lean:167–175. Equivalence.mk adjusts the unit while keeping the functors: its fullyFaithfulFunctor.map_bijective is the exact one-line match. Every search entry in the new node is copied from a real command in searches.jsonl; broad searches are distinguished from the final anchored grep that provides file and line evidence.

I checked every cited statement with its file open. Step 1 uses def-sfb-monoidal-category for exactly the tensor bifunctor and natural associator/right unitor that construct both composite isomorphisms. It does not infer any evaluation/coevaluation triangle. Step 2 applies the new leaf to those two composites, whose hypotheses match verbatim, and obtains essential surjectivity separately from the already displayed object isomorphism. The monoidal definition supplies the explicit convention for associators.

Step 3 uses only the adjunction bijections explicitly assumed in the item; their naturality gives the uncurrying formulas written there. Step 4 cites the new leaf for the first and third Hom-set bijections and the monoidal definition for the parenthesis changes. It calculates postcomposition with the actual t, including the permutation chi, so an arbitrary abstract isomorphism is not substituted for the normalized map. Step 5 needs no additional theorem: surjectivity at the target produces a right inverse, and injectivity at the source makes it a left inverse. Step 6 cites the same two statements and writes the entire chain for postcomposition with the actual s; its domain is Z tensor (X tensor J), with the inverse associator inserted explicitly. No Yoneda theorem or representability lemma is being silently imported: the inverse test is proved in step 5.

Steps 7 and 8 cite the monoidal definition for tensor functoriality and associators. Evaluation naturality comes from the item's natural adjunction, and braiding naturality and symmetry are assumptions of the item, not inferred from that definition. I checked the uncurried formulas on both sides of both naturality identities. In step 8 the second map is [1_X tensor u^{-1},1_Y tensor u]; the u and u^{-1} cancel after uncurrying. Step 9 uses tensor preservation of composition and identities from the monoidal definition and composes the defining equations with the actual inverses. This proves the inverse normalization and inverse naturalities, rather than merely labelling them canonical. All these elementary steps contain their arguments; the substantive internal-Hom bijection steps 4 and 6 are marked non-elementary and cite the exact full-faithfulness leaf they use.

For small cases I checked J=I=1, where both comparisons reduce to the unit constraints and identity on internal Hom. I checked X=1 and Y=1, which impose no dualizability condition on the other argument. A terminal category makes all formulas identities. In modules, an invertible rank-one module gives exactly tensor-Hom cancellation, for arbitrary X, including non-projective X. For shifted invertible complexes the symmetry chi is retained, so it carries the Koszul sign rather than silently replacing it by an unsigned swap. Choosing inverse-object isomorphisms scaled independently by units changes neither definition of t nor s and is allowed by the new leaf. Finally changing a trivialization J -> J' by a scalar gives the expected covariant scalar for t and cancellation of scalar/inverse scalar for s. These tests also verify why no compatibility condition on the inverse-object isomorphisms may be added.

I checked delivery-errors B–E: the one new node is self-contained, statement-only, properly sourced by tag and label, and has an exact Mathlib match with lines; it neither restates an item clause nor packages an elementary tensor rearrangement. Its implication is not in the existing same-tag node. Statement definitions are either cited or spelled out. Every step citation has a verbatim quotation in citations.json. The graph only adds edges to the generic leaf and existing definitions; there is no reverse edge. No step exceeds 2000 characters or hides a separately assumed comparison. The complete proof of each comparison, rather than the item's conclusions moved into children, is in steps 4–6.
