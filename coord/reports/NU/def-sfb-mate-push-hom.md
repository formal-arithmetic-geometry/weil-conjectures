# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/def-sfb-mate-push-hom.json: existing definition, Mathlib leaf via CategoryTheory.mateEquiv at Mathlib/CategoryTheory/Adjunction/Mates.lean:84, inverse body at lines 93–100.
- citations.json: empty list; a Mathlib definition leaf has no proof steps.
- report.md: this report. No new DAG nodes or unit changes.

## Attachments

None. Searched the slopmaster2 WeilConjectures tree by the blueprint id, pushHomOfComapIso, pullIsoOfComapIso, and mate/push terminology. No project declaration gives this item exactly. The upstream master reference has CategoryTheory.Adjunction.pushHomOfComapIso in WeilConjectures/CategoryTheory/ModuleObjects/ChangeOfScalarsSquare.lean:230–231, but the brief excludes master as attachment evidence. Its body agrees exactly with the one-line Mathlib specialization recorded here.

## Wanted sources

None. This is a formal categorical definition; its actual source is the current blueprint and the Mathlib implementation, not an assertion requiring a Stacks tag. No SGA source is used.

## Faults and changes

The imported node had no searches or Mathlib match. Its statement is well typed and faithful to the current source, so it is unchanged. The reference to def-sfb-conjugate-pull-iso introduces the four categories, two horizontal adjunctions, vertical functors, and e; it does not require the conjugation theorem to construct the mate. Retained that statement dependency. Changed only the worker-owned search/match/status/blueprint.same_as/split_report fields. No STATEMENT-DISPUTED correction is needed.

## Unfinished work

None for this item. The general construction is already in Mathlib. Only the required delivery dry run remains to be checked below.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for mate, mate comparison, adjunction, and mateEquiv found the existing def-weil-pbc-adjunction-mate leaf, whose statement explicitly supplies both directions of the general mate bijection. It is more general than the item's specialized definition; no auxiliary node is warranted. Its blueprint.is is null, so it is not a same_as blueprint entry. Imported def-sfb-push-hom and def-sfb-derived-push-hom specialize this definition to coefficient functors; they do not state the generic square construction. lem-trf-adjoint-mate and lem-sf-mate concern conjugation or pasted adjunctions, with narrower hypotheses. The blueprint search 'mate comparison' returned this item and the ringed-site exchange identification; the latter is a particular exchange-map theorem, not this definition. Accordingly blueprint.same_as is [].

## Review by NU

I read the current main-20261015 chapter, the sk-def-sfb-coefficient-comparisons unit (especially formal-input step 1), and the whole def-sfb-mate-push-hom source. I also opened def-sfb-conjugate-pull-iso: its statement has E₁:A→B, E₂:A′→B′, Res₁:B→A, Res₂:B′→A′, L₁:A→A′, L₂:B→B′, and e:Res₂ L₂≅L₁ Res₁. This supplies exactly the input used by our statement, including the direction of e.inv. No result in that node's proof is used.

I read Mathlib/CategoryTheory/Adjunction/Mates.lean:55–119, including the complete inverse definition, and Mathlib/CategoryTheory/Functor/TwoSquare.lean:43–66. Substituting horizontal left adjoints E₁,E₂ and vertical functors L₁,L₂ gives a right-adjoint square e.inv:Res₁⋙L₁→L₂⋙Res₂, and the inverse mate is L₁⋙E₂→E₁⋙L₂. Remembering Lean's left-to-right functor composition, these are exactly the two transformations in the item. Lines 95, 97, 99 respectively insert η₁, apply E₂ e.inv E₁, and apply ε₂. At an object a the component is E₂(L₁(η₁(a))), then E₂((e.inv)_{E₁(a)}), then ε₂ at L₂(E₁(a)); every intermediate object has the displayed type. The associators/unitors in lines 94–100 provide only canonical reassociation. No inverse of the mate, vertical adjunction, exactness, coefficient hypothesis, or smallness assumption is being inferred.

The item is a definition leaf, so there are no proof-step node citations: citations.json is empty. This avoids a spurious lemma restating a clause of the item (D1/D2), or another generic mate node duplicating the existing leaf (C5). The sole statement dependency was checked against its actual statement, rather than its proof (B3/C3/C4). All searches in mathlib_searches were run through msearch.py, including two semantic phrasings and two narrowed/broad grep passes; LeanSearch, Loogle, LeanFinder and grep all returned results. I read the decisive source, rather than treating approximate semantic hits as a theorem match. The first asynchronous LeanFinder output was recovered through its logged returned declaration names; the second full response was read and returned mateEquiv_symm_apply first. No unavailable service is represented as an absence result.

For edge cases, with all functors and adjunctions identities and e the identity, the formula reduces to the identity. An empty source category gives the unique natural transformation, with no nonemptiness assumption. The caveat “not an isomorphism in general” is correct even in the full four-adjunction setting: take A=B=B′=Mon, A′=Set, E₁=Res₁=L₂=U₂=id, E₂=U₁=free monoid, and Res₂=L₁=forgetful. Then e is the identity on the forgetful functor and the mate is the free/forgetful counit. On the trivial monoid its source is the free monoid on a singleton (words of all lengths), while its target is a singleton, so the component is not injective. This is a check of the source's caveat, not a new theorem node or an extra clause in the Lean definition. Mathlib's own docstring at line 81 also warns that mates need not preserve isomorphisms.

I checked delivery-errors B–E against these files: there are no unsplit new statements, unsupported tags, off-unit proof tools, copied proof clauses, or missing construction hypotheses. Nothing was silently repaired or weakened. No Lean, compiler, Lake, live repository, or launcher file was written. The dry-run tool is the only authorized packager.

## Second reading by NU

- Item statement: compared every hypothesis and arrow with main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-coefficient-comparisons/def-sfb-mate-push-hom.md, its unit _section.md and formal-input proof paragraph; exact agreement, including the inverse of e and the noninvertibility caveat. This categorical definition has no Stacks source tag to verify.
- Statement dependency def-sfb-conjugate-pull-iso: opened its node and blueprint statement; the four categories, six named functors needed here and e have the required domains and codomains. The two vertical adjunctions are extra context, not used to form this mate; no conjugation theorem or dependency proof is invoked.
- Construction (the only substantive operation): independently read Mathlib/CategoryTheory/Adjunction/Mates.lean:55–119. With C=A, D=B, E=A′, F=B′, horizontal left adjoints E₁,E₂ and vertical functors L₁,L₂, the input TwoSquare Res₁ L₂ L₁ Res₂ is Res₁⋙L₁ → L₂⋙Res₂, precisely e.inv. The inverse mate lies in TwoSquare L₁ E₁ E₂ L₂, i.e. L₁⋙E₂ → E₁⋙L₂. Verdict: exact one-line specialization of CategoryTheory.mateEquiv, not a theorem asserted only by its proof.
- Component check: at a in A the three arrows are E₂(L₁(a)) → E₂(L₁(Res₁(E₁(a)))) → E₂(Res₂(L₂(E₁(a)))) → L₂(E₁(a)); they are respectively E₂(L₁(η₁(a))), E₂(e.inv at E₁(a)), and ε₂ at L₂(E₁(a)). Mathlib lines 95, 97 and 99 give these arrows; lines 94, 96, 98 and 100 merely reassociate functor composition. Verdict: no missing hypothesis or hidden transport argument.
- Mathlib wrapper: read Functor/TwoSquare.lean:43–66; TwoSquare is definitionally the natural-transformation type, and mk/natTrans are identity wrappers at lines 55/59. Verdict: the stated match requires no additional theorem or coherence assumption.
- Proof steps and citations: there are no proof steps in this definition leaf; proof, proof_deps and citations.json are all empty, correctly. No non-elementary claim is hidden in an elementary proof step.
- New nodes: none; B1–B7 therefore introduce no new-node obligations. Opened existing def-weil-pbc-adjunction-mate, whose inverse formula is the same general construction; it already is a Mathlib leaf, so no duplicate helper is needed. Whole-DAG keyword searches and blueprint_refs searches for “mate comparison” and “mates” were independently run; the other comparison hit is an exchange-map theorem, not this generic definition.
- Project attachments: independently searched the read-only slopmaster2 WeilConjectures and Comparator trees for the item id and pushHomOfComapIso/pullIsoOfComapIso; no attachment found. The upstream master ChangeOfScalarsSquare.lean:230–231 has exactly the recorded one-line expression; used only as a reference check, never as completed proof evidence.
- Edge cases: identity adjunctions with identity e give the identity mate; the empty-category identity square gives the unique transformation; a terminal-category square also gives the unique identity component. In the first worker’s free-monoid example, both vertical adjunctions really exist and the mate is the counit Free(Forget(M)) → M, noninjective for the trivial monoid. Verdict: “not an isomorphism in general” is correct without excluding degenerate categories.
- Independent searches: ran msearch.py with the new semantic phrasing “Beck Chevalley natural transformation obtained by taking the right adjoint square and transposing across the horizontal adjunctions”, a new grep pattern, and Loogle mateEquiv_symm_apply. Recorded the actual eight approximate semantic hits, one grep hit, and Loogle’s unknown-identifier result; none is misrepresented as an exact semantic match or an unavailable service.

Changes: appended the independent searches and their precise verdicts to mathlib_searches and retained the msearch-generated searches.jsonl entries; added this second reading. No statement, dependency, Mathlib specialization or node inventory required repair. The first worker’s sections, including Review by NU, remain intact. The installed delivery tool accepts group and item plus --no-push, without the brief’s trailing dot; its documented syntax is used. All writes are confined to this sandbox, except the explicitly authorized delivery tool’s temporary worktree operations. No Lean writing or compiler/build invocation occurred.
