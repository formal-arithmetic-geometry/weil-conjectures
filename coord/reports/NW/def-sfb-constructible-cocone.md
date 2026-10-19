# Worker report: def-sfb-constructible-cocone

## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-constructible-cocone.json`: definition, split using its six existing statement dependencies; no Mathlib match.
- `citations.json`: empty list, because the item is a pure definition with no proof steps.
- `report.md`: this report. `searches.jsonl` was written by the required search command.

New nodes: 0. Mathlib leaves: 0. No unit record was changed: this item is not the unit's key statement.

## Attachments

None. Searches for the blueprint id, `constructibleCocone`, and constructible/cocone concepts under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` returned no matching declaration. Upstream master does define `AlgebraicGeometry.ProEtale.constructibleCocone` in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean:219`, but that checkout is reference material, not the finished slopmaster2 branch, so it is not an attachment.

## WANTED

None. The item is a definition specified completely by the current blueprint; no external theorem or Stacks lemma is needed to assemble already-defined data.

## Problems found and changes

The imported definition already named all its constituent notions. Its statement, six statement dependencies, empty proof, empty proof dependencies, and null proof origin are retained. I completed `blueprint.same_as`, actual Mathlib search records, status, and the split report. The imported `in_cycle` flag is retained as required; a read-only traversal of the current statement/proof dependency graph found no path from any dependency back to this item. No statement correction or route departure was necessary.

I searched the whole imported blueprint with `tools/blueprint_refs.py search 'constructible cocone'` and `search 'cocone of categories'`, and the whole DAG and current blueprint with the corresponding names/concepts. The other constructible-cocone hits state object descent, Hom-surjectivity, Hom-injectivity, or the two-colimit theorem, not a second definition of these data. Thus `same_as` is empty. No new nodes were proposed, so there are no new/existing-node duplicate pairs.

## Unfinished work

None in this one-level definition split. The existing dependencies retain their own independent stage-1 obligations. No claim that the cocone is a filtered two-colimit is made here.

## Review by NW

I read `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/def-sfb-constructible-cocone.md`, the chapter record, and the unit record, especially step 9 beginning “The cocone itself”. The node's statement agrees verbatim with this source. The coefficient categories are layer-B derived categories of module objects over pulled-back condensed coefficient rings. They are not replaced by sheaves of modules over discrete coefficient rings. The unit's four descent/two-colimit conclusions are not assumed to construct the cocone.

I opened the full statements of all six dependencies. Here is the check of every constituent of the definition (there are no numbered proof steps to audit):

- `sk-def-sfb-filtered-two-colimit` defines a cocone over a preordered set by transition functors, vertex functors and natural isomorphisms, with no coherence required. Thus the inclusion order on finite extensions inside the fixed algebraic closure is an appropriate index preorder. Its later Obj/Hom-surj/Hom-inj predicates are additional properties, not fields required here.
- `def-sfb-dcons-subfield` explicitly defines the full subcategory of the derived category of modules over `E_X` consisting of bounded complexes with constructible cohomology. It supplies exactly the category at each finite field, for every prime and scheme appearing in the item.
- `def-sfb-constructible-extend-subfield` supplies the restricted functor from the E-category to the F-category for every inclusion E ≤ F. Its statement already names the preservation theorem needed for the restriction; this definition does not silently reprove or strengthen preservation.
- `def-sfb-dcons-qlbar` defines the analogous bounded constructible full subcategory over the pulled-back algebraic-closure coefficient ring. It supplies exactly the vertex.
- `def-sfb-constructible-extend-to-qlbar` supplies the functor from each E-category to that vertex. Its statement explicitly supplies the restriction using the stated preservation lemma; it is not merely a definition of an unrelated scalar-extension functor.
- `def-sfb-constructible-extend-comp-iso` supplies a natural isomorphism from T(F,closure) composed with T(E,F) to T(E,closure), both with source the E-category and target the vertex. This is exactly the comparison field of the cocone definition, including its direction. It is not an assertion of object descent or a converse equivalence.

I also read the five corresponding current blueprint definition files, and the upstream master construction at TwoColimit.lean lines 190–225: its three fields are precisely the transition functor, vertex functor and comparison isomorphism above. This corroborates the intended construction without treating upstream sorry-dependent declarations as closed proofs.

The hypothesis check is specific: each constituent is stated for a prime ℓ and an arbitrary scheme X; no Noetherian, quasi-compact, quasi-separated or finite-type hypothesis is needed or introduced. With E = F (in particular E = Q_ℓ), the cited definitions still supply the transition functor and comparison isomorphism; no separate strict identity law is demanded. For the empty scheme and for a non-Noetherian scheme, the same full subcategories and functors remain defined. The fixed algebraic closure makes the collection of finite subextensions a set, and inclusion is reflexive and transitive by ordinary set inclusion. No colimit existence or small-index theorem is invoked. Thus none of the hidden-hypothesis or universe faults of E1/E4 is used here.

For B–E: the definition is self-contained through exactly the six explicit references; there are no new nodes with incomplete statements, unrun searches, same-tag duplicates, or claims moved out of the item. The empty proof is intentional for a pure definition, as stages/1-dag.md §3(2) requires the notions to be statement dependencies. Consequently C1/C4's proof-citation audit is vacuous, and `citations.json` is empty; the six actual statement-citation checks are the ones above. The data assembly introduces no non-elementary result, no circular proof, and no hidden transport or compatibility claim. The imported statement needed no correction.

Mathlib was searched through the required command with LeanFinder twice (different phrasings), Loogle, LeanSearch, and two source greps, and every query is recorded exactly as run. All services returned results. I read the returned types and relevant source: Grothendieck.lean lines 126 and 159 are constructors for ordinary cocones in a fixed target category; Pointwise.lean line 241 concerns a left Kan extension; ElladicCohomology.lean lines 58–67 define the integral coefficient sheaf. The remaining semantic hits concern profinite-space cocones and locally constant or solid condensed modules. None constructs the bounded constructible derived coefficient diagram or is a one-line specialization giving all this item's data. No Mathlib leaf was asserted.

## Dry run

The required `python3 /home/ubuntu/weil-launcher-nt/deliver.py NW def-sfb-constructible-cocone --no-push` printed `OK (not pushed)` and `preflight passed` on 2026-10-17 (first dry-run commit b948927929). The final report update is checked by the same command again before READY. This sandbox is for second reading only; no delivery was pushed.

## Second reading by NW

- Item statement: compared verbatim with current blueprint `def-sfb-constructible-cocone.md`, node order 1769, and the unit proof's step 9, “The cocone itself”; verdict: prime, arbitrary scheme, finite-subextension index, inclusion order, all four data bullets, and isomorphism direction agree. Its source is the blueprint definition, not a Stacks tag, so no Stacks theorem is invoked by this assembly.
- Cocone data: read the complete statement and current blueprint source of `sk-def-sfb-filtered-two-colimit`; verdict: its fields require only transition functors, vertex functors, and natural isomorphisms, with precisely the listed directions and no coherence obligation. The additional (Obj), (Hom-surj), and (Hom-inj) properties are not asserted here.
- Stage categories: read the complete statement and current blueprint source of `def-sfb-dcons-subfield`; verdict: each finite subextension supplies the full bounded constructible category in the derived category of modules over the pulled-back condensed coefficient ring, with no extra scheme hypothesis.
- Transition functors: read the complete statement and current blueprint source of `def-sfb-constructible-extend-subfield`; verdict: for every inclusion $E\le F$, it supplies the restriction $D_{\mathrm{cons}}(X,E)\to D_{\mathrm{cons}}(X,F)$, with preservation already named in that dependency.
- Vertex category: read the complete statement and current blueprint source of `def-sfb-dcons-qlbar`; verdict: it supplies the required bounded constructible full subcategory over the pulled-back algebraic-closure coefficient ring for every scheme $X$.
- Vertex functors: read the complete statement and current blueprint source of `def-sfb-constructible-extend-to-qlbar`; verdict: the domain is the stage category and the codomain is the vertex for every finite $E$, with the stated preservation restriction.
- Comparison isomorphisms: read the complete statement and current blueprint source of `def-sfb-constructible-extend-comp-iso`; verdict: both sides are functors from the $E$-category to the vertex, and the direction is exactly $T_{F,\Qlb}\circ T_{E,F}\cong T_{E,\Qlb}$.
- Proof steps: none; checked the empty `proof` and `proof_deps` against stages/1-dag.md §3(2). All construction data are supplied by the six statement dependencies; no hidden inference, uncited theorem, transport, or two-colimit claim is made. `citations.json` correctly remains empty because there are no proof-step citations.
- New nodes: none; no new-node statement, source, elementary lemma, duplicate, or Mathlib-leaf obligation arises. The whole-DAG/current-blueprint search for `constructibleCocone` and `constructible cocone` found the item and its property theorems, rather than another definition of these same data.
- Edge cases: checked $E=F=\mathbf Q_\ell$ and a nontrivial finite extension, the zero complex, $X=\operatorname{Spec}(k)$ for a field $k$, and the empty scheme; the categories and functors have the same types and no strict identity law is demanded. No Noetherian, quasi-compact, quasi-separated, or finite-type hypothesis is used. Inclusion is a preorder on the set of finite subfields of the fixed algebraic closure.
- Source-declaration check: read upstream master `TwoColimit.lean` through the construction at lines 219–225; its `T`, `Φ`, and `iso` fields agree exactly with these data. The preceding preservation theorems contain `sorry`, so this is reference evidence only. Independent name/concept searches in slopmaster2 found no matching declaration to attach.
- Independent Mathlib search: ran LeanFinder with the more general query “A family of categories indexed by a preorder with transition functors and natural comparison isomorphisms to a common vertex category”; verdict: the eight returned types (`InverseSystem`, `preordToCat`, `LightDiagram'`, `DirectedSystem`, well-order induction data, `LightDiagram`, `FunctorObjIndex`, and `HasIterationOfShape`) do not construct this cocone. The actual query and results are now in `searches.jsonl` and the item's `mathlib_searches`.

Changes: added this second-reading audit and one independently run Mathlib search; no mathematical statement, dependency, proof, or citation required repair. The delivery script accepts no trailing `.` argument, so the dry run and delivery use the script's documented syntax without that argument.

Final verification: an independent read-only traversal found no dependency path back to the item. The required server dry run with the second-reading changes printed `OK (not pushed) deliver/NW/def-sfb-constructible-cocone at 0600a3f7a0: preflight passed`. Delivery follows using the same script, which repeats preflight before pushing.
