# Q63 stage-1 delivery: lem-pd-internal-oplax-resolving-components

## Files written

- `dag/nodes/sec-poincare-duality/lem-pd-internal-oplax-resolving-components.json`: statement node, now split into six steps. The statement and statement dependencies are unchanged. Mathlib has the generic localization formula, already represented by an existing Mathlib leaf, but does not state this item with its internal resolving preservation and specified normalization data.
- `citations.json`: one checked verbatim statement excerpt for each step/node citation.
- `report.md`: this report and direct-delivery self-review.
- `searches.jsonl`: the search command's original log. `write_split.py` is a sandbox-only JSON preparation script, not a project change.

New nodes: 0. New Mathlib leaves: 0. All ingredients were already present.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, internal/oplax terminology, and the pro-etale module-derived pullback implementation found no declaration covering every clause. `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperLowerStar.lean:176-177` even leaves `AlgebraicGeometry.ProEtale.CondensedRing.preservesKFlatComplexes_mapMod_upperStar` as `sorry`; its existence is not an attachment for the whole item. The project generic adjunction projection maps concern different statements.

## WANTED

None. The needed source and generic localization implementation are available locally.

## Errors and changes

The imported item had no proof. Its two representative comparison maps have the correct direction and its hypotheses suffice. No statement dispute or extra flatness hypothesis was needed. In particular the proof does not silently replace the actual internal localized arrow with the independently specified ringed tensor-pullback arrow.

The substantive reduction is to the already stated generic lifting formula: once the source and target resolution factors have been identified as a and c, the component is c inverse followed by q(b) followed by a (composition read right to left). The unit has the identity target comparison, giving q(u) followed by eta. No new node merely restates either clause.

The inherited blueprint ancestry is rooted at the seeded `nt-target-poincare-isiso`, not an imported blueprint node. `tools/blueprint_refs.py ancestor` reports `None`; the inherited `from.node: null` and `via` are retained. The exact inherited place is retained and `same_as` is checked as empty. I read the current `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-verdier-exchange/_section.md`, including the evaluation/composition/coefficient comparison requirement; this item remains a categorical operation-comparison ingredient below that route. The repository's older unit record and chapter assignment are not edited.

The historical brief names a missing `coord/dag-sync.md` and older checkout paths; the explicit current read-clone paths in this assignment were used. Nothing in the repository or launcher was written, no git command was run there, and no Lean/compiler/build command was run.

## Unfinished work

No mathematical part of the assigned stage-1 split remains. The reused unsplit or sorried dependencies are separate DAG items, not finished Lean proofs. This delivery does not claim stage 2 or stage 3 completion.

## Not duplicates

No new nodes exist, so there are no new/existing pairs to justify. Before settling on reuse I searched the whole DAG for 0G7E and 07A4 and the concepts K-flat pullback, resolving localization, and component lifting; I read the actual statement fields rather than their proof bodies. Whole-blueprint searches with `tools/blueprint_refs.py search` for `K-flat`, `oplax`, `localization`, `pullback`, and `tensor` found the general tensor/derived constructions but no other blueprint node stating this full internal component package. All facts needed are cited using their existing IDs.

## Mathlib search and source check

The original item's five search records are retained. The Q63 `msearch.py` log supplies fresh LeanFinder, Loogle, grep and LeanSearch searches, plus an alternative semantic phrasing. The successful results are recorded exactly by tool and query, with their actual hit summaries and digests. No unavailable service was treated as absence.

I read `Mathlib/CategoryTheory/Localization/Predicate.lean:332` (`CategoryTheory.Localization.liftNatTrans_app`) and `Mathlib/CategoryTheory/Localization/Bifunctor.lean:170` (`CategoryTheory.Localization.lift₂NatTrans_app_app`). They give precisely the conjugation formula for specified lifting isomorphisms, but not the item’s internal sheaf-module preservation and comparison normalizations. The already existing `lem-weil-pbc-localization-universal-property` states the one-variable component formula and identity/composition compatibility, and is a Mathlib leaf. Applying it successively, with a functor category as target for the first variable, gives the needed two-variable assertion without creating a duplicate Mathlib leaf.

## Review by Q63

I read Stacks `sites-cohomology.tex`, Tags 0G7E (`lemma-pullback-K-flat`), 07A2 (`lemma-tensor-product-K-flat`), and 07A4 (`lemma-pullback-tensor-product`), and checked these tags against `tags/tags`. The Stacks route is flat-term K-flat models, preservation of those models under ringed pullback, closure under signed direct-sum total tensor, and localization of the ordinary tensor arrow. Stacks 07A4 alone does not assert our specified internal component identities. I therefore mark the proof as agent-written, give its exact model-map calculation, and use existing normalization and localization statements for the additional content. No SGA route is involved and no new node needs a source check.

Step 1 uses four statements that I opened. `lem-pd-section-kflat-tensor-comparison` identifies the internal and section resolving classes, gives the fixed total comparison, and explicitly states that the regular degree-zero module is resolving. `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` explicitly preserves K-flat complexes with flat terms. `lem-sfb-internal-module-operations-transport` explicitly gives E_X F_i isomorphic to F E_Y, for the same pulled-back coefficient rings. `lem-pur-kflat-total-tensor-model` explicitly gives unbounded closure under total tensor. Combining these gives both internal pullback preservation and internal total closure; no assertion about a merely K-flat complex lacking flat terms is substituted. The sites are small relative to module sheaves exactly as in the item; none of these applications identifies the independent site universes.

Step 2 uses the specified-counit clause of `lem-weil-pbc-kflat-tensor-pullback-computation-universes`, not just an object-level formula for derived pullback. `lem-pd-section-derived-pushpull-normalization` explicitly says its canonical comparisons are compatible with the resolution comparison transformations. In that square the ordinary operation comparison, gamma and localization factors are isomorphisms, and epsilon is an isomorphism on the section model, so G_X(eta) and then eta are isomorphisms. Reflection follows from the quasi-inverse of G_X. I checked the four models A, B, Tot(A tensor B), and R_Y[0] against Step 1. This avoids inferring internal counit invertibility from the mere existence of a derived functor.

Step 3 writes both restrictions and all source/target comparison maps. The K-flat comparison node states the canonical r maps with the required direction (localized total to derived tensor). Consequently the source comparison is eta_Tot L(r_Y inverse) and the target comparison is r_X inverse (eta_A tensor eta_B). Their invertibility is only composition, functoriality, and the inverse equations already established. This is marked elementary; it does not add a new comparison theorem.

Step 4 uses `lem-pd-section-oplax-total-comparison` for the actual chain map and its homotopy quotient, `lem-pd-section-kflat-tensor-comparison` for resolving localization, and clause (2) of `lem-weil-pbc-localization-universal-property` for the component formula of a lift. All three statements were opened. The two ordinary functors H1 and H2 invert resolving quasi-isomorphisms because Step 3 identifies them with restrictions of derived bifunctors. Thus the lifting hypotheses are checked, not assumed. Successive one-variable lifting uses the generic node's arbitrary target category, with the first target a functor category. The source and target factors are exactly a and c from Step 3; uniqueness identifies the computed map with the specified localized internal delta. I did not use the theorem that this delta equals the canonical ringed derived tensor map, which would be the conclusion of an ancestor and circular here.

Step 5 evaluates the meaning of localization for the actual unit arrow. The cited total-comparison statement explicitly covers the internal unit and its derived image. There is no target tensor factor to identify: its comparison is the identity on the regular derived unit. The formula is therefore q(u) eta, with the degree-zero model already justified. This is an elementary substitution, not a newly postulated unit compatibility.

Step 6 writes the inverse-naturality equation explicitly. The cited K-flat comparison statement supplies the resolving localization and the cited generic localization statement preserves composition. Multiplication of V xi = xi' U by the inverses gives V inverse xi' = xi U inverse. This handles inverse quasi-isomorphisms in each variable and their composites. Naturality is on homotopy-category representatives, not on arbitrarily chosen resolutions.

For C4 I generated `citations.json` from excerpts and asserted every quote is a literal substring of the corresponding current statement. The selected excerpts concern the fact each step actually takes. For C1 all non-elementary ingredients above are existing citations; no tag is used as an uncited theorem and no proof body is mined for a stronger claim. I checked dependency reachability for the new proof dependencies to exclude a path back through this item or its representative-square/derived-tensor-normalization ancestors.

Small-case checks: for the identity morphism the normalized comparison formula reduces to q(b) with the appropriate identity resolution factors; for a zero complex all tensor terms and their squares are zero; for the regular complex in degree zero the unary formula has source Lq(R[0]) and target q(R[0]) with no spurious tensor map. Unbounded pairs are handled by the existing direct-sum total closure statement, not a bounded-total argument. As an extra hypothesis test, arbitrary ringed pullback allows the nonflat map Z to Z/2: the argument uses K-flat representatives and never assumes that module pullback preserves all exact sequences. All six steps are under 2000 characters, so none hides a long inline lemma. The statement, its hypotheses, and its statement dependencies needed no correction.

The off-unit generic tools are explicitly declared in `split_report.tool_uses`: preservation under ringed pullback, ordinary internal/section operation comparison, total closure, and specified resolving-counit computation. They are categorical/model tools, not replacements of the Verdier-exchange unit route. The generic localization node is already a Mathlib leaf. No `reviewed` or top-level `tool_uses` approval was written by the worker.
