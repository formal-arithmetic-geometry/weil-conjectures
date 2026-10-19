# Worker report: def-real-boundary-decomposition-path

## Files written

- `dag/nodes/sec-purity-real-sheaves/def-real-boundary-decomposition-path.json`: existing definition; Mathlib leaf by specialization of `CategoryTheory.Iso` to the two fibre functors. Component clauses are `CategoryTheory.NatTrans`, `CategoryTheory.Iso.app`, `CategoryTheory.NatIso.ofComponents` and `FintypeCat.equivEquivIso`.
- `citations.json`: empty list, because the definition/Mathlib leaf has no proof steps.
- `report.md`: this report. No new nodes, no unit edits, no Lean changes.

## Attachments

None. I searched the slopmaster2 project under `WeilConjectures/` for the item's blueprint tag and for etale-path, fibre-path and fiber-path terminology. `AlgebraicGeometry.Scheme.FiniteEtale.galoisToFundamentalGroup` in `AlgebraicGeometry/FundamentalGroup/GaloisAction.lean:82` consumes a parameter `τ : fiber (pointOfAlgebra Ω y) ≅ fiber s`; it does not declare the definition of all etale paths. `BoundaryChart.path` constructs a particular path, also not the item. Thus neither is claimed as an attachment. The exact upstream master was searched read-only as reference material too.

## WANTED

None.

## Findings and corrections

The statement is unchanged, as are its two statement dependencies and the original searches. The inherited no-match searches sought etale-specific names; broader searches find the generic interface that gives this entire definition when specialized to the already supplied fibre functors. The geometric construction of those functors is not being claimed to exist in Mathlib. It remains the role of `def-galois-fibre-functor`, whose statement explicitly includes its finite-etale interpretation.

The current source read is `literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-d-real-boundary/d-real-boundary.md`, the paragraph choosing a geometric point over the local field and a path to the base point. I also read the chapter and unit records and the statements of `def-weil-geometric-point`, `def-galois-fibre-functor` and `lem-real-lisse-path-fibres`. The last contains the same path convention together with substantially stronger hypotheses and lisse-transport assertions; it is not a dependency needed to define a path. The whole blueprint was searched with `blueprint_refs.py` for `path`, `etale path` and `natural isomorphism`, and the whole DAG with matching words and declaration names. No new node is needed, and `blueprint.same_as` remains empty because no other blueprint node has the same entire statement.

## Mathlib searches and source verification

All additional Mathlib searches used the mandated `msearch.py NU def-real-boundary-decomposition-path` command and their queries/results are preserved in `searches.jsonl` and copied into the item's `mathlib_searches`. LeanFinder with “A natural isomorphism between two functors consists of isomorphisms at every object satisfying naturality”, LeanSearch with “A natural isomorphism of finite set valued functors is a family of bijections commuting with every morphism”, and Loogle with `CategoryTheory.NatIso.ofComponents` all returned `CategoryTheory.NatIso.ofComponents`. The two logged source greps in `CategoryTheory` located the component, naturality, isomorphism and finite-set equivalence declarations.

I read the pinned Mathlib sources at `CategoryTheory/Iso.lean:53`, `CategoryTheory/NatTrans.lean:53`, `CategoryTheory/NatIso.lean:53` and `:181`, and `CategoryTheory/FintypeCat.lean:130`. `Iso` has forward and inverse morphisms and both inverse equations. `NatTrans` has one component for every object and naturality for every arrow. `Iso.app` extracts a component isomorphism. `FintypeCat.equivEquivIso` turns it into a bijection, and `NatIso.ofComponents` conversely constructs the natural isomorphism, requiring only the forward naturality equation. These are exactly the clauses of the item with `F = F_ybar` and `G = F_zbar`; no comparison theorem is needed.

## Unfinished work

None for this stage-1 item. No existence, conjugation or transport theorem has been added to its meaning.

## Not duplicates

No new nodes. Existing related nodes are cited above only for the audit, not used as proof dependencies.

## Review by NU

I compared the unchanged definition with the current boundary-source path clause and checked its orientation: a path from ybar to zbar has type `F_ybar ≅ F_zbar`, so its forward component maps the ybar fibre into the zbar fibre. The geometric-point dependency states a morphism from an algebraically closed field's spectrum; the fibre-functor dependency explicitly supplies the finite-etale fibre sets and their maps. Neither dependency is being used for a theorem about path existence. The source's later decomposition-group and Frobenius-invariance clauses are outside this item's definition and have not been moved into new nodes.

There are no proof steps and therefore no step citations to quote. The empty `proof`, `proof_deps` and `citations.json` accurately reflect a definition that is a Mathlib leaf. For its componentwise description I checked the actual generic declarations listed above, rather than relying on their names: evaluating the naturality field at a cover morphism f:P→Q gives `F_zbar(f) ∘ gamma_P = gamma_Q ∘ F_ybar(f)`; the inverse identities give bijectivity. Conversely the given family of bijections gives component isomorphisms through `FintypeCat.equivEquivIso`, and precisely this equation is the hypothesis of `NatIso.ofComponents`. No additional category, finiteness, Galois-category, algebraic-closure or connectedness hypothesis enters this specialization. The connectedness assumption in the item's context has been retained.

I tested the interpretation on an empty cover (the component is the unique empty-set bijection), the identity path when the two points coincide, and singleton fibres; none requires a nonempty cover fibre. If Y has no geometric points there is no input pair, and the definition makes no existence assertion. All declarations are universe-polymorphic and apply to the given cover category. The B–E checklist yields no new-node, missing-citation, hidden-lemma, cyclic, relabelling or missing-hypothesis issue. The substantive correction is the Mathlib verdict: the previous etale-specific searches missed the exact generic specialization. The statement, blueprint ancestry, created provenance and inherited searches have been retained. There are no non-elementary proof steps exceeding 2000 characters, or proof steps of any length.
