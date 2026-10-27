# Q13: lem-sfb-qlbar-bounded-tensor-colimit

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-qlbar-bounded-tensor-colimit.json`: statement, split into eight proof steps; no exact Mathlib match for the full assertion. Statement and original metadata preserved.
- `citations.json`: one verbatim statement extract per node used in each step.
- No new nodes; no Mathlib leaves created. Sandbox-only research artifacts: `hrs.txt`, `searches.jsonl`, `write_split.py`, and this report.

## Attachments

None. Searches for the exact blueprint tag and coefficient/bounded-tensor notions in the live `lean/WeilConjectures/` found no declaration proving the whole item. The source's `SixFunctors/ProEtale/ModuleObject/Colimit/Compatibility.lean` supplies coefficient flatness and the point-pullback colimit, but does not state the entire strict bounded-below tensor diagram and arbitrary-representative cohomology assertion. Those partial results do not justify ATTACH. No Lean was written and nothing was compiled.

## WANTED

None. All sources needed for this split were available locally.

## Findings and changes

The imported item had no proof. Its statement is correct with the specified finite-subextension-valued condensed closure, a coefficient universe containing the index, and ordinary unbounded module-sheaf derived categories. I did not change it. In particular I did not replace the closure coefficient by all continuous functions to the valued algebraic closure, impose constructibility, assume qcqs on the arbitrary scheme map, or require the arbitrary representative J to be K-flat.

The Hemo–Richarz–Scholbach source motivates the filtered coefficient colimit and exactness of filtered cohomology, but is not literally this normalized ordinary-derived-category theorem. I marked the expanded proof `by: agent`, and supplied its ingredients as existing cited DAG statements, rather than claiming the paper proves every clause verbatim.

I reused `lem-sfb-qlbar-tail-finite-free-algebra-presentation` for precisely the small tail, finite freeness, specified coefficient actions and module cocone; `lem-sfb-filtered-colimit-flat-module-sheaves` for flatness; `lem-weil-pbc-independent-sheaf-tensor-colimits` for termwise tensor colimits; and the general clause of `lem-sfb-rhom-colimit-cohomology-ladder` for cohomology. Existing generic statements from other units are declared in `split_report.tool_uses`, with their exact role; this follows the worker brief's express tool-use mechanism. They do not replace the open-image unit's integral-finiteness or rational-coefficient-continuity route. This item supplies the strict common-bound diagram used in the rational coefficient step. It is not the key node of its unit, so no unit realization file was changed.

## Unfinished work

No mathematical clause is left unfinished at this splitting level. The existing unsplit dependencies remain separate queue items; their proofs are not claimed here. Delivery validation results follow below.

## Review by Q13

I read `coord/delivery-errors.md` B–E in full, the chapter and unit records, the current main-20261015 ancestor's statement/proof and the open-image unit route. For the paper source I read Hemo–Richarz–Scholbach Lemma 5.3, its proof around equation (5.4), and the paragraph before Lemma 5.6. I also read the actual local Stacks statements and proofs: Modules on Sites Tag 03EP (`lemma-tensor-commute-colimits`), Tag 03EU (`lemma-colimits-flat`), Tag 03DB (`lemma-limits-colimits`), and Cohomology on Sites Tags 06YT/06YU (`lemma-derived-tor-quasi-isomorphism-other-side` / `definition-derived-tor`) and the K-flat localization construction preceding the definition. These give the generic infrastructure; no SGA source is used. No new nodes need additional source verification.

For step 1 I opened the entire statement of `lem-sfb-qlbar-tail-finite-free-algebra-presentation`, rather than taking information from its proof. It explicitly states the tail is small, nonempty and filtered, the finite freeness including F=E, and the very same q_F cocone in module sheaves. Its coefficient convention and module equivalence agree exactly with this item's. Thus this is a specialization, and a new tail or cocone lemma would duplicate it.

For step 2 I checked the statement of `lem-weil-pbc-independent-sheaf-tensor-colimits` and the actual sheafified sectionwise definition in `def-pur-sheaf-tensor-product`. The finite-free tensor calculation and coordinatewise exactness of a finite direct sum are written out. This is an elementary few-line calculation from the chosen finite basis and cited tensor-colimit fact; it is deliberately a step, not a new lemma. Step 3 cites the entire general flat-colimit theorem, whose hypotheses allow the small site and the very same coefficient universe. Step 1 provides its directed small index and colimit, and step 2 supplies flatness of every stage. No argument uses flatness of section modules.

For step 4 I opened `sk-prop-sfb-cartesian-coefficients`, `sk-def-sfb-coefficient-change`, and `def-weil-pbc-internal-abelian-sheaf-module-equivalence`. The first explicitly asserts exactness of module pullback, not just invertibility of a coefficient ring map. The second explicitly states the commuting pullback square for an arbitrary condensed ring morphism. Applying its equation separately to E→F, E→Omega, and F→Omega proves both the module-action identifications and the specified q_F leg equation. The equivalence preserves the underlying abelian sheaf and sections identically; the actions are identified by these same equations. The untwisted assertions hold for every scheme morphism, so no invertibility of ell or finiteness assumption on f was added.

For step 5 I opened `def-sbc-standard-tstructure-derived-category` and `def-kun-truncations`. They state both the vanishing criterion and the good lower truncation with the cokernel in degree a and retained cohomology. The proof explicitly checks the truncation quasi-isomorphism below, at and above a; merely using the stupid truncation would have been wrong.

For step 6 I checked every cited statement: `lem-pc-kflat-resolution` supplies a flat-term K-flat resolution of any unbounded complex; `lem-fd-ringed-flat-single-tensor-cohomology` says a flat module in degree zero is K-flat with flat terms; `lem-weil-pbc-site-derived-tensor-descent` gives the derived isomorphism natural in both flat-term K-flat variables; and `lem-sp-exact-functor-preserves-homology` gives the natural kernel/image/cohomology comparison for an exact functor. These give the actual derived-object isomorphism, rather than just per-degree agreement. Exact tensor turns the resolution map into a quasi-isomorphism. I use one resolution for the whole coefficient diagram, and wrote the commuting square on pure tensors, so q_F and every transition become the derived coefficient maps. There is no hidden requirement that K or J itself be K-flat, and no new derived-comparison node is needed because the existing statements already supply it. This step is 1338 characters, below the 2000-character long-step threshold.

For step 7 I rechecked that the tensor-colimit node accepts all small diagrams at this universe. Symmetry of the sheafified tensor is the ordinary flip of pure tensors. I wrote the differential/transition and differential/cocone equations explicitly, so the colimit is the claimed complex with its actual legs. Vanishing below a is termwise and independent of F. Step 8 uses only the expressly stated general cohomology-colimit isomorphism in `lem-sfb-rhom-colimit-cohomology-ladder`, without using its RHom continuity or triangle clauses. That statement is for every small filtered complex diagram, including unbounded ones. Its natural map is identified by the coprojections, and step 6 identifies those coprojections with the specified derived legs. Thus no bound on A has been smuggled in.

For B and C: no new unsplit node contains a hidden proof, no duplicate is created, the statement remains self-contained, all non-elementary facts are covered by the cited node statements, and every use has a verbatim entry in `citations.json`. The Mathlib searches were actually run through the required msearch command, and their hit output read. They found presheaf tensor-colimit instances, filtered-colimit infrastructure, and the general strict-lower-representative lemma `DerivedCategory.exists_iso_Q_obj_of_isGE` (Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean:175), all useful pieces but none an exact match for this item. I inspected that representative lemma and reused the existing standard-t-structure/truncation nodes instead of inventing a new Mathlib node. The original searches are retained, and the new logged searches appended with their exact query text; all services used were available.

For D: the proof carries the actual construction and compatibility argument. No new node is a renamed clause, and none moves the item into a new black box. I traversed statement/proof dependencies of the cited tools and found no path back to this item. For E I tested the rank-one identity F=E, the empty scheme, the zero complex, negative a and q, and complexes unbounded in either direction in the Y assertion. All steps still apply: zero sheaves and zero complexes cause no exceptions, filteredness is independent of the schemes, and exactness supplies every cohomological degree without convergence of any spectral sequence. The finite-free proof uses only finite direct sums; no exactness of arbitrary products is assumed. No statement dispute arose.

## Not duplicates

No new nodes. The existing tail-presentation, flat-colimit, tensor-colimit, good-truncation, and natural cohomology-colimit statements are reused directly.

## Validation

Server `review_split` passed with zero new nodes. The prescribed `deliver.py Q13 lem-sfb-qlbar-bounded-tensor-colimit --no-push` exited 0 and printed `OK (not pushed)` at dry-run commit 90a6cf50165, with server preflight passed. The only route note says this non-key item's unit has no realization recorded yet; the item does not own the unit key statement. All proof steps are below 2000 characters, and all 16 citations have been checked as literal substrings of the live cited statements. The report was updated with these results before the final delivery command, which repeats the preflight.
