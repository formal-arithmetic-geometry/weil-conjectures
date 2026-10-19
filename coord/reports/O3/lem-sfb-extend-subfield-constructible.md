# Stage-1 report: lem-sfb-extend-subfield-constructible

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-extend-subfield-constructible.json`: statement; split in five steps, unchanged statement; no exact Mathlib match after the six recorded searches (LeanFinder twice, Loogle, LeanSearch, grep twice).
- `citations.json`: 18 entries, one for every step/node citation, copied literally from the corresponding statements.
- `report.md`: this report. `prepare.py` is a sandbox-only preparation script; `searches.jsonl` is the search command's log. Neither is a DAG node.

New nodes: 0. New Mathlib leaves: 0. No unit or chapter file changed, since this is not the unit's key node.

## Attachments

None. I searched `WeilConjectures/` in `/home/ubuntu/weil-src-slopmaster2` for the blueprint id, expected declaration, scalar-extension names, and constructibility. There is no declaration for this item there. The upstream master declaration with the expected name `AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj`, `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean:165–171`, has a `sorry`. Its finite-field extension and cohomological bounds have the same form and it has no Noetherian hypothesis, but its constructibility predicate differs from the current blueprint; see below. It is reference material only, not an attachment.

## WANTED

None. The proof follows the current blueprint and is marked agent-written. No Stacks theorem, SGA source, or unavailable document is used as a black box.

## What was wrong and what changed

The imported single paragraph omitted the homology-preservation theorem, the exact-functor derived comparison, right exactness, and the comparison identifying tensoring after restriction to a stratum with restriction after tensoring. These now appear as explicit existing-node citations. The homology theorem is applied with its actual universal hypothesis: flatness holds for every scheme, by the statement of `lem-sfb-subfield-flat`.

The upstream definitions were also read in `ConstructibleSheaf/ProEtaleModule/Def.lean:65–95` and `DerivedCategory.lean:66–70`. Upstream `IsConstructible` uses generic local finite presentation on a global finite stratification. The current blueprint instead uses finite constant local models and imposes the condition affine-locally on arbitrary schemes. I do not identify these two predicates or certify a comparison theorem. This split proves the current DAG item with its current definitions; the upstream sorried declaration remains a separate reference.

The imported argument only showed preservation of local finite presentation, then concluded constructibility. The current definition requires finite constant local models. Its local-model detail node explicitly warns that arbitrary local finite presentation has no converse. I repaired the inference by retaining a scalar matrix over E throughout and showing that its extension is the same matrix with entries mapped into F. This repairs a gap in the proof, without changing the statement, the definition, the coefficient category, or the unit route.

I did not use the apparently more general `lem-weil-pbc-bounded-constructible-exact-scalar-extension`: its statement defines constructibility through generic local finite presentations, so it cannot supply the finite constant local models required here. The rationalization node `lem-sfb-extend-scalars-bounded-constructible` treats the different map O_E to E; the qlbar sibling treats E to qlbar. Neither states this item's map, and neither is needed. The DAG and whole-blueprint searches returned the existing local-model equivalence, underived Pull comparison, homology theorem and exact-derived comparison, all reused without duplication. No new node merely restates a clause of this item.

The only off-unit statement tools declared in `split_report.tool_uses` are the flatness input required by the original proof and the generic homology comparison. The remaining extra dependencies are definitions that explicitly state their comparison or local-model equivalence. I did not write maintainer-owned `tool_uses`.

## Unfinished work

None in this one-level split. Existing dependencies remain their owners' work. The statement has not been disputed or weakened. No Lean file was written or compiled; no Lake/build tool was run. The live source, launcher, shared repository and upstream reference checkouts were not edited. The required delivery dry run operates in the delivery tool's own temporary worktree.

## Review by N3

I read `coord/brief-stage1.md`, the stage-1 document, the three-level contract in SETUP, GOAL, the sync policy, the worker role, and delivery-errors B–E in full. I read this item's current chapter and two-colimit unit, its main-20261015 statement and complete proof, and the upstream master declaration and module docstring. The unit's cocone paragraph explicitly requests this coefficient-extension preservation, so the flatness/termwise/tensor-presentation proof remains on its route. This is a subsidiary node and does not own the unit's realization record.

For step 1 I opened the full statements of `def-sfb-subfield-coefficient-map`, `lem-sfb-subfield-flat`, `sk-def-sfb-change-of-scalars`, `def-sfb-left-derived-exact`, `lem-sfb-extend-scalars-preserves-homology`, and `def-sfb-derived-extend-subfield`. The coefficient map is induced by the inclusion of condensed fields; the flatness statement really quantifies over every scheme. Change of scalars explicitly provides the coequalizer and finite-colimit preservation. Additivity is written on tensor generators. The exact-derived node explicitly states LF is isomorphic to the termwise functor; its closed slopmaster2 declaration at `CategoryTheory/DerivedCategory/LeftDerivedFunctor/MapDerivedCategory.lean:77–92` was also read as supporting reference. The homology node explicitly states preservation of homology and its uniform flatness hypothesis is satisfied. Thus the cohomology formula concerns this same extension of scalars, not restriction of scalars or discrete constant coefficients. An arbitrary complex representative suffices; a bounded representative is not assumed.

For step 2 I read the full bounded-constructible statement and the change-of-scalars statement. Boundedness is cohomological; the zero object is preserved as an initial object. Hence the same integers bound the new cohomology. This is the explicit elementary inference from step 1, not an extra boundedness lemma.

For step 3 I read the full constructibility definition, local-model detail statement, underived Pull definition and subfield-coefficient-map statement, and their current blueprint texts. Constructibility is affine-local on general schemes; affine opens admit the finite stratifications specified by this definition. The local-model equivalence gives scalar matrices, not arbitrary coefficient-sheaf matrices. The Pull node explicitly asserts a natural isomorphism of the two underived functors for any scheme morphism; I use exactly that displayed isomorphism for affine opens, stratum inclusions and pro-étale covering objects. No immersion factorization, pullback exactness, stalk argument, or globally finite stratification is silently assumed.

For step 4 I checked the same statements against the formulas. Right exactness supplies a cokernel presentation after extension. The free-module identification is proved by two explicit inverse balanced maps; it is not inferred from sectionwise tensor being a sheaf. The formulas factor through the defining internal relative-tensor coequalizer. Each constant scalar entry a maps to that same scalar in F under the inclusion of condensed rings, so the resulting cokernel satisfies clause (2) of the cited local-model equivalence, which actually implies clause (1). The same covers and same constructible strata still witness the definition. There is no need for F to be algebraically closed or for X to be Noetherian.

For step 5 I checked that the bounded definition gives constructibility of every H^q(K), and that composing the resulting local isomorphisms with the step-1 cohomology isomorphism gives local models for H^q(TK). The bound was already proved separately in step 2. Thus every clause of the item's conclusion is supplied, with no appeal to the proof of a cited node rather than its statement.

I tested E=F (identity scalar change), K=0, a complex concentrated in one degree, X empty, zero ranks in a presentation, and non-quasi-compact/non-Noetherian X. The formulas and proof apply in each case: zero ranks give zero free modules, arbitrary X is handled separately on each affine open, and no finiteness of the total number of opens is used. A field extension may change a presentation's rank, but no rank equality or injectivity of the presentation map is claimed.

Against B–E: there are no new nodes requiring self-contained statements, extra definition nodes, Stacks-tag duplicate checks or Mathlib leaf certification. All six searches were really run via msearch.py and are recorded verbatim from its log, with a second natural-language phrasing. I read the nearest Mathlib candidates: ordinary-module scalar extension/flatness (`ModuleCat/Descent.lean:34–46`), sheaf local finite presentation (`ModuleCat/Sheaf/Quasicoherent.lean:265–269`), and the locally constant condensed-module functor (`Condensed/Discrete/Module.lean:35–59`). None states this item or specializes to it in one line. Every cited node exists, every use appears in proof_deps, every quote is a literal statement substring, and no source proof is substituted for a node statement. Non-elementary comparisons have explicit nodes; elementary tensor/free and zero arguments are written out. No new lemma relocates the item's content. The proof keeps all its original hypotheses and the corrected constructibility predicate.

## Validation

Source-level overlay checks passed: all 10 proof dependencies exist and are unmerged, their union equals the step uses, no dependency path returns to the item, and all 18 citation quotes are exact statement substrings with complete step coverage. The final required validation is `python3 /home/ubuntu/weil-launcher-nt/deliver.py N3 lem-sfb-extend-subfield-constructible --no-push`; its accepted sandbox is for the second reader to inspect and deliver. No push is authorized for this worker.


## Second reading by N3

I independently opened the item, all ten cited node statements, and their main-20261015 blueprint source files. The item's statement agrees verbatim with `lem-sfb-extend-subfield-constructible.md`: the prime, arbitrary scheme, finite inclusions inside the fixed algebraic closure, boundedness, and constructible cohomology are unchanged. The source is the blueprint, with no Stacks tag asserted or used. I also checked the chapter route and the two-colimit unit's cocone-preservation paragraph. The upstream master declaration at `TwoColimit.lean:165–171` has `sorry`; the named declaration and scalar-extension constructibility statement are absent from the read-only slopmaster2 source, so neither supplies a finished attachment.

- Step 1: checked against `def-sfb-subfield-coefficient-map`, `lem-sfb-subfield-flat`, `sk-def-sfb-change-of-scalars` (2), `def-sfb-left-derived-exact`, `lem-sfb-extend-scalars-preserves-homology`, and `def-sfb-derived-extend-subfield`; PASS. The finite-limit hypothesis holds on every scheme, as the homology lemma requires; the coequalizer supplies the additive formula and finite-colimit preservation; the exact-derived comparison applies to this same functor, with no bounded representative assumed.
- Step 2: checked against `sk-def-sfb-bounded-constructible` and finite-colimit preservation in `sk-def-sfb-change-of-scalars`; PASS. Preservation of the initial/zero object and the formula in step 1 give precisely the same cohomological bounds. This is elementary.
- Step 3: checked against `sk-def-sfb-constructible` (1)–(2), both directions of `det-def-sfb-constructible-local-model`, and `def-sfb-pull-iso` for the coefficient inclusion; REPAIRED, then PASS. The argument now chooses the global finite stratification when X is qcqs and an affine covering otherwise. It explicitly writes the comparisons for the open, stratum, and cover maps. The scalar-matrix presentation is supplied by the cited statement, not its proof.
- Step 4: checked against right exactness in `sk-def-sfb-change-of-scalars`, the coefficient-map statement, and the local-model equivalence; REPAIRED, then PASS. The two balanced maps are inverse on the defining tensor coequalizer, including rank zero, and each scalar matrix entry maps into F. The concluding witnesses now distinguish the global qcqs case from the affine-local case, so no gluing or global finiteness theorem is tacitly used.
- Step 5: checked against `sk-def-sfb-bounded-constructible` and `sk-def-sfb-constructible`; PASS. For each degree, compose the model isomorphisms from steps 3–4 with step 1; step 2 supplies boundedness. This is elementary.
- New nodes: none; PASS. There is no elementary, duplicate, Mathlib, or restatement node to remove, and B1–B7 impose no new-node repairs. The ten existing citations remain sufficient.

Small cases checked independently: E=F, X the spectrum of a field, X empty (empty stratification), K=0, one nonzero cohomological degree, and presentation ranks 0 and 1. Both tensor composites reduce to the identity, zero is preserved, and the given strata and covers still work. For non-quasi-compact or non-Noetherian schemes the proof uses only the affine-local condition, with no uniform finite collection of strata across the covering. No statement dispute was found.

Changes made:

- In steps 3–4, preserve the global qcqs stratification explicitly; the original affine-only argument did not explicitly supply the global witness required by the cited definition.
- In step 3, replace the abbreviated restriction-comparison sentence with its three applications, so the stratum and cover restrictions are stated rather than left to “the same comparison”.
- Run three independent searches via `msearch.py`, using locally constant finite-dimensional vector spaces and Mathlib's `IsConstructible` vocabulary; append their actual results and verdicts to the item and retain the unedited search log. LeanFinder returns condensed locally constant-module functors; Loogle and grep return constructible subsets. I read the relevant declarations in `Mathlib/Condensed/Discrete/Module.lean` and `Mathlib/Topology/Constructible.lean`; none states this item. No Mathlib leaf is warranted.

The 18 citation quotes remain verbatim parts of the unchanged cited statements and still cover every step citation. The first worker's review and all earlier report sections remain in place. No Lean file, live checkout, launcher, unit, or chapter record was edited; no compiler was run.
