# Stage-1 worker report: def-sfb-constructible-module

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-constructible-module.json`: definition split using nine existing definition nodes; no exact Mathlib match. The inherited coefficient setup is spelled out, and the predicate itself is unchanged.
- `citations.json`: `[]`, since this is a definition with no proof steps.
- `report.md`: this report. `searches.jsonl` was written by the required search command.

New nodes: 0. Mathlib leaves: 0. No Lean, compiler, Lake or build commands were used.

## Attachments

None. The declaration `AlgebraicGeometry.ProEtale.IsConstructible` at `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/SixFunctors/ProEtale/ConstructibleSheaf.lean:71` concerns ordinary sheaves of modules over a discrete commutative ring, with finite locally constant restrictions. It does not state the item for ring objects in general monoidal sheaf categories. For example, the constant rank-one integer module on a geometric point is finitely presented but its stalk is infinite; this distinguishes the two finiteness conditions even before considering general coefficients. The exact item tag and `IsLocallyFinitelyPresented` produced no matching declaration in that checkout.

The upstream master reference `/home/ubuntu/weil-newtargets-master/WeilConjectures/ConstructibleSheaf/ProEtaleModule/Def.lean:87` has the intended ring-object predicate, with the same coefficient-category hypotheses, locally finitely presented restrictions, and `mapMod` transport. This read-only upstream reference is not submitted as a finished attachment.

## WANTED

None: all sources needed for this definition split are present locally.

## Findings and corrections

The original opening referred to another definition's setup without listing its coefficient objects. I expanded precisely that setup: closed symmetric monoidal Grothendieck abelian category with additive tensor, scheme, ring object in its pro-étale sheaves, and module object. The additional dependencies name notions already used by the original formula. There is no new commutativity, flatness, Noetherian, qcqs or torsion hypothesis.

The blueprint reference `sk-def-sfb-finite-pushforward-pullback` used by the locally-finitely-presented source is not a node in this snapshot. Its actual existing constituent nodes `def-sfb-finite-upper-star` and `def-sfb-finite-upper-star-monoidal` state the pullback and its monoidal structure, so I cite those directly. No other worker's file was edited.

The current chapter and unit source files were read at `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/_section.md` and `.../sk-def-sfb-constructible/_section.md`, together with the latter's `.proof.md`. Their corresponding chapter/unit JSON records are absent in this repository, and the imported item has no chapter/unit fields. I preserve the maintainer's metadata and do not manufacture unit records. The item is not the unit's key node, so no realization fields are delivered.

The surrounding unit's condensed-coefficient definition uses finite constant local models and constructible locally closed strata (locally on affine opens for arbitrary schemes). The present node defines the general ring-object, local-finite-presentation predicate instead. The source `det-def-sfb-constructible-local-model` explicitly distinguishes local finite presentation from finite constant local models. These definitions must not be identified without additional input; this split does not assert such an identification. The node's own source and upstream master ring-object definition agree on the local-finite-presentation criterion.

## Not duplicates

No new nodes were created. Whole-blueprint searches for “locally finitely presented” and “constructible modules”, and DAG searches for the same notions, were read. `pur713-def-module-constructible` is restricted to its specified coefficient rings and fixed abelian inverse-image convention. `sk-def-sfb-constructible` and `det-def-sfb-constructible-local-model` use the stronger finite-constant-model condition. Neither states this general definition in another form, so `same_as` is empty. The item's imported `blueprint.is` and null `blueprint.from` remain appropriate.

## Unfinished work

None for this one-level definition split. Its existing prerequisite nodes remain separate work items.

## Review by Q47

I read the full item source `def-sfb-constructible-module.md`, its inherited setup in `def-sfb-locally-finitely-presented.md`, and the unit's statement and proof in the current main-20261015 snapshot. The expansion preserves exactly the existential finite stratification and local finite presentation on each immersed stratum. I read the statements of all nine cited nodes, rather than borrowing constructions from their proofs: `sk-def-sfb-sheaf-tensor` supplies the sheaf tensor structure; `def-weil-pbc-proetale-site` supplies the site; `sk-def-sfb-ring-object` and `sk-def-sfb-module-objects` supply the ring and module notions. `def-sfb-finite-upper-star` defines the sheaf inverse image. Its setup in `def-sfb-finite-lower-star` permits an arbitrary scheme morphism, so it applies to each immersion without assuming that an immersion is pro-étale. `def-sfb-finite-upper-star-monoidal` supplies precisely the monoidal structure required by clause 1 of `sk-def-sfb-transport`, whose statement constructs a module over the image ring. The hypotheses in `lem-sfb-finite-upper-star-unit`, on which the monoidal-definition setup rests, are satisfied by the coefficient category here. This yields a module over the actual ring object $g_a^*\mathcal R$; no extension to a different stratum coefficient ring is being performed. Finally, `def-constructible-stratification` gives the finite partition with immersed realizations, and `def-sfb-locally-finitely-presented` applies to that pulled-back ring and module on $X_a$.

There are no proof steps to quote: the split is the dependency decomposition prescribed for a definition, and no theorem has been hidden inside the definition. In particular, it does not need a newly created statement restating one of its own clauses. I checked the empty scheme (the empty stratification makes the condition vacuous), a one-stratum scheme (the criterion is local finite presentation), and zero and regular modules (finite presentations allow rank zero and impose no nonzero-stalk condition). No global constructibility condition on locally closed subsets was silently added to the existing stratification definition.

For the Mathlib decision I read all seven actual search outputs, including the second semantic phrasing and second name/source patterns. I opened `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:236` and `:267`: its finite-presentation predicates concern ordinary sheaves of modules and contain no finite stratification or arbitrary monoidal module-object definition. I also read `Mathlib/Topology/Constructible.lean:178`, which defines constructible subsets, not the module predicate. Thus these are useful related notions, not exact or one-line-specialization matches for this item. Every recorded query is copied from the search command's log, with the actual successful service status. The checks against delivery-errors B–E found no new-node self-containment issue, unsupported proof citation, relabelled lemma, cycle introduced by a new lemma, or added mathematical hypothesis. All changes are confined to this sandbox.

## Earlier second reading (a previous round; superseded)

- Item statement: compared hypothesis by hypothesis with main-20261015 `def-sfb-constructible-module.md` and the inherited setup in `def-sfb-locally-finitely-presented.md`; PASS. The expanded setup and explicit word “finite” preserve exactly the source's definition and cited stratification convention.
- Proof steps: none, checked against stages/1-dag.md §3(2); PASS. This is a predicate definition, with its notions exposed as statement dependencies, not a theorem whose proof has been moved elsewhere. Empty `proof`, `proof_deps` and `citations.json` are appropriate.
- New nodes: none; PASS. There are no new statements to remove, search, or turn into Mathlib leaves.
- `sk-def-sfb-sheaf-tensor`: read the node's statement; PASS. The specified coefficient category satisfies its hypotheses, and its tensor and unit are those used for the ring and module objects.
- `def-weil-pbc-proetale-site`: read the node's site and covering definitions; PASS. No assumption that the immersed strata themselves are pro-étale over the base is introduced.
- `sk-def-sfb-ring-object`: read the statement; PASS. A ring object means a monoid object for the specified tensor; commutativity is not assumed.
- `sk-def-sfb-module-objects`: read clauses 1–2; PASS. They define left module objects and their category for a general monoidal category, not only the condensed specialization of clause 3.
- `def-sfb-finite-upper-star`: read its statement and the setup in `def-sfb-finite-lower-star`; PASS. The inverse image exists for arbitrary scheme morphisms, including the stratum immersions, and uses the same coefficient category on source and target.
- `def-sfb-finite-upper-star-monoidal`: read its statement and the hypotheses of `lem-sfb-finite-upper-star-unit`; PASS. They give precisely the strong monoidal structure on this inverse image under the coefficient hypotheses in force.
- `sk-def-sfb-transport`: read clause 1; PASS. Applying its displayed action formula to the inverse image gives a module over the actual image ring, with no unmentioned scalar-extension comparison.
- `def-constructible-stratification`: read the node, the current blueprint definition, and Stacks `topology.tex`, Tag 09XZ, label `definition-paritition`; PASS. The convention here is a finite partition into locally closed subsets with specified immersed realizations. Tag 09XZ defines the partition; finiteness is the blueprint's addition. Stacks' separate ordered notion at `definition-stratification` is not used. No constructibility or reducedness requirement on the immersed strata is added.
- `def-sfb-locally-finitely-presented`: read the node and its current blueprint source, and read `def-sfb-finitely-presented-module.md`; PASS. It is local finite presentation over the pulled-back ring, via finite-rank free module presentations, not a finite-stalk or finite-constant-model condition.
- Edge cases: PASS. For the empty scheme the zero-stratum partition makes the predicate vacuous. For the chosen identity one-stratum partition, its condition is exactly local finite presentation. Zero and regular modules have presentations $R^0\to R^0\to0$ and $R^0\to R^1\to R$, respectively. Over a geometric point with constant coefficient ring $\mathbf Z$, its regular module has such a presentation although its stalk is infinite; over a field the zero and rank-one constant modules also pass. Finite ranks zero and one are permitted.
- Existing Lean: independently opened slopmaster2 `SixFunctors/ProEtale/ConstructibleSheaf.lean:55–76` and upstream master `ConstructibleSheaf/ProEtaleModule/Def.lean:54–90`; PASS. The first uses finite locally constant stalks over a discrete commutative ring and does not state this predicate. The second has the intended general coefficient setup and formula but remains reference material, not a completed proof attachment.
- Duplicate check: read the entire current constructibility unit, its proof, `pur713-def-module-constructible`, and `det-def-sfb-constructible-local-model`, after whole-blueprint and DAG keyword searches; PASS. The former has restricted coefficient objects; the latter and the unit's finite constant model convention are different notions. No exact duplicate was identified.
- Independent Mathlib searches: ran `leanfinder` with the finite partition/free presentation phrasing, `grep` for `Stratification|IsConstructible`, and `loogle` for `"mapMod"`; PASS, no exact match. Read `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:236–278`: these local presentation predicates for ordinary sheaves have neither the required stratification nor the general module-object setting. The Loogle results concern manifold maps and derivations and supply no matching declaration. All three real outputs are preserved in `searches.jsonl` and recorded without changing the original search entries.

Changes: added this independent second reading and three independently phrased Mathlib search records. No mathematical statement or dependency needed repair; no new node, leaf, proof step or attachment was added. The first worker's review and findings are retained.


## Second reading by Q47

- Item statement: independently compared main-20261015 `def-sfb-constructible-module.md` (order 1640) and its inherited setup in `def-sfb-locally-finitely-presented.md` (order 1639), clause by clause; PASS. The coefficient category, arbitrary ring object, finite stratification and local-presentation predicate agree exactly.
- Proof steps: none; checked stages/1-dag.md §3(2) and the surrounding unit proof; PASS. This definition only decomposes its notions. Empty `proof`, `proof_deps` and `citations.json` introduce no hidden theorem or unsupported citation.
- New nodes: none; PASS. The sandbox has just the existing item, so B1–B7, removal of elementary/relabelled lemmas and new-node Mathlib-leaf decisions have no instances.
- `sk-def-sfb-sheaf-tensor`: read its complete statement and checked the coefficient assumptions; PASS. Its tensor is sheafified objectwise tensor with the sheafified constant unit.
- `def-weil-pbc-proetale-site`: read its objects, morphisms, coverings and universe convention; PASS. The item uses this site, without requiring stratum immersions to be its objects.
- `sk-def-sfb-ring-object`: read its general monoid-object definition; PASS. No commutativity of the coefficient ring is added.
- `sk-def-sfb-module-objects`: read clauses 1–2, including the action and regular module; PASS. They apply in the general monoidal sheaf category; clause 3's condensed specialization is not imposed.
- `def-sfb-finite-upper-star`: read its statement and `def-sfb-finite-lower-star`'s setup; PASS. The latter explicitly allows arbitrary scheme morphisms, so every stratum immersion is allowed.
- `def-sfb-finite-upper-star-monoidal`: read its statement and `lem-sfb-finite-upper-star-unit`'s hypotheses; PASS. Closed symmetric monoidal Grothendieck abelian coefficients give the monoidal pullback used here.
- `sk-def-sfb-transport`: read clause 1 and its precise constituent `def-sfb-modobj-transport`; PASS. The action is the lax structure map followed by the image of the original action, over the actual image ring; no identification with another coefficient ring is used.
- `def-constructible-stratification`: read its statement, current `blueprint_update`, and Stacks `topology.tex`, label `definition-paritition` (Tag 09XZ); PASS. This is a finite locally closed partition with immersed realizations. The separate ordered Stacks notion at `definition-stratification` is not being substituted.
- `def-sfb-locally-finitely-presented`: read its complete statement and both presentation source definitions; PASS. Finite free ranks may be zero; the presentation is over the pulled-back ring. The cover is pro-étale and the coefficient category is unchanged.
- Edge cases: checked empty scheme/zero strata, the identity one-stratum witness, zero modules and the regular module, and constant modules over a field; PASS. Presentations are respectively $R^0\to R^0\to0$ and $R^0\to R^1\to R$. A constant rank-one integer module on a geometric point passes the local-presentation condition although its stalk is infinite, so the slopmaster2 finite-stalk predicate is not an attachment.
- Existing definitions and Lean: independently searched the whole blueprint and DAG and opened `pur713-def-module-constructible`, `det-def-sfb-constructible-local-model`, the surrounding unit statement/proof, slopmaster2 `ConstructibleSheaf.lean:55–76`, and upstream master `ProEtaleModule/Def.lean:54–90` and `ConstructibleSheaf/Defs.lean:196–208`; PASS. The first DAG candidate restricts coefficients and the local-model candidate states a different condition. Upstream master has the intended general predicate and its stratification has no extra constructible-subset field; it remains read-only reference material.
- Independent Mathlib searches: ran a new finite-partition/local-presentation LeanFinder phrasing (eight results), Loogle `"IsFinitelyPresented", "Sheaf"` (no hits), and a scoped source grep (no hits), then read `Quasicoherent.lean:197–278`; PASS, no exact predicate. The candidates define finite presentation for ordinary sheaves of modules, with neither finite stratification nor arbitrary monoidal coefficients. One preliminary grep mistakenly scoped to the literal directory `--sub`; its zero-hit receipt is retained but is not evidence and is not recorded in `mathlib_searches`. The corrected scoped grep was actually run.

Changes: appended this independent second reading and three fresh, accurately recorded Mathlib searches. No mathematical statement, dependency, citation, node count or leaf count needed repair. The original worker sections, including `## Review by Q47`, are retained.
