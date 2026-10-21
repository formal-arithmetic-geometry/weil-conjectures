# Stage-1 delivery: def-sfb-module-linear-open-lower-shriek

Group Q06, 2026-10-21. This is the explicitly requested re-split of the live item, not an attachment and not a declaration that its previous review was stale.

## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-module-linear-open-lower-shriek.json`: definition with its statement unchanged; nine assembly steps replacing the broad exact-lift invocation by its finite-limit reflection and cancellation ingredients and the already lifted adjunction. All previous import, blueprint, Lean, source and search metadata retained.
- `dag/nodes/sec-six-functors-basics/lem-sfb-conservative-left-exact-reflects-finite-limits.json`: statement; Mathlib leaf, exactly `CategoryTheory.Limits.reflectsFiniteLimits_of_reflectsIsomorphisms`, `Mathlib/CategoryTheory/Limits/Preserves/Finite.lean:175–178`.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-limit-preservation-cancellation.json`: statement; Mathlib leaf, exactly `CategoryTheory.Limits.preservesFiniteLimits_of_reflects_of_preserves`, the same file, lines 163–165.
- `citations.json`: one verbatim statement quotation for each node cited in each numbered step.
- `searches.jsonl`: actual msearch log; `prepare.py`: sandbox-only JSON preparation script; `report.md`: this report.

There are two NEW nodes and both are Mathlib leaves. They carry statement-only bodies with empty proof and proof_deps. The human's request for new statement-only ingredients is satisfied by exact Mathlib matches rather than postponing already available proofs as unsplit nodes. Neither new statement restates an extension-by-zero clause: both concern arbitrary categories and arbitrary functors, without modules, sheaves, monoidal structures, or an adjunction. The old exact-lift node is no longer a proof dependency. Construction, coherence and the lifted adjunction already have dedicated existing nodes, and are reused rather than duplicated.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id and the linear-extension-by-zero names and read the full relevant part of `WeilConjectures/SixFunctors/ProEtale/ModuleObject/LowerShriek/Defs.lean`. The definition at line 90, forgetful equality at 99, adjunction at 105 and instances at 109, 123 and 130 cover the intended objects and clauses, but they use the projection-formula instance at 81, whose body is `sorry`. They do not qualify as a finished attachment. The new categorical statements are Mathlib leaves, not project attachments; project searches for their names found applications of the general Mathlib results, not project declarations stating these two generic results.

## WANTED

None. The blueprint and all Mathlib declarations used here are locally available. No SGA source is used.

## What changed and what was wrong

The current repository had already replaced the 3442-character proof named in the route note by a seven-step proof using existing dedicated nodes. I started from that CURRENT repository copy, retained its construction and adjunction arguments and all logged searches, and further decomposed its final exactness argument. In particular I did not deliver another no-new-node reuse-only change. There is no statement dispute or change of coefficients: the input is Mod over j^* Lambda_X, not over Lambda_U, and there is no scalar-change step in this node.

The inherited exact-lift theorem is a valid tool, but hiding its reflection/cancellation ingredients behind that one invocation did not make new atomic nodes visible. The delivery makes those two categorical ingredients separately searchable leaves. Its right-exactness argument now comes directly from the adjunction already obtained in step 4; its left-exactness argument uses the source forgetful functor's preservation, the target forgetful functor's conservativity and preservation, and the two new leaves. This retains the unit's projection-formula route. The parent statement, statement dependencies and blueprint import metadata are unchanged.

## Not duplicates

lem-sfb-conservative-left-exact-reflects-finite-limits vs det-prop-sfb-module-pullback-exact-lifted: the new result is a reflection theorem for arbitrary categories and functors, assuming only source finite limits, preservation and reflection of isomorphisms. The existing result assumes two abelian monoidal categories, right-exact tensors and an exact additive base functor, and concludes exactness of a module lift. It does not state the generic reflection result.

lem-sfb-finite-limit-preservation-cancellation vs det-prop-sfb-module-pullback-exact-lifted: the new result cancels a functor reflecting finite limits from a composite in arbitrary categories, without assuming either category abelian, any module structures, additivity, exactness of a base functor or even existence of all finite limits. The existing result is a module-specific application, and its proof uses this Mathlib theorem, but its statement does not supply this general tool.

lem-sfb-conservative-left-exact-reflects-finite-limits vs lem-sfb-modobj-forget-left-exact: the existing node only states preservation for a module forgetful functor under abelian/right-exact tensor hypotheses. The new node states reflection for an arbitrary conservative preserving functor whose source has finite limits.

lem-sfb-finite-limit-preservation-cancellation vs lem-sfb-modobj-forget-left-exact: the existing node supplies one hypothesis of the application; it says nothing about cancellation of a composite of functors.

lem-sfb-conservative-left-exact-reflects-finite-limits vs lem-sfb-finite-limit-preservation-cancellation: the former constructs reflection from preservation, source existence and conservativity; the latter assumes reflection and cancels a second functor from a composite. Neither is a specialization of the other.

lem-sfb-conservative-left-exact-reflects-finite-limits vs def-galois-finite-limits-colimits: the existing node defines finite limits; it does not state reflection of limiting cones by a conservative preserving functor.

lem-sfb-finite-limit-preservation-cancellation vs def-galois-finite-limits-colimits: the existing node is the finite-diagram notion, not a cancellation theorem.

lem-sfb-conservative-left-exact-reflects-finite-limits vs lem-trf-coherent-conservative-reflection: the latter reflects coherence of objects along a coherent conservative geometric morphism between coherent topoi. It does not state reflection of finite limit cones in arbitrary categories.

Before creating the nodes I searched the whole DAG by reflection, creation, conservativity, finite-limit preservation and the exact four Basic/Finite Mathlib names. I read the candidate statements including the existing exact-lift theorem and module forgetful nodes. Whole-blueprint searches used `module.*limit`, `reflects limits`, `conservative`, `limit preservation`, `reflecting`, `finite limits`, and `linear extension by zero`. No blueprint node states either generic new theorem; thus both same_as lists are empty. The ancestor command identified the item itself; the new from.place fields point to its final exactness sentence, with no intermediate via nodes.

## Review by Q06

I read the current main-20261015 chapter and module-lower-shriek unit, then the item's statement and proof files. The source's first sentence constructs the action from the projection formula and lifts the adjunction. Its final sentence computes finite limits and colimits through underlying sheaves to deduce exactness. The revised proof implements those same operations. I also read the live Lean implementation of the linearization and its finite-limit instance in `WeilConjectures/CategoryTheory/ModuleObjects/ProjectionFormula.lean:280–319`: it uses exactly the reflection/cancellation pattern separated here.

For the two new nodes I read `Mathlib/CategoryTheory/Limits/Preserves/Finite.lean:150–183`, not only search snippets. At 175 the source has all three hypotheses recorded in the new reflection statement: ReflectsIsomorphisms, HasFiniteLimits of the SOURCE, and PreservesFiniteLimits. At 163 the cancellation theorem assumes preservation by the COMPOSITE and reflection by its SECOND factor, without an existence hypothesis. The statements expand reflection and preservation in terms of cones, so neither depends on an unexplained use of the word conservative. The finite-diagram notion is bound to def-galois-finite-limits-colimits; I read that statement and Stacks Categories Tag 002E, categories-definition-limit, for its cone meaning. The Mathlib file is the primary source of the two theorems, not an invented Stacks tag for them.

Step 1 uses the pulled-back coefficient node for the ring object B, finite-lower-shriek for P exact and P left adjoint to S, and finite-upper-star-monoidal for S strong monoidal. I opened these three statements. The monoidal node's inherited hypotheses hold with abelian groups and an open scheme immersion; it is the same pullback used by the extension-by-zero adjunction.

Step 2 uses open-projection-formula for invertibility of the canonical maps of this adjunction, and adjunction-projection-formula for their coherence. The latter's statement specifically says that those maps form the coherent projection formula; no coherence is inferred merely from having some isomorphisms. Step 3 uses modobj-linearization, whose statement explicitly gives the displayed action, module axioms, linearity on morphisms and commutation with forgetful functors. Step 4 uses linearization-transport-adjunction, whose statement identifies the right adjoint with mapMod(S), rather than only asserting an unidentified right adjoint. I opened all five cited statements and checked the orientation P(SL tensor M) to L tensor PM and the domain Mod_{SB}.

Step 5 uses the chosen small pro-etale site to satisfy the small-site hypothesis of site-sheaves-enough-injectives; only its abelianity conclusion is used. I opened the tensor-closed statement and its structure hypotheses: Ab and the small pro-etale sites are explicit examples, and tensoring with either ring object preserves all colimits, hence finite colimits. This verifies exactly the additive-tensor and tensor-right-exact assumptions needed in step 6, not just closedness by name.

Step 6 uses modobj-abelian for abelianity and modobj-forget-left-exact for finite-limit preservation by BOTH forgetful functors. I opened their statements: the second applies under the hypotheses of the first, and step 5 verifies those hypotheses on both sides. Abelianity supplies source finite limits for step 8. Step 7 uses the module-morphism equation from module-objects, writes the inverse-linearity calculation out, and is elementary. Faithfulness by itself would not imply conservativity; I corrected that potential gap by proving inverse linearity rather than citing faithful forgetfulness for reflection of isomorphisms.

Step 8 applies the first new leaf with C=Mod_B(D), D=D, V=U_B. Step 6 gives finite limits in that C and preservation by V, and step 7 gives reflection of isomorphisms. It then applies the cancellation leaf with F=P_B and V=U_B. Step 3 supplies U_B P_B=P U_SB; applying the two preserving functors successively to a limit cone proves preservation of this composite. This is an elementary composition observation, not an assumed exactness of the module lift. Both quoted leaf statements therefore have every hypothesis available before application.

Step 9 uses left-adjoint-preserves-colimits on the LIFTED adjunction from step 4, not on the original sheaf adjunction. Finite index categories are small and module categories are abelian, so finite colimits exist. The preserving-colimits-additive node has abelian source and target and finite-colimit preservation as its exact hypotheses; these come from step 6 and the first half of this step. The exact-functor definition then identifies finite-limit and finite-colimit preservation with exactness. Thus no uncited theorem about tensor-exactness or abelian sheaf stalks is hidden here.

I checked the two new statements on the empty indexing category (terminal objects), identity and equivalence functors, and categories without all finite limits. The reflection statement retains its necessary existence hypothesis; the cancellation statement makes only a preservation assertion about cones which exist, so needs no such hypothesis. For the item, j=id gives the identity linearization, U empty gives zero extension and its usual adjunction, and the zero coefficient ring gives zero module categories; the action and all hypotheses remain consistent. The module inverse calculation also applies to the zero module. There are no new hypotheses on the immersion or on Lambda, no added finiteness or flatness assumptions, and no scalar substitution.

Against B–E of delivery-errors: every new statement introduces all its categories and functors and has no proof sketch; mathematical notions needing explanation are cited or explicitly defined; every search is an actual recorded msearch query and every hit used was read; no new lemma is an elementary module calculation or a clause of the item. The elementary inverse calculation stays a step. The two new leaves have no dependencies on the item, and no cited existing node has been changed. Every cited statement was opened, and citations.json copies verbatim text from it. Each step is below 2000 characters (longest 449); there is no concealed long subproof. No source error, cycle-inducing backward dependency or unit-route change was introduced.

The off-unit generic tools already accepted on the item remain generic tools: coherence, linearization, lifted adjunction, abelianity of small-site sheaves, and closed sheaf tensor. The delivery requests no change to the maintainer's top-level tool_uses. The new leaves are Mathlib tools and the module forgetful/abelian nodes are existing declarations. I have written no Lean, run no compiler/Lake/build command, made no repository or launcher edit, and started no agents.

## Unfinished work

No mathematical split argument remains unfinished. Validation and delivery results are recorded by deliver.py; stage-2 and stage-3 work is outside this delivery.
