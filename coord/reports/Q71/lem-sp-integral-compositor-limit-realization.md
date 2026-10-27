# Stage-1 report: lem-sp-integral-compositor-limit-realization

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-integral-compositor-limit-realization.json — statement node, now split in six proof steps; not a Mathlib leaf.
- citations.json — 16 verbatim statement excerpts, one for every step/node citation.
- searches.jsonl — actual Mathlib search-command log. The item's inherited search records are retained and the current searches appended.

There are **0 new nodes and 0 new Mathlib leaves**. The proof uses three existing Mathlib leaves for fully faithful restriction, composition of adjunctions and uniqueness of right adjoints. No Lean was written or compiled; no repository or launcher files were changed.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, integral compositors, adjoint compositors, integral adjunctions and normalized towers found no declaration proving this item. The normalized-tower derived-limit modules concern reconstruction, rather than both functor compositors with their specified adjunctions.

## WANTED

None. The source and the relevant pinned Mathlib source files are available locally.

## Problems in the imported node and source

The statement is retained verbatim. Its proof was empty. The latest blueprint's det-sp-composition-comparisons proof (3) gives only the instruction to apply the reduction/total-limit equivalence, and its proof (1) fixes the counit normalization. I expanded that instruction rather than asserting transport without checking the maps. The blueprint's displayed integral assertion names E = Q_ell, whereas this item already states the same conditional construction for any finite E. Every step is categorical once the stated equivalences and adjunction comparisons have been supplied, so no extra geometric claim is required for the general E statement.

No STATEMENT-DISPUTED correction is needed. In particular the inverse of the middle counit belongs in the right compositor, and the direct counit belongs in the left compositor. No finite-evaluation faithfulness is used.

## What remains unfinished

Nothing in this one-level split. The existing statement dependencies retain their own proof obligations. Delivery status is recorded below after the required server dry run.

## Not duplicates

No new nodes were created. I searched the whole DAG for equivalence/adjunction/compositor and right-adjoint uniqueness statements, inspected the relevant statements, and ran tools/blueprint_refs.py ancestor and search for compositors and integral composition. The ancestor is det-sp-composition-comparisons. That parent includes the Q_ell conclusion but also the finite/tower construction, and already depends on this item; it cannot be used to prove this item. The other blueprint hits concern composition factors and vector-bundle purity, not this precise reduction/limit realization statement. Thus blueprint.same_as stays empty.

The existing lem-pur-normalized-reconstruction-adjunction-calculus gives a useful general transport calculation for semilinear systems, but the proof here only needs the already cited equivalence and the existing categorical leaves. I did not introduce another transport node or reroute through that other unit. Likewise lem-sf-adic-exceptional-compositor-coefficients has broader coefficient-stage and compactification assertions; it is not needed here.

## Mathlib searches read

The msearch.py calls in searches.jsonl were read as returned:

- LeanFinder, “Conjugate composition isomorphisms of adjoint functors by equivalences with compatible units and counits”, finds conjugateIsoEquiv, conjugateEquiv_comp and the adjunction-composition mate theorem. These are general categorical tools, not the stated completed-integral derived-tower assertion.
- Loogle, CategoryTheory.Adjunction.comp, finds comp, comp_homEquiv, comp_counit_app and comp_unit_app.
- LeanSearch, “Composition of adjunctions has counit equal to the composite of the counits and right adjoints are uniquely isomorphic”, finds comp_counit_app and rightAdjointUniq compatibility lemmas.
- grep, “rightAdjointUniq|comp_counit|counit.*naturality” in CategoryTheory/Adjunction, locates the actual Mathlib declarations. I read Basic.lean:563–586, Unique.lean:101–140 and Restrict.lean:26–88. These agree with the existing three DAG leaf statements; there is no missing categorical node to add.
- A second LeanFinder phrasing, “Realize normalized adic tower adjoint composition isomorphisms on derived complete integral sheaves by reduction and total inverse limit”, returns ordinary AdicCompletion/IsAdicComplete module and ring lemmas. They do not give this derived sheaf theorem.

The first broad query and the second coefficient-specific phrasing therefore do not turn the item into a Mathlib leaf. The useful generic hits are reused through existing nodes.

## Review by Q71

I read the current literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/sk-prop-sp-composition-comparisons.md and its proof, together with the current unit statement and proof. The unit's route passes from actual tower adjunctions to integral identities by total inverse limit, exactly the route of this split. I also read the chapter and unit records, the three-level rule in SETUP.md, GOAL.md, the worker brief, and delivery-errors B–E. There are no new-node sources to review.

For step 1 I opened the statements of det-sp-normalized-equivalence, det-sp-integral-direct-image-tower, det-sp-integral-adjunction-bijection and lem-sp-tower-adjoint-compositor-realization. The first supplies an actual adjoint equivalence with natural unit/counit. The direct-image node gives the specified integral limit comparison, the adjunction node specifies the natural Hom chain and both adjunction structures, and the tower node expressly preserves the normalized subcategories. The equivalence and the integral comparisons are part of this item's given data; the proof does not silently apply an unbounded reconstruction theorem to a different coefficient category. The strict varying-coefficient towers, uniform bounds, and completed coefficient sheaves are the ones in those statements. Their formal consequence is full faithfulness on the full normalized categories.

For step 2 the same equivalence statement gives invertibility of kappa on precisely those normalized towers, and the tower node states that alpha_bullet and theta_bullet are natural isomorphisms of actual derived-tower functors. Applying L to the two displayed composites therefore gives natural isomorphisms with the exact domains and targets in the item. I checked the inverse direction of H_f(kappa_Y) and did not replace total inverse limit by a degreewise construction.

Step 3 uses only counit naturality and these actual tower maps. I checked the types of the two composite reduction identifications: b_{g,f}: r_Z barF_g barF_f -> F_g F_f r_X and c_{f,g}: r_X barH_f barH_g -> H_f H_g r_Z. Substituting the left internal composite into kappa_B rL(v) = v kappa_A proves the left equation; substituting the right internal composite and cancelling H_f(kappa_Y) proves the right equation. Essential surjectivity via kappa_C extends the equations from reduced integral objects to every normalized tower. This is an equality in the tower category, with no appeal to its finite evaluations.

For step 4 I opened lem-sp-fully-faithful-adjunction-restriction and def-weil-pbc-composite-adjunction and checked their full statements against the pinned Mathlib sources. The former expressly gives the b,c-dependent reduced unit and counit formulas, rather than merely existence of an adjunction. Its Hom chain agrees with det-sp-integral-adjunction-bijection, so it applies to the adjunction chosen in the item. The latter is a Mathlib leaf whose statement actually includes the composite Hom bijection and both unit/counit formulas, not an unsupported definition cited for an existence theorem. Composing the two Hom chains cancels the middle r_Y Hom bijection; naturality places the b and c factors in exactly the order used here. This proves the reduced composite counit formula from those two statements.

For step 5 the tower node states the unique counit-preserving comparison and the explicit composite counit. I wrote its defining counit equation with the left compositor inserted, then checked the actual chain of substitutions: naturality of b, the right reduction equation, the tower counit identity, naturality of alpha, the left reduction equation, and the single-functor counit formula. All arrows end in r_Z K. Full faithfulness from the equivalence then proves the integral equation. This step is a direct algebraic calculation from cited statements and previous steps; it does not hide an additional lemma.

For step 6 I read det-sp-unique-right-adjoint: its statement gives uniqueness even among families of maps, as well as the natural isomorphism. Precomposing Hom maps by baralpha^{-1} constructs the second adjunction for the same left functor and gives its counit explicitly. Applying that uniqueness statement to the equation already established identifies precisely the displayed bartheta. The composite-adjunction statement gives the integral composite counit; the specified integral Hom chain fixes its unit as well. All functors remain between the full categories in the hypotheses.

I tested the formulas with identity equivalences (kappa = identity), where they reduce to alpha_bullet and theta_bullet, and with f or g the identity, where their typed domains and the counit normalization remain correct. I also checked zero objects, empty schemes, d=e=0, and E=Q_ell: no division by dimensions, nonempty-object hypothesis, flat coefficient change or invertibility beyond the given equivalences is used. Arbitrary coherent nonidentity kappa is handled by the explicit naturality equations, so the proof is not restricted to strict identity models of the equivalence.

Against B–E: there are no new statement-only nodes to confuse with clauses of the item; every proof citation was opened and is accompanied by a verbatim excerpt; every non-elementary ingredient is an existing cited statement; the categorical leaves are reusable generic tools; the geometry and coefficient hypotheses are unchanged; and no parent or citer is used in a way that could make a cycle. All six steps are shorter than 2000 characters, and the reduction and counit calculations are fully written. No route departure or SGA source is involved.

## Validation

The required deliver.py --no-push finished successfully: `OK (not pushed) deliver/Q71/lem-sp-integral-compositor-limit-realization at 8fef2bbcf3c: preflight passed`. The server ran the delivery preflight, including check_dag and review_split. No local checker or compiler was run.
