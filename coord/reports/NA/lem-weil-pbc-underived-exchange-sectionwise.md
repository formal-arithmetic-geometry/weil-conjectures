# Worker report: lem-weil-pbc-underived-exchange-sectionwise

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-underived-exchange-sectionwise.json: statement, split into five proof steps; Mathlib searches find infrastructure, but no declaration stating the etale representative formula and its comparison with exchange.
- citations.json: one entry per proof-step citation, with verbatim statement quotations.
- report.md: this report.

No new nodes; zero new Mathlib leaves. searches.jsonl contains the actual search-command log. write_split.py is sandbox-only scratch, not a delivery file.

## Attachments

None. I searched the project source by the item's exact id, by section/exchange terminology, and by baseChangeMap. Square.lean provides AlgebraicGeometry.Etale.baseChangeMap, upperStar_map_baseChangeMap_app_counit and unit_map_baseChangeMap_app (lines 85, 103, 165), but none states the sectionwise representative formula. They cover the categorical part only. UpperLowerStar/Defs.lean lines 227–253 gives the inverse image and adjunction, not this lemma. The item's slopmaster2 audit is none. No master sorry declaration is claimed as a proof.

## WANTED

None. The current blueprint and all Stacks sources used are available locally. No SGA source is used.

## Source error and statement clarification

STATEMENT-DISPUTED: the literal instruction to restrict a section of F along A = X' times_{Y'} V -> X times_Y W need not be a restriction map in X_et. For example, take X = Y = Spec(k), X' = Y' = A^1_k, f and f' identities, g and g' the structure map, W = Spec(k), and V = Y'. This is a Cartesian square, but A = A^1_k is not an etale X-object, so F(A) is not defined. The intended operation is the unit F(K) -> (g'^{-1}F)(X' times_X K), followed by restriction within X'_et. The revised statement writes exactly this well-typed operation. Its conclusion and hypotheses are unchanged in mathematical intent.

The old imported proof also identifies sections of the sheafified inverse image with a filtered colimit and deduces equality from a common presheaf refinement. The colimit formula applies before sheafification. A representative's sheafified class is well-defined, but the proof must also handle any identifications introduced by sheafification. Step 3 uses the actual universal property of sheafification, so it requires neither that assertion nor a new local-representability theorem. The revised statement explicitly defines a representative's sheafified class and does not assert global representability of every sheaf section. This is not a new hypothesis on the conclusion.

The old proof's evaluation of f^{-1}f_*F “over W” is also ill-typed when W is only an etale Y-object. The new proof compares sheaf morphisms under the composite adjunction instead.

I read both the master blueprint node (which has a Proof section) and the main-20261015 node (which currently has the statement only), together with the current sk-def-exchange unit and updated underived-exchange definition. The latter specifies that theta is the canonical composition isomorphism. The split does not replace the unit's mate construction or make any derived or coefficient-category identification.

## Not duplicates

No new nodes, so no new/existing same-tag pairs arise. Searches of the whole DAG and blueprint for sectionwise, underived-exchange, inverse-image-composition, and the infrastructure tags 00VC, 00VE, 00WH, 03CB locate the existing inverse-image, sheafification and composition nodes used here. The sectionwise formula is also present as an assertion in def-weil-pbc-underived-exchange, but the present lemma supplies its well-definedness and comparison proof rather than assuming that assertion. Naturality, identity/pasting, cohomological exchange and proper base change are different statements; same_as is empty.

## Review by NA

I checked the item against Stacks etale-cohomology.tex, Tag 03Q0 (definition-inverse-image and equation-pullback), sites.tex Tags 00VC and 00VE (the indexing category, restriction maps, unit coprojection and adjunction), Tag 00WH (unique extension to sheafification), and Tag 03CB (composition through the common right adjoint). I read the exact statements of every cited DAG node. No new node needs a separate source audit.

Step 1 uses def-weil-size-convention to work with small skeletons; lem-weil-pbc-etale-base-change-finite-limits supplies the functor and the finite-limit hypothesis needed by lem-weil-pbc-presheaf-pullback-sets-left-exact. The latter explicitly supplies both the colimit formula and the unit coprojection, not merely left exactness. def-weil-pbc-sheafification supplies the hom bijection, and lem-weil-pbc-etale-inverse-image-algebraic-structures explicitly identifies set and abelian pullbacks compatibly with adjunctions and units. These statements justify the passage from set representatives to abelian sheaves. I have not silently treated the underlying set of an arbitrary colimit of groups as a set colimit.

Step 2 uses def-weil-pbc-cartesian-square for the arrows and chosen identification, def-weil-pbc-direct-image for B(V) = Q(A), def-weil-pbc-inverse-image for the adjunction unit, and def-weil-pbc-category-colimit for the cocone universal property. I checked the domain of every restriction: K_i is etale over X, X' times_X K_i and A_i are etale over X', and ell_a is a morphism of the X' site. Naturality of the unit yields the written equality for each h:W_1 -> W_2; functoriality gives compatibility in V. This is an elementary cocone check, not an uncited independence theorem.

Step 3 uses precisely the universal property in def-weil-pbc-sheafification: the target is already a sheaf by the direct-image definition. This handles equality after sheafification rather than presuming equality in a presheaf colimit. The inverse-image definition gives the adjunct formula g_*psi composed with eta_g, and the Cartesian identification gives the displayed map d. Evaluating at (W,id,s) identifies this adjunct with f_*eta_g'. No separate mate theorem is assumed here.

Step 4 invokes the actual statement of def-weil-pbc-composite-adjunction, including its hom bijection and unit. The statement of lem-weil-pbc-inverse-image-composition part (1) supplies the components of the right-adjoint comparison d and part (2) supplies the exact unit compatibility needed to take the adjunct of theta. def-weil-pbc-cartesian-square fixes the square isomorphism. I checked both orientations: the adjunct of r_0 goes from H to g_*f'_*Q, and the intermediate composite goes through f_*g'_*g'^{-1}f^{-1}H. This is a generic off-unit tool use declared in split_report.tool_uses; it does not replace the exchange unit's route.

Step 5 uses naturality and the triangle identity of the inverse-image adjunction (the defining adjunction data), writes out their application, and then the injectivity of the composite hom bijection in def-weil-pbc-composite-adjunction. def-weil-pbc-underived-exchange is used only for its categorical definition as the unique adjunct of r_0, not its claimed section formula. Thus no step uses the item itself or a circular dependency.

I tested identity squares (the formula restricts and sheafifies the original representative), zero F (all maps vanish), W or V empty (the unique section maps to the unique section), and the A^1 example above (the corrected target and restriction are now defined). No properness, noetherian, torsion, coefficient finiteness or invertibility hypothesis is used. This is a statement about abelian sheaves, without substitution of condensed or derived coefficients.

Against delivery-errors B–E: all notions are introduced or cite existing definitions; no new node, duplicate, hollow unsplit proof or missing search record is created; all citations quote actual statements (citations.json); Stacks sources are specified by tag and label; the smallness hypothesis is explicit; every non-elementary input is cited; the two elementary construction steps and the final triangle calculation are written out; neither a source proof nor a definition with insufficient content is used as a lemma. All five steps are below 2000 characters. The Mathlib candidates read in Sites/Sheafification.lean, ConcreteSheafification.lean, Pullback.lean and Adjunction.lean supply the reused general tools, not the whole etale formula in one specialization. The exact queries are copied from searches.jsonl, with their actual results.

## Unfinished work

None in this one-level split. The pre-existing dependencies retain their own statuses. No Lean was written or compiled; no build, Lake, git command in the shared repository, launcher edit, or external message was used.

## Validation

Server checks and required delivery dry run are run after this report and repaired if necessary; their results are recorded below before the final push.

- Server-only check_dag: OK, no finding introduced by the sandbox or on its nodes.
- Required deliver.py --no-push: exited 0 and printed OK (not pushed), preflight passed, provisional commit 021dc57754. A final dry run after this validation note binds the final report before pushing.
