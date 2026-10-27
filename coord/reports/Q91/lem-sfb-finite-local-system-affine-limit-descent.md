# Q91: lem-sfb-finite-local-system-affine-limit-descent

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-local-system-affine-limit-descent.json`: item, split into seven steps following Stacks 0GL2(3); no statement change; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-constructible-module-affine-limit-hom.json`: one new statement-only node, unsplit, no Mathlib match. It records the faithful and fully faithful parts of 09YU(3), rather than essential surjectivity or local-system descent.
- `citations.json`: one verbatim statement quotation for each of the 29 step citations. The full statements retain the hypotheses used in checking applicability.
- `searches.jsonl`, `hom-search-*.txt`, `item-search-*.txt`, and `write_split.py`: search evidence and sandbox preparation artifacts, not additional DAG nodes.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item identifier and for finite local systems, locally constant descent, and constructible limit descent. The project has finite locally constant representability and constructible essential-surjectivity declarations; neither states this item. No exact finished project declaration was found. No compiler or Lean/Lake command was run.

## Wanted literature

None. Read the local Stacks source, `etale-cohomology.tex`, at labels `lemma-category-loc-cst-is-colimit` (0GL2), `lemma-category-is-colimit` (09YU), `lemma-colimit-affine-sites` (0EYL), `lemma-constructible-quasi-compact-quasi-separated` (095E), and `lemma-pullback-constructible`. Read `topologies.tex`, label `lemma-etale-affine` (0218), including the preceding covering axioms. Also checked the official 0GL2 and 09YU pages against the local source. All mathematical sources here are Stacks or the existing blueprint; no SGA route is used.

## What needed attention

The imported statement is correct. Finite rings are Noetherian, and a finite module over a finite ring is of finite type, so 0GL2(3) applies without assuming that any scheme is Noetherian. The item had no proof. The main missing input was morphism descent and eventual equality for arbitrary qcqs stages: the existing constructible essential-surjectivity node expressly excludes these clauses. Existing derived Hom/Ext continuity nodes require Noetherian stages or a different inverse system and cannot discharge this input.

The proof does not call a descended morphism an isomorphism merely because its pullback is one. It descends the inverse separately and then detects both inverse identities at later stages. It also does not apply the affine-target covering refinement lemma to the possibly nonaffine scheme X. A finite affine open cover of X_i supplies affine targets after pullback to X. This avoids any assumption that the schemes are separated or that intersections of arbitrary affine opens are affine.

`tools/blueprint_refs.py ancestor` reports `None`: the inherited `created.item` chain ends at the non-node name `Sheaf.SixFunctors.CtfStabilityDirectImages`. The item already carries a precise place in the direct-image/alteration route and the entire intermediate via list. I preserved its null ancestor and place, used the prescribed null ancestor for the new node, prepended the item to the new node's via list, and specified the exact additional 0GL2-to-09YU proof sentence. Searches for finite locally constant sheaves, affine limits, 09YU, constructible morphisms, and Hom continuity found no imported blueprint statement to attach. I did not change ancestors or their metadata.

## Unfinished work

The item is completely split. The one new node is intentionally statement-only, as required for a one-level split. Its future proof is the faithful/fully faithful argument of 09YU(3): equality is detected on constructible equality loci; morphisms lift through finite constructible presentations and affine-etale section continuity, with finitely many relations made equal at a common later stage. This is a genuine reusable morphism theorem, not a clause asserting local-system essential surjectivity. No assertion in the item depends on that future proof being silently treated as finished.

## Mathlib searches

Ran the authorized msearch command five times for the new node and five times for the item: two distinct LeanFinder formulations, LeanSearch, Loogle, and grep in each case. Every query, result, and verdict is recorded as returned; all ten calls succeeded. Read the saved results. Hom queries returned affine-limit descent for scheme morphisms and structure-ring sections, ordinary module-presheaf colimit universal properties, and constructible subsets. These concern different objects from etale module-sheaf morphisms. The item queries also returned locally constant functions on profinite spaces, condensed discrete sheaves, and etale ring maps; none states finite local-system descent on schemes. Inspected the likely candidates in Mathlib's `AlgebraicGeometry/AffineTransitionLimit.lean` and `Algebra/Category/ModuleCat/Presheaf/ColimitFunctor.lean`; the former concerns schemes and structure-ring sections, the latter the universal property of a module colimit. Neither is an exact match or a one-line specialization. Retained the item's existing search evidence and added the searches from this session.

## Not duplicates

lem-sfb-constructible-module-affine-limit-hom vs lem-trf-constructible-etale-ext-continuity: the latter requires every scheme stage to be Noetherian and states derived Ext continuity; the new node covers underived maps on arbitrary qcqs stages.

lem-sfb-constructible-module-affine-limit-hom vs def-per-derived-hom-pullback: the latter defines maps on shifted derived Hom under pullback, without any existence or eventual-equality assertion.

lem-sfb-constructible-module-affine-limit-hom vs lem-weil-pbc-constructible-module-noetherian-descent: the latter descends objects to a Noetherian base, not maps between fixed stage objects.

lem-sfb-constructible-module-affine-limit-hom vs lem-weil-pbc-affine-free-etale-module-arrow-descent: the latter descends maps between special free-sheaf sums, allowing new models for both objects; the new node keeps given constructible stage objects fixed and also detects equality.

lem-sfb-constructible-module-affine-limit-hom vs lem-weil-pbc-pullback-sections-is-colimit: the latter is a section-colimit assertion on a fixed affine etale object; it does not state morphism descent from a general constructible source.

lem-sfb-constructible-module-affine-limit-hom vs lem-weil-pbc-constructible-module-limit-descent: its statement explicitly gives only essential surjectivity and explicitly excludes faithfulness/full faithfulness, the two clauses of the new node.

lem-sfb-constructible-module-affine-limit-hom vs lem-weil-pbc-affine-free-etale-module-eventual-hom-lift: the latter lifts maps from fixed finite affine free families, not from arbitrary constructible objects, and does not assert eventual equality.

lem-sfb-constructible-module-affine-limit-hom vs new-constructible-limit-descent-general: the latter descends objects with Noetherian coefficient rings, not maps between given objects or equality of such maps.

lem-sfb-constructible-module-affine-limit-hom vs lem-weil-pbc-limit-pullback-sections-colimit: the latter states continuity of sections on affine etale objects, not the Hom theorem for constructible sources.

lem-sfb-constructible-module-affine-limit-hom vs lem-weil-pbc-sets-pushforward-stalk-strict-henselization: the latter is a set-sheaf stalk formula for a strict-henselization system, not arbitrary-system module Hom continuity.

lem-sfb-constructible-module-affine-limit-hom vs lem-weil-pbc-pullback-sections-diagram: the latter constructs a section diagram and cocone and explicitly asserts no colimit property.

lem-sfb-constructible-module-affine-limit-hom vs lem-weil-pbc-affine-free-etale-family-models: the latter supplies object models for special finite free families and explicitly makes no assertion about arrows.

lem-sfb-constructible-module-affine-limit-hom vs lem-trf-bounded-constructible-derived-hom-continuity: despite its more general derived degree, this existing statement assumes Noetherian stages, which the present item does not have.

lem-sfb-constructible-module-affine-limit-hom vs lem-per-ind-etale-derived-hom-continuity: this existing result uses finite-field coefficients and affine etale objects over one fixed base; neither restriction is available for the arbitrary finite ring and arbitrary affine-transition scheme system here.

lem-sfb-constructible-module-affine-limit-hom vs lem-sfb-finite-local-system-affine-limit-descent: the new node asserts only lifting and eventual equality of maps between given constructible objects. It neither produces a global object model nor proves any local constancy. The item still constructs the cover, descends the two inverse maps, enforces the inverse identities, and verifies the local property.

## Review by Q91

I read B through E of delivery-errors.md, the worker brief, stage-1 contract, the three blueprint levels in SETUP.md, GOAL.md, and the recorded chapter and unit. I checked the item against the entire proof of Stacks 0GL2, not only its statement. For the new node I read both the Faithful and Fully faithful paragraphs of 09YU and its module paragraph. I kept the new node statement-only: it has no proof, no proof dependencies, and no proof sketch in its statement. I searched the whole DAG by tag and by the morphism/constructible/limit concepts, the blueprint references, and the project Lean sources before creating it. I opened the statements of every same-tag node listed above rather than inferring their contents from titles.

In Step 1, the limit-affine node gives affine projections, affine permanence gives their qcqs property, and qcqs permanence transfers qcqs from a stage to X. The finite-value constructibility definition accepts the one-stratum partition, and constructible-module descent gives exactly a constructible F_i and a module isomorphism. Its statement does not claim that F_i is locally constant; I did not use it for that.

In Step 2, finite affine open cover gives finitely many W_b. Affine permanence makes their inverse images affine. The etale affine-refinement statement actually assumes an affine target, which is now satisfied, and permits zero covering members. Restriction of a trivialization is pullback of a constant object, covered by constant pullback; the module inverse-image statement explicitly respects constant scalars and localized-site restriction. Pullback of a covering along an etale object is the covering axiom, and the affine base-change system gives the geometric affine pullbacks used here.

In Step 3, the finite-cover-factorization statement has precisely a fixed affine etale stage target W_b and finitely many affine limit-source objects. Its extra arrows are harmless structure maps to the terminal etale stage object, which that statement allows to be nonaffine. It asserts a covering at a stage and the required identifications over the limit target. The base-change-system statement explicitly preserves standard covering presieves, so passing all finitely many covers to a common upper bound preserves coverage. The W_b cover pulls back to an open cover; joint surjectivity of the combined etale family follows immediately. No use is made of a proof-internal construction of any cited node.

In Step 4, I checked the possible mismatch between the two constructibility predicates: the finite-value module constructibility comparison says exactly that they agree over a finite ring. Thus prop-constructible-pullback can be applied in the module coefficient category and the comparison applied back. Constants are constructible by the definition. Scheme-over-limit supplies the actual limit of the U_k, and affine permanence makes every U_k affine and its transitions affine. The new Hom node's qcqs hypotheses are therefore satisfied without adding Noetherian assumptions. Constant pullback and the scalar-compatible inverse-image composition identifications give the stated module-sheaf trivialization on the limit.

In Step 5, clause (1) of the new node gives a lift for each of the two maps with the stage objects fixed. Directedness handles the finite list of indices; inverse image is a functor and its composition identifications preserve the chosen limit maps. In Step 6, clause (2), not clause (1), detects the two inverse equations. I checked constructibility again after moving stages, using exactly the same comparison and pullback statements. The final identities are equations of module-sheaf maps, so the resulting isomorphisms retain the scalar structure. The elementary common-upper-bound operations and functorial identities are written out and have not been promoted to nodes.

In Step 7, covering preservation, the definition of locally constant, and scalar-compatible composition finish the conclusion. The local isomorphisms are certificates for the already existing global F_l; no gluing theorem or overlap compatibility has been assumed. The step is elementary from those inputs. Generic tools from other units are explicitly declared in split_report.tool_uses; they supply the geometric/small-etale descent inputs to this prerequisite, not a replacement for the enclosing alteration/direct-image route.

I tested the empty limit and empty-stage cases: empty finite affine refinements and empty covering families are permitted, and common upper bounds still exist because I is nonempty. If X is empty but earlier stages are not, finite-cover descent forces a sufficiently late empty stage on each of the finitely many affine pieces, so the argument does not assume surjectivity of a projection. Zero rings and zero module values cause no difficulty; no freeness or positive rank is used. Disconnected schemes may have different M_{b,a}; a single constant module on the whole scheme is never asserted. A singleton index gives the original local system, and non-Noetherian stages are permitted at every use of a statement. Every non-elementary step is shorter than 2000 characters; none conceals a separately hypothesized comparison or an unrecorded standard lemma. JSON TeX has single mathematical backslashes after decoding. No statement dispute or source correction was needed.

## Validation

The preliminary server-side review_split check passed. The required deliver.py --no-push invocation exited successfully: `OK (not pushed) deliver/Q91/lem-sfb-finite-local-system-affine-limit-descent at 4569644d491: preflight passed`. The direct-delivery push uses the same node files, with this validation receipt added to the report.
