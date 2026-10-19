## Files written

- `dag/nodes/sec-smooth-purity/def-weil-proetale-inverse-image.json`: the existing item split, retained with no new dependency nodes; the former long ring-construction step was divided into three explicit proof steps.
- `citations.json`: verbatim statement quotes for every cited node at every proof step.
- `searches.jsonl`: Mathlib searches run for this item with `msearch.py`.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` found no sorry-free declaration carrying the item id, blueprint tag, or this full inverse-image definition. No Lean was written or compiled.

## WANTED

None. The item and its cited source locations are available in the repository's Stacks Project and site-theory literature.

## What was checked or corrected

The shared DAG already contained this complete split and its reviewed metadata. I copied the current item into the Q30 sandbox and retained its statement, dependencies, blueprint ancestry, proof route, and Mathlib search records. I did not create a new node: every non-elementary input is already represented by an existing DAG node, and the definition itself is not a Mathlib leaf. I checked the whole DAG and blueprint for duplicate statements and searched both read-only source trees for an exact project declaration before treating it as a split.

The split follows the Stacks pro-etale functoriality route. It constructs the base-change functor and its covering preservation from weakly etale and fpqc base change; checks final objects, fibre products, and finite limits; verifies continuity and the sheaf inverse-image/direct-image adjunction using the comma category indexed by the opposite of the stated indexing category; lifts the construction to rings and commutative rings; defines the constant-ring map and its adjoint; and verifies module actions, scalar extension, and direct-image restriction of scalars. I checked each hypothesis against the cited node statements, including the chosen small skeletons and larger-universe smallness, and confirmed that every `uses` entry appears in `proof_deps`.

The prior ring step was 2156 characters and combined three separate arguments. I split it into three steps so the operation-preservation argument, the ring-colimit universal-property argument, and the constant-section structure-map argument are independently reviewable. Their cited nodes and source place remain unchanged. All resulting proof steps are below 2000 characters. Edge cases checked include the identity morphism, empty schemes/sites, zero and commutative coefficient rings, nullary operations, and constant sections under restriction. No prohibited SGA source is used.

## Not duplicates

No new nodes were created, so there are no new duplicate pairs. The existing cited nodes are used for their stated generic site, topology, sheafification, ring-object, constant-sheaf, module, and tensor constructions; none is a restatement of this full pro-etale inverse-image definition.

## Review by Q30

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, delivery-errors sections B--E, the fixed chapter and unit records, the item node, and every cited dependency node. I also read the Stacks Project source locations recorded on the item (Tag 09A5 and the Sites tags 00X6, 06UM, 00VC, 00WX, 00YV, 0H7J, plus the Sites Modules tags 03D1/03D2) and the current main blueprint inverse-image materials. The source supports the base-change, finite-limit, continuity, adjunction, algebraic-structure, and module constructions in the five-part route.

For each proof step, I checked that the cited node statements say exactly what the step takes from them. Steps 1--2 use the pro-etale site, size convention, fibre-product, weakly-etale composition/base-change, fpqc-covering base-change, small-site, and left-exact site-functor statements. Step 3 uses the small-site, continuous-functor sheaf pullback/adjunction, and sheafification statements for the equalizer and comma-colimit construction. The first new step 4 uses the left-exact inverse image, group/ring-object lifting, constant-sheaf, and sheafification statements for operations and adjunction restriction; step 5 uses the same ring/sheafification inputs for the ring-colimit universal property; step 6 uses the constant-sheaf and sheafification inputs for `rho` and `c`. Step 7 uses the left-exact inverse image, sheaf-of-modules category, and sheaf tensor-product statements for module actions and scalar extension. `citations.json` contains 26 verbatim step/node quotes after this split.

I checked the statement's hypotheses and edge cases, verified that no cited step silently relies on an uncited theorem, and confirmed that the proof dependency union is exact. The Mathlib searches in `searches.jsonl` were actually run with the required search command; they found only generic sheaf-pullback, site-continuity, and pro-etale declarations, with no one-line theorem stating this complete construction. The item's `mathlib_match` remains null. No Lean compiler, Lake, build, or direct git command was run, and only this Q30 sandbox was modified.

## What I could not finish

No required mathematical portion remains unfinished. The remote delivery dry run is the remaining gate for this packet.

## Metadata issue for maintenance

The inherited node metadata binds this pro-etale inverse-image definition to `sk-def-sf-admissible`, whose unit statement is an unrelated exceptional-adjoint admissibility definition and whose `realized` fields are empty. The item's route and proof do not realize that unit. Per `coord/dag-sync.md`, I did not rewrite the maintainer-owned `unit` field or manufacture a realization; this requires authoritative metadata repair outside the worker sandbox.
