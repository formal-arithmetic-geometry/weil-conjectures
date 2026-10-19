# Stage-1 delivery report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-finite-closed-shriek.json`: existing item split into twelve proof steps; no new nodes.
- `citations.json`: verbatim statement quotations for every cited node in every proof step.
- `report.md`: this report.

## Attachments

No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this item. Grep by the item id, theorem title, and the finite closed exceptional names found no declaration.

## WANTED

None. The cited Stacks sources and blueprint proof are present in the repository.

## What was checked and corrected

The item source is `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-finite-closed-shriek.md`, order 2139. I also read the corresponding current `main-20261015` source at `sec-smooth-purity/sk-lem-sp-tower/lem-coef-finite-closed-shriek.md` and its proof, the fixed chapter and unit records, and every current DAG statement used by the item. The global hypotheses are checked throughout: (k=\overline{\mathbf F}_q), \(\ell\ne p\), finite coefficient rings and arbitrary unital finite coefficient map (A\to B), separated finite-type schemes, a closed immersion, bounded constructible finite-Tor input, and the chosen constructible exceptional functor.

Step 1 checks the finite-Tor constructible domains after scalar change using the etale-origin equivalence, flat constructible models, K-flat change of rings, constructibility closure, and the ringed-topos tensor comparison. I verified that each cited node states the relevant equivalence, flat model, K-flat preservation, constructibility closure, or tensor comparison. Step 2 applies the stated exceptional-preservation theorem separately at coefficient fields (E) and (L), preserving the same geometric chart family and using the theorem's explicit finite-Tor bounds; it does not use the level-varying clause to change coefficient fields. Step 3 tensors the two localization triangles and checks that the exceptional functor is the constructible adjoint named by the localization node. Step 4 uses finite direct-image coefficient exchange for both the closed map and its open complement, the pullback/tensor comparison, and the ordinary adjunction/projection mate to prove the open-unit square.

Step 5 uses triangulated TR3 and the two-out-of-three triangle lemma to obtain the first comparison map, then uses the stated full faithfulness of closed direct image and its constructible adjunction to identify that map with the counit-defined (b_{i,M}). Step 6 records the naturality and exceptional-counit equation directly from the adjunction Hom bijection. Step 7 checks composition of closed immersions by chaining the stated direct-image composition and finite direct-image coefficient cocycle and comparing both maps by their transposes. Step 8 now gives the successive coefficient comparison using an explicit K-flat balancing model and the arbitrary finite-algebra cocycle already stated by `lem-coef-finite-direct-image`; the current node's hypotheses do not assume flatness of either coefficient map.

I corrected the locally closed tail. Its construction is now a typed factorization (Rh^!=Rk^!j^*) with the etale-origin domain supplied by the compact-support composition theorem. The open coefficient map is constructed in (D(B)) by an explicit chain of the derived scalar-extension/restriction adjunction and the open (j_!\dashv j^*) adjunction; this repairs the earlier unsupported claim that an (A)-linear projection was automatically (B)-linear. The counit equation is obtained by transposing both sides through these adjunctions and applying the two triangle identities. The final two steps spell out successive coefficient and inner closed-composition coherence using the closed result and tensor associativity. I marked these scalar and coherence arguments non-elementary and cited the statements they use.

The Mathlib audit used the required `msearch.py` searches for the item: LeanFinder and LeanSearch returned only ordinary scheme-module or algebraic local-cohomology declarations, Loogle returned no relevant declaration, and Mathlib grep found only `Mathlib/Algebra/Homology/LocalCohomology.lean`, whose source was read and is unrelated. No new nodes were created, so no new-node Mathlib search records or duplicate section are needed. `citations.json` quotes each cited node's complete statement verbatim, satisfying the citation checker.

## Not duplicates

No new nodes were created; no duplicate pairs arise.

## Review by Q76

I reread the item, the master and current blueprint versions, the chapter and unit records, and all 31 distinct node statements cited by the twelve proof steps. I checked every hypothesis at the point of use: finite coefficient maps may be nonflat; the exceptional preservation theorem is applied at both coefficient fields; open complements are Noetherian, quasi-compact, separated and finite type; compact-support composition is used only on bounded-below etale-origin inputs; and all maps in the locally closed tail are typed in the (B)-coefficient derived category. I checked that the closed comparison is the specified counit-adjoint map, that the triangle argument identifies this map rather than merely producing an isomorphism, and that closed composition and coefficient-chain equalities are proved by injectivity of the relevant adjunction Hom bijections.

The correction I made was to replace the previous locally closed scalar-action assertion with the explicit scalar/open adjunction construction and its counit calculation. I also split the former long locally closed paragraph into construction, scalar comparison, counit, and coherence steps, and changed the nontrivial scalar/coherence steps from `elementary` to `false`. The blueprint ancestry is recorded in the item's `blueprint` and `split_report` fields; no route-level change or new node was introduced.

## What remains

No proof node remains unsplit below this item as part of this delivery; the existing cited nodes retain their own stage-1 statuses. No Lean source was written and no compiler or Lake command was run.
