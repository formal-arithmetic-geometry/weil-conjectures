# Stage 1 report

Files written:

- dag/nodes/sec-smooth-purity/lem-pur-compact-support-strict-scalar-composition-prelude.json: repaired existing split; statement unchanged, no new nodes.
- citations.json: nine verbatim citation entries for every non-elementary use in proof steps 1–4.
- searches.jsonl: retained the fresh search records from the original delivery.

Attachments: none. No finished project declaration states this item.

The live lean/WeilConjectures tree has no declaration tagged (blueprint: lem-pur-compact-support-strict-scalar-composition-prelude) and no PurStrictScalar declaration. The similarly named declarations in lean/Sheaf/Paper/CompactSupportStrictScalarCompositionPrelude.lean are stage-3 interface material and are not an attachment for this stage-1 item.

## WANTED:

None.

What was wrong or corrected:

- Step 1 was not elementary because it asserted the strict derived-tower associator is the canonical composite-adjunction comparison. It is now non-elementary and cites lem-pur-strict-scalar-tower-associator.
- Step 2 now explicitly proves that the completed coefficient maps compose: their finite-level projections agree by the defining uniqueness in def-weil-completed-integral-scalar-data. The completed-associator localization lemma remains a proof dependency but was removed from stmt_deps, since it is not needed to state the item.
- Step 4 now cites lem-pur-compact-support-strict-scalar-mate for the identification of openTensor with localized ordinaryOpenTensor, and lem-pod-derived-exact-square-composition for derived square pasting. The ordinary open composition lemma remains cited for the finite-level equation.
- proof_origin.by is now agent, since this proof is reconstructed from the source module and existing DAG statements rather than copied from a named Stacks location.
- Removed the two unused tool_uses declarations. Removed the prior unit-file edit; this auxiliary item is not the unit key node.

## Not duplicates

lem-pur-compact-support-strict-scalar-composition-prelude vs lem-pur-completed-scalar-associator-localization: the existing node states only the completed tensor associator comparison and explicitly omits constant-restriction balancing, while this item also states constant-map composition, level selection, ramification, strict proper mates and open balancing.

lem-pur-compact-support-strict-scalar-composition-prelude vs lem-pur-strict-proper-restriction-composition: the existing node is the proper restriction/proper-image cocycle used as an input; this item derives the mate composition equation from it and also includes the other scalar-tower clauses.

lem-pur-compact-support-strict-scalar-composition-prelude vs lem-pur-ordinary-open-scalar-composition: the existing node is the ordinary open balancing equality; this item lifts it through strict towers and localization and includes proper composition and arithmetic clauses.

## Review by ND

I reread the returned item, its sk-thm-sf-compatibility binding, the chapter, the complete current statements of all nine cited dependencies, the Lean source CompactSupportStrictScalarCompositionPrelude.lean and OrdinaryOpenScalarComposition.lean, and the returned review references to openTensor_ordinary, localize_scalar_square, tensorComposition and completedMap_composition. I also compared the retained sandbox node with the current shared DAG and verified that the prior unauthorized unit realization file has been removed.

Step 1 performs the constant-map, ramification and index arithmetic calculations, but its associator clause is a genuine comparison theorem. I therefore cite lem-pur-strict-scalar-tower-associator, whose statement identifies the exact localization of the ordinary scalar-extension associator with the canonical leftAdjointCompIso for the specified adjunctions and restriction compositor. This citation covers the strict tower associator; the remaining map, ideal and natural-number calculations are written explicitly and use no hidden theorem.

Step 2 uses def-weil-completed-integral-scalar-data, whose construction defines each completed coefficient map as the unique map with prescribed finite-level projections. For E→F→L, the two composites have the same projection at every quotient level, so uniqueness gives composition of the completed maps. I then use lem-pur-completed-scalar-associator-localization, whose statement identifies completed derived tensor composition with successive exact-model comparisons followed by the localized ordinary associator. The latter is exactly the remaining normalization needed for the completed associator. The localization lemma is therefore a proof dependency only, not a statement dependency.

Step 3 still uses the proper restriction/proper-image cocycle from lem-pur-strict-proper-restriction-composition, the canonical tower associator from lem-pur-strict-scalar-tower-associator, and the composite-adjunction mate equation in clause 2 of lem-weil-pbc-mate-pasting. Their hypotheses match the finite coefficient tower and arbitrary scheme morphism in the item. The inverse cocycle and mate pasting are stated as the argument, with no unstated properness or finite-Tor condition.

Step 4 first applies lem-pur-ordinary-open-scalar-composition at each ordinary tower index. The strict scalar mate statement explicitly supplies the strict coefficient comparison and its exact open coefficient tensor map, which is the openTensor versus localized ordinary map bridge used here. The generic lem-pod-derived-exact-square-composition statement supplies the derived pasting identity for exact functors and natural-isomorphism squares; it is on the route through unit sk-lem-finite. Natural-transformation extensionality then carries the levelwise identity through localization and all quotient transitions. All three facts are quoted verbatim in citations.json.

I checked edge cases E=F=L (all scalar maps and associators reduce to identities), e=h=1 (the selection and ramification equations are identity equations), and empty or zero coefficient objects (the morphism equations are the unique zero or identity equations). No statement change or new node is needed. Fresh and retained Mathlib searches remain recorded in the node and searches.jsonl; none is an exact or one-line specialization, so there are zero Mathlib leaves and zero new nodes.
