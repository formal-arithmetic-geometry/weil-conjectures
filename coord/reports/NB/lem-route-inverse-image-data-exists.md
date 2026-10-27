# Worker report: lem-route-inverse-image-data-exists

## Files written

- `dag/nodes/sec-zeta-weil/lem-route-inverse-image-data-exists.json` — item, split into five assembly steps.
- `dag/nodes/sec-zeta-weil/lem-route-inverse-image-ring-functor.json` — statement node; Mathlib searches found only general adjunction/sheafification APIs, so no leaf.
- `dag/nodes/sec-zeta-weil/lem-route-inverse-image-module-lift.json` — statement node; Mathlib has `SheafOfModules.pullback` but no matching arbitrary-site algebraic inverse-image package.
- `dag/nodes/sec-zeta-weil/lem-route-inverse-image-constant-comparison.json` — statement node; Mathlib has constant-sheaf APIs but no inverse-image comparison for this hypothesis set.
- `citations.json` — verbatim quotes for every node cited by every item proof step.

## Attachments

None. `CategoryTheory.ConstantCompletion.inverseImageData_exists` in `lean/Sheaf/Paper/ConstantCompletionInverseImageExists.lean:106-109` still has `sorry`; no sorry-free declaration in the checked source states the item.

## WANTED

None. The Stacks source is present at `literature/stacks-project/sites.tex` and `sites-modules.tex`.

## Not duplicates

- `lem-route-inverse-image-ring-functor` vs `lem-weil-pbc-etale-inverse-image-ring-lift`: the existing node is restricted to scheme étale sites and a specified étale pullback; the new node is for arbitrary small sites and an arbitrary finite-limit-preserving adjunction.
- `lem-route-inverse-image-module-lift` vs `lem-weil-pbc-geometric-module-construction`: the existing node constructs modules after separately supplied rings and scalar map and includes a right-side module construction; the new node specializes the target scalar map to the ring lift and packages exactly the AlgebraicInverseImage data needed here for every source ring.
- `lem-route-inverse-image-constant-comparison` vs `lem-weil-pbc-constant-ring-inverse-image-comparison`: the existing node concerns one constant ring on a scheme étale morphism; the new node asserts a natural comparison for all commutative rings and arbitrary site adjunctions.

## What was checked and corrected

The provisional item was machine-generated from the Lean signature and docstring. I retained its hypotheses `L ⊣ V` and `PreservesFiniteLimits L`, expanded `InverseImageData` into its four actual fields, and made the blueprint `from.place` and `same_as` fields explicit. The proof now follows Tags 00YV, 03D2, and 099L: first lift the set adjunction to commutative-ring objects, then transport module operations, then use naturality for `ring_naturality`, and finally package the canonical constant comparison. No coefficient category, site morphism, or flatness assumption was added.

## Review by NB

I read the Lean declaration and docstring in `Sheaf/Paper/ConstantCompletionInverseImageExists.lean`, including the exact `InverseImageData` structure in `Sheaf/Paper/ConstantCompletionInverseImage.lean`, and checked that the item statement names every field used by the declaration. I read Stacks `sites.tex` at Tags 00YV and 099L and `sites-modules.tex` at Tag 03D2. The ring-functor node cites the existing statements identifying sheaves of rings with ring objects and lifting a finite-product-preserving adjunction; its hypotheses are exactly the arbitrary small sites, the set adjunction, and finite-limit preservation. The module-lift node cites the existing geometric module-construction statement and the algebraic-inverse-image transport statement; its target ring is explicitly `rings.obj R` and its comparison is the `e_R` supplied by the ring node. The constant-comparison node uses the constant-sheaf definition and the left-adjoint/terminal/coproduct argument from 00YV; its conclusion is a natural family in all ring maps.

For the item proof, Step 1 takes only the ring functor and comparison stated by `lem-route-inverse-image-ring-functor`; Step 2 takes only the module and graph transport stated by `lem-route-inverse-image-module-lift`; Step 3 is the naturality square for that same `e_R`, so it is elementary; Step 4 takes the natural constant isomorphism stated by `lem-route-inverse-image-constant-comparison`; Step 5 is record packaging and is elementary. I checked the edge cases of the construction on the identity adjunction (the ring and module lifts are identity transports) and on the zero ring (the constants component is the unique map), so no nonempty-site or nonzero-coefficient hypothesis was silently introduced. I also searched the whole DAG and blueprint for the three new claims and recorded the specialized étale nodes as non-duplicates. All required Mathlib searches were run with the item or each node's own id and their digests are retained in `searches.jsonl`.

## What remains

The three new statement nodes are intentionally unsplit and join the stage-1 queue. No Lean file was written and no compiler or Lake command was run, per the stage-1 restriction.
- `lem-route-inverse-image-constant-comparison` vs `lem-sc-etale-inverse-image-joint-representatives`: existing node concerns joint representability on an étale site, while the new node compares ring-valued constant sheaves under an arbitrary site adjunction.
- `lem-route-inverse-image-constant-comparison` vs `def-pd-proetale-section-module-functors`: existing node defines pro-étale section/module functors, while the new node proves a general natural constant-sheaf comparison.
- `lem-route-inverse-image-constant-comparison` vs `def-pd-section-derived-realization`: existing node is a derived section realization definition, while the new node is an inverse-image constant-ring theorem.
- `lem-route-inverse-image-constant-comparison` vs `def-pd-section-derived-tensor-data`: existing node defines derived tensor data, while the new node compares constant ring sheaves.
- `lem-route-inverse-image-constant-comparison` vs `def-pd-section-module-operations-data`: existing node defines section module operations, while the new node proves naturality of constant-ring comparison.
- `lem-route-inverse-image-constant-comparison` vs `lem-pd-module-ringed-topos-derived-comparison`: existing node compares derived module objects, while the new node is an underived constant-sheaf comparison.
- `lem-route-inverse-image-constant-comparison` vs `def-pe-comparison-torsor`: existing node defines a comparison torsor, while the new node gives a canonical constant-sheaf isomorphism.
- `lem-route-inverse-image-constant-comparison` vs `def-pe-finite-discrete-presentation-encoding`: existing node defines finite-discrete presentations, while the new node treats arbitrary commutative rings and sites.
- `lem-route-inverse-image-constant-comparison` vs `lem-pe-constant-left-module-inverse-image-coherence`: existing node gives composition/localization coherence for a fixed constant scalar module lift, while the new node compares all constant commutative-ring sheaves.
- `lem-route-inverse-image-constant-comparison` vs `lem-pe-constant-left-module-inverse-image`: existing node constructs modules for one fixed ring, while the new node constructs the natural ring-sheaf constant comparison.
- `lem-route-inverse-image-constant-comparison` vs `lem-pe-constant-left-module-transport`: existing node packages a fixed-ring module transport, while the new node is a natural comparison for the entire commutative-ring category.
- `lem-route-inverse-image-constant-comparison` vs `lem-pe-constructible-comparison-module-exact`: existing node concerns exactness of constructible module comparison, while the new node concerns constants and no exactness.
- `lem-route-inverse-image-module-lift` vs `def-a1-integral-completed-tower-pullback-universes`: existing node defines an integral tower pullback, while the new node constructs an arbitrary-ring module lift from a set adjunction.
- `lem-route-inverse-image-module-lift` vs `def-a1-integral-finite-pullback-tower`: existing node defines finite pullback towers, while the new node states graph transport for every module sheaf.
- `lem-route-inverse-image-module-lift` vs `def-a1-pulled-koszul-tower-normalization`: existing node defines Koszul tower normalization, while the new node constructs AlgebraicInverseImage data.
- `lem-route-inverse-image-module-lift` vs `def-per-etale-differential-pullback-presentation`: existing node defines an étale differential presentation, while the new node handles arbitrary sites and modules.
- `lem-route-inverse-image-module-lift` vs `lem-per-independent-scalar-inverse-image`: existing node compares scalar extensions after two already-specified algebraic inverse images, while the new node constructs the inverse-image module data itself.
- `lem-route-inverse-image-module-lift` vs `lem-per-rational-ordinary-pullback-composition`: existing node proves rational pullback composition, while the new node is an underived module-lift construction.
- `lem-route-inverse-image-module-lift` vs `lem-per-rational-ordinary-pullback-identity`: existing node proves rational pullback identity, while the new node transports module operations for arbitrary ring sheaves.
- `lem-route-inverse-image-module-lift` vs `def-pod-scalar-pullback-generator`: existing node defines a scalar pullback generator, while the new node supplies the general AlgebraicInverseImage tuple.
- `lem-route-inverse-image-module-lift` vs `lem-pod-canonical-module-adjunction-unit`: existing node concerns a canonical module adjunction unit in a specialized setting, while the new node has no derived or scalar-generator assumptions.
- `lem-route-inverse-image-module-lift` vs `lem-pe-coefficient-comparison-fixed-pullback`: existing node compares fixed coefficient pullbacks, while the new node constructs the module functor and operation graphs for each ring sheaf.
- `lem-route-inverse-image-module-lift` vs `def-weil-pbc-algebraic-inverse-image`: existing node is the definition of the AlgebraicInverseImage notion, while the new node proves existence of such data from the finite-limit adjunction.
- `lem-route-inverse-image-module-lift` vs `def-weil-pbc-module-inverse-image-action`: existing node defines an action for a supplied continuous-site construction, while the new node proves a full module lift with underlying comparison.
- `lem-route-inverse-image-ring-functor` vs `lem-sc-etale-inverse-image-joint-representatives`: existing node concerns étale joint representatives, while the new node lifts arbitrary sheaf adjunctions to commutative-ring objects.
- `lem-route-inverse-image-ring-functor` vs `def-pd-proetale-section-module-functors`: existing node defines pro-étale section/module functors, while the new node constructs a ring-sheaf functor.
- `lem-route-inverse-image-ring-functor` vs `def-pd-section-derived-realization`: existing node defines derived realization, while the new node is an underived ring-object lift.
- `lem-route-inverse-image-ring-functor` vs `def-pd-section-derived-tensor-data`: existing node defines derived tensor data, while the new node concerns ring-sheaf adjunctions.
- `lem-route-inverse-image-ring-functor` vs `def-pd-section-module-operations-data`: existing node defines section module operations, while the new node constructs a functor on all commutative ring sheaves.
- `lem-route-inverse-image-ring-functor` vs `lem-pd-module-ringed-topos-derived-comparison`: existing node is a derived module comparison, while the new node is the ring-object lift before modules.
- `lem-route-inverse-image-ring-functor` vs `def-pe-comparison-torsor`: existing node defines a coefficient comparison torsor, while the new node gives an adjunction on ring sheaves.
- `lem-route-inverse-image-ring-functor` vs `def-pe-finite-discrete-presentation-encoding`: existing node defines finite coefficient encodings, while the new node is coefficient-independent.
- `lem-route-inverse-image-ring-functor` vs `lem-pe-constant-left-module-inverse-image-coherence`: existing node gives coherence for one fixed constant ring module lift, while the new node lifts all commutative ring objects.
- `lem-route-inverse-image-ring-functor` vs `lem-pe-constant-left-module-inverse-image`: existing node constructs a module inverse image for one ring, while the new node constructs the ring-sheaf functor itself.
- `lem-route-inverse-image-ring-functor` vs `lem-pe-constant-left-module-transport`: existing node transports modules for one fixed ring, while the new node handles arbitrary commutative ring sheaves and their ring adjunction.
- `lem-route-inverse-image-ring-functor` vs `lem-pe-constructible-comparison-module-exact`: existing node proves exactness for constructible modules, while the new node proves no exactness and concerns ring objects.
