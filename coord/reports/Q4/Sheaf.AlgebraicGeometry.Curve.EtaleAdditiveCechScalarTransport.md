## What changed

The target `AlgebraicGeometry.Scheme.Modules.additiveCech_scalar_transport` now has a
complete proof from a coefficient augmentation compatibility lemma and a proved canonical
comparison naturality lemma. Its signature is unchanged.

The new module `EtaleAdditiveCechScalarChainAction` constructs the global and total
endomorphisms from `InjectiveResolution.desc`, actual functor maps, flip and totalization.
The same module proves `additiveCech_alpha_natural` by total-summand naturality,
product projections, and naturality of the resolution map. The target applies `cyclesMap` to these concrete maps and takes `z' = r • z`. It proves
the augmentation equations using `cyclesMap_i`, transports equality of total classes
using `homologyπ_naturality`, and proves the coefficient scalar identity using linearity
of the ModuleCat homology projection. No definition chooses a witness from an unproved
existence theorem.

The new module `EtaleAdditiveCechGlobalMapNaturality` proves
`additiveCech_global_map_naturality` using the constant-sheaf sections adjunction,
`global_cocycle`, and `InjectiveResolution.extMk_comp_mk₀`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.additiveCech_scalar_transport`.

Also proved:
`AlgebraicGeometry.Scheme.Modules.additiveCech_global_map_naturality`,
`AlgebraicGeometry.Scheme.Modules.additiveCech_alpha_natural`, and
`AlgebraicGeometry.Scheme.Modules.additiveCech_scalar_chain_action`.
The definitions `additiveCechGlobalMap` and `additiveCechTotalMap` contain no holes.

No sorry remains in any delivered module, and no new hole is added. The construction
uses actual resolution descent and functor maps, rather than a choice from an
unproved existence statement. The net count for this delivery is one hole closed.

## No longer needed

No existing imports were removed. The normalization module remains needed by all
signatures. The old direct proof dependencies `def-sp-injective-resolutions`,
`def-pbc-etale-additive-cech-normalization`, and
`def-weil-pbc-etale-resolution-section-canonical-comparison` are now used through
the two new helper nodes instead of appearing in the target node's `proof_deps`.
Their definitions and modules remain needed; no original node or module is pruned.

The earlier proposed representative-existence and unconstrained homology-identity
helpers were discarded before delivery; neither their modules nor their nodes is delivered.

## Where the brief, the DAG or earlier work was wrong

The original node gives a valid informal chain-map plan, but does not expose a Lean
lemma for the actual alpha/beta component identities. Both alpha and beta identities are now proved. Canonical comparison naturality is proved rather than assumed.

Edge cases: the maps and their cycle projections exist without finite-cover, affine,
separatedness, or normalization assumptions. At zero and unit scalars, and in degree
zero, the same identities apply. Empty indexing families are handled by the actual
product and total-functor constructions. The component naturality theorem asserts no converse or uniqueness for augmentation
representatives.

## New nodes

`new-q4-additive-cech-scalar-chain-action`, in
`dag/nodes/sec-proper-base-change/new-q4-additive-cech-scalar-chain-action.json`, records
the two constructed maps, the proved alpha identity and proved beta compatibility theorem. Its
source is the functorial augmented double-complex diagram of Tags 01FD and 01EQ.

`new-q4-additive-cech-global-map-naturality`, in
`dag/nodes/sec-proper-base-change/new-q4-additive-cech-global-map-naturality.json`, records
the proved comparison naturality theorem. It follows the normalized Ext-cocycle formula
and the existing injective-resolution postcomposition lemma.

## Second reading by Q4

1. PASS: Compared the target module with the repository by diff. The sole existing
   theorem's signature and docstring are byte-for-byte unchanged; only its proof,
   proof-only imports, and whitespace changed. The other two modules are new.
   No existing definition, public import, hypothesis, or conclusion changed, so
   no interface change record or forced adaptation is required.
2. PASS: Compiled all three delivered modules in import order with lcompile.py,
   with no errors or warnings. There is no sorry, axiom, unsafe, opaque,
   implemented_by, or extern in the delivered Lean. A scratch copy with
   #print axioms checked both new map definitions and all four theorems:
   each uses only propext, Classical.choice, and Quot.sound, without sorryAx.
   The maps are actual functor images of the proved resolution descent.
3. PASS: No statement is left split off with sorry. The new proved statements are
   strictly intermediate: cochain-level augmentation compatibility and a global
   cycle comparison without a cover or total-class hypothesis. Reviewed zero and
   unit scalars, n=0, empty covers and empty intersections: the projection and
   adjunction arguments use no nonemptiness, division, or positive-degree step.
   Searched again for extMk composition, adjunction naturality, total-summand
   naturality, and local coefficient-map comparisons. The related private lemmas
   in EtaleAdditiveCechResolutionTransfer only treat the identity coefficient map;
   its public existence theorem cannot supply scalar transport. Mathlib's actual
   extMk_comp_mk₀ and functor/naturality APIs are used directly here.
4. PASS: Read the proof from its five output equations downward. The construction
   transports cycles with the actual global and total maps, uses z' = r • z,
   and transports equal homology classes by naturality. All imports provide data
   in signatures or proofs; the target's added imports are plain import. The old
   proof dependencies remain necessary through the helper nodes and normalization
   import. No module is pruned. Inspected sk-thm-p1.json realized: this item is
   below its realized nodes, and the curve/Artin–Schreier route is retained.
5. PASS after repair: The target node records the two helper dependencies and the
   actual cycle-transport proof. The two new nodes have source, searches,
   provenance, chapter/unit, and verbatim Lean statements. Added an explicit
   alpha-naturality proof step to the chain-action node so it documents both
   proved augmentation squares, not only beta. Existing-node changes are confined
   to proof, proof_deps and proof_origin.

Changes made by the second reader: added the chain-action node's alpha argument;
clarified all three replaced direct proof dependencies under No longer needed;
restored the target's original := indentation and removed an extra blank line.
No mathematical proof or statement needed repair. One original hole is closed,
zero holes are added, and zero modules are pruned.
