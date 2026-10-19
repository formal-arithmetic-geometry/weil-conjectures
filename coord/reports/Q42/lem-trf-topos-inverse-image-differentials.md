# Worker report: lem-trf-topos-inverse-image-differentials

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-topos-inverse-image-differentials.json` — item, split; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-sheafified-module-differentials-cokernel.json` — new statement node, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-geometric-inverse-image-exact.json` — new statement node, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-geometric-inverse-image-free-module.json` — new statement node, unsplit; no Mathlib match.
- `citations.json` — verbatim statement quotes for every proof-step citation.

Attachments: none. A grep of both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` found no declaration tagged `(blueprint: lem-trf-topos-inverse-image-differentials)` or stating this result. No WANTED items.

The imported item had an empty proof. I retained its statement and dependencies. The source is `literature/stacks-project/sites-modules.tex`: Tag 08TP is the sheafification/cokernel presentation and Tag 08TQ is the exact inverse-image pullback comparison. The imported blueprint ancestry is `lem-trf-local-term-locality`; I filled the previously unspecified `blueprint.from.place` and recorded the underived-input sentence realized by the split.

## Review by Q42

I read the complete item node, the chapter `sec-trace-formula`, and unit `sk-i-curve-zero`. I checked the four proof steps against Tags 08TP and 08TQ. Step 1 uses the new 08TP node for the explicit free-module relation-map cokernel, together with the existing sheafification, Kähler-differential, and sheaf-module definitions; those statements provide exactly the sheafified sectionwise object and its universal derivation. Step 2 uses the exact inverse-image node and free-module comparison node, plus the geometric-morphism and sheaf-module definitions: their statements provide finite-limit preservation, exactness on underlying abelian sheaves, and preservation of the free generators and finite-product comparisons. Step 3 uses the cokernel and universal-property clauses verbatim to construct the canonical map and inverse. Step 4 uses generator preservation, exactness, and the composite inverse-image clause of the geometric-morphism definition; both identity and composite comparisons are forced by the same generator and cokernel universal property.

For each new node I checked the hypotheses and source place. The sheafified-differentials node is exactly Stacks 08TP and introduces its site and presheaf ring map. The inverse-image-exact node states the first assertion of Stacks 04JC and explicitly limits the module claim to transported scalars (it does not invoke the separate flat tensor-pullback assertion). The free-module node states the generator-preserving comparison needed in 08TQ for an arbitrary finite-product-preserving left adjoint. I searched the entire DAG and blueprint for duplicates and found none. Mathlib searches were run and recorded for all three nodes with LeanFinder, Loogle, and grep; the closest hits (`KaehlerDifferential`, `leftAdjoint_preservesColimits`, and `SheafOfModules.pullbackObjFreeIso`) are only ring-level or continuous-site specializations and do not state these general sheaf-topos lemmas. Small cases checked include the identity geometric morphism, the zero ring map (all relation generators map to zero), and a composite of two identity morphisms; the comparison is respectively the identity and the composite identity.

No statement correction or source error was found. The item’s `tool_uses` records the generic adjunction lift `lem-weil-pbc-adjunction-lifts-group-ring-objects`, used only to transport module structure; the trace-formula unit has no more specific algebraic-structure node.

## Not duplicates

lem-trf-geometric-inverse-image-exact vs def-weil-pbc-etale-coefficient-injective-target: the existing node is a target-specific injective-coefficient statement with 04JC as a source tag; the new node is the generic geometric-morphism exactness lemma for arbitrary small sites.
lem-trf-geometric-inverse-image-exact vs lem-weil-pbc-cohomology-module-square-compatibility: the existing node concerns a cohomology-module square, while the new node concerns exactness of inverse image on abelian sheaves.
lem-trf-geometric-inverse-image-exact vs lem-weil-pbc-etale-coefficient-injective-cokernel-system: the existing node is an étale coefficient cokernel-system construction, while the new node is generic topos exactness.
lem-trf-geometric-inverse-image-exact vs lem-weil-pbc-etale-coefficient-injective-system-data: the existing node records injective-system data, while the new node proves exactness of inverse image.
lem-trf-geometric-inverse-image-exact vs lem-weil-pbc-etale-coefficient-injective-system-embedding: the existing node is an embedding of a specific étale coefficient system, while the new node is generic geometric-morphism exactness.
lem-trf-geometric-inverse-image-exact vs lem-weil-pbc-etale-coefficient-injective-system: the existing node concerns one étale injective system, while the new node applies to all small-site geometric morphisms.
lem-trf-geometric-inverse-image-exact vs lem-weil-pbc-etale-replacement-stage-diagram: the existing node is a replacement diagram, while the new node is an exactness statement.
lem-trf-geometric-inverse-image-exact vs lem-weil-pbc-etale-system-cone-functor: the existing node constructs a cone functor, while the new node proves exactness of inverse image.
lem-trf-geometric-inverse-image-exact vs lem-weil-pbc-proetale-module-inverse-image-comparison: the existing node compares pro-étale module inverse images, while the new node treats arbitrary geometric morphisms and abelian sheaves.
lem-trf-geometric-inverse-image-exact vs lem-weil-pbc-proetale-module-inverse-image-scalar-graph: the existing node is a scalar-graph construction for pro-étale modules, while the new node is generic abelian exactness.
lem-trf-geometric-inverse-image-exact vs lem-weil-pbc-site-pullback-abelian-exact: the existing node assumes a presented continuous site functor and its constructed pullback; the new node applies to an abstract geometric-morphism datum and also records transported module cokernels.
lem-trf-geometric-inverse-image-exact vs lem-weil-pbc-site-pullback-abelian-underlying: the existing node gives an underlying-sheaf comparison for a site pullback; the new node gives exactness for an abstract geometric morphism and its module transport.
lem-trf-geometric-inverse-image-free-module vs lem-trf-topos-inverse-image-differentials: the item states the full differential isomorphism and naturality/coherence conclusion; the new node is only the free-module generator comparison used in its proof.
lem-trf-sheafified-module-differentials-cokernel vs lem-trf-topos-inverse-image-differentials: the item compares differentials under inverse image; the new node is the preliminary sheafification/cokernel presentation used to state that comparison.
