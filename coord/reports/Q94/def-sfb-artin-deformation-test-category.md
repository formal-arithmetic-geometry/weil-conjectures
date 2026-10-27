# Worker report: def-sfb-artin-deformation-test-category

## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-artin-deformation-test-category.json`: definition, split; no complete Mathlib match. Added existing statement dependencies for finite-dimensionality, square-zero extension and Artinian maximal-ideal nilpotence. No new nodes and no new Mathlib leaves.
- `citations.json`: `[]`, since a definition has no proof steps.
- `searches.jsonl`: actual searches made by the required launcher search command. Inherited item searches are retained verbatim, including their results; they were not represented as searches made by Q94.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id and for predeformation, Schlessinger, cofibred and Artinian-test terminology. The Artinian infinitesimal-etaleness lifting file concerns scheme test diagrams, not this category, its formal objects or versality. No project declaration states the whole item. Mathlib provides local and Artinian rings, residue fields and pseudofunctors, but none of the hits supplies the complete deformation datum.

## WANTED

None. The sources used are present in `literature/stacks-project/`.

## Corrections and scope

The imported definition did not spell out what a local map is, the groupoid transport coherence, the transition isomorphisms that are part of a formal object, or the positive indexing. These are now explicit. The old phrase “transport of any sufficiently high xi_n” must be interpreted up to the specified comparison isomorphisms, not literal equality of objects. I fixed evaluation at the least positive N with m_A^N=0 and supplied the comparisons with all higher levels; this is the construction in 06HC. Completeness uses the canonical map to the inverse limit, not an unspecified abstract ring isomorphism. The tangent set is explicitly attached to a predeformation category. No vector-space structure on the tangent set is asserted without (S2).

The source's formal-defos base convention assumes a finite ring map Lambda to k. The item's finite-type R-to-k convention comes from artin.tex 07T4: choose an affine neighbourhood of the image point with a finite map to k. The unchanged category of marked Artinian R-algebras is the factorization-category formulation there. I did not strengthen finite type to module-finite over the originally given R. For example R=Z_(p), k=Q is allowed. The neighbouring `lem-sfb-artin-local-test-algebra` records the localization comparison, but depends on this definition and is deliberately not cited back, avoiding a cycle.

The current latest blueprint source is `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3). Its front matter still identifies `det-thm-sf-ctf-stability-direct-images`. The supplied definition is a supporting prerequisite several levels below this route, not a unit key node. The ancestor tool prints `blueprint.from.node = None`; I retained that inherited null and its explicit ancestry/via list, rather than invent an imported ancestor id. Searches of the whole imported blueprint for predeformation, Artinian local, groupoid, square-zero and pseudofunctor found no duplicate of this definition. No chapter or unit record changed.

## Unfinished work

None in this stage-1 definition split. No Lean was written or compiled. No assertion of existence of versal objects, effectivity, (RS), or tangent-vector-space laws has been inserted as a definition.

## Not duplicates

No new nodes. Existing `def-sc-trivial-square-zero-extension` was reused instead of creating a duplicate. Existing `def-weil-finite-dimensional-subspace` and `lem-weil-pbc-artinian-local-noetherian-nilpotent` were also reused. Curve-specific marked-deformation and stable-moduli-groupoid definitions concern different base categories and are not replacements for general Artinian tests.

## Review by Q94

I read formal-defos.tex at 06GC/06GD for objects, residue-field markings, morphisms and small extensions; 06GJ and remarks-cofibered-groupoids for covariant pushforwards and their coherence; 06GS for the terminal fibre at k; 06J2 and lemma-RS-2-categorical for the stated 2-fibre-product formulation of (RS); 06SR and 06IG for square-zero test rings and the tangent set; 06GW, 06H3, 06H5 and 06HC for completed rings, compatible systems and evaluation; and 06HR/06HS for versality with its prescribed isomorphism. I also read artin.tex around 07T4, including the choice of finite affine neighbourhood and the factorization category, to check the general finite-type-field convention.

There are no proof steps in this definition. I opened all eight statement dependencies and checked their actual statements: Noetherian and field definitions give the opening hypotheses; finite type is the scheme-morphism convention applied to Spec(k) -> Spec(R); the size convention gives the universe bound; completion defines the canonical inverse-limit map; finite-dimensionality gives the finite spanning condition on V; the square-zero node gives exactly the displayed multiplication and constants; Artinian nilpotence gives exactly the positive N used for evaluation. The latter is already a Mathlib leaf, so no off-unit proof-route replacement occurs. The comparisons between evaluations are the specified transition maps whiskered with transport, not a lemma about independence of arbitrary filtrations (the latter is already a separate node, and is not used here).

I checked small cases. A=k has N=1 and evaluation is the transport of xi_1. For V=0 the ring k[V] is k; for V=k it is the dual-number ring. The identity is not a small extension, since its kernel has dimension zero; k[epsilon] -> k is small. For B=k[t]/(t^3) -> A=k[t]/(t^2), the kernel (t^2) is killed by m_B and one-dimensional. The zero ring is excluded by having exactly one maximal ideal and by the residue-field marking. For C=k[[t]], every local map to an Artinian target kills m_C^N because it maps m_C into m_A; no extra continuity assumption has been slipped in. Two higher truncations compare through their common higher level using the transition composites, whose associativity is part of the specified data. The terminal-groupoid condition is stronger than having just one isomorphism class: it excludes nontrivial automorphisms at k, as required.

Against delivery-errors B, the sole edited node is self-contained, source labels and tags were checked in the tag table, and no search was fabricated. Against C, no dependency is used for a fact it does not state, and no proof is accessed through a citation. Against D, this is a definition split by naming existing constituent notions and writing its data explicitly; nothing is moved into a new copy of an item clause. Against E, residue markings, ring-map direction, positive powers and the specified isomorphism in versality were checked. No non-elementary proof step exists, so no long proof step hides a lemma. The source document and every original field not requiring this split, including inherited searches, created provenance and blueprint ancestry, are preserved.
