# Stage 1 worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-pbc-proper-open-comparison-composition.json`: existing six-step statement split, marked `split`; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotes for all cited nodes in all six proof steps.
- `report.md`: this report.

## Attachments

None. I searched both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the slopmaster2 source for the item id, blueprint tag, comparison-map terminology, and the declaration names recorded in the DAG; no sorry-free declaration states this item exactly. The source trees contain no finished attachment for the item.

## WANTED

None. The local Stacks and blueprint files cited by the item were available. No literature was downloaded or written.

## What was checked or corrected

The sandbox initially had no node, so I copied the current repository node and retained its statement, six proof steps, dependencies, blueprint metadata, Mathlib search records, import flags, and existing review metadata. The current node already contains the expanded injective-representative proof and no new child node is required. I changed only its stage-1 status from `unsplit` to `split` and regenerated `citations.json` from the current dependency statements.

The item is not a Mathlib theorem: the recorded grep, LeanFinder, Loogle, and LeanSearch searches found only generic sheaf/direct-image or adjunction declarations, with no proper-open comparison composition law. I read those recorded results before reusing them. The blueprint place is the imported node itself (order 1483), and the proof follows the blueprint's open-restriction, clopen-component, composition, adjunction, and identity clauses. No statement correction or source error was found.

## Not duplicates

No new nodes were created, so there are no new-node duplicate pairs. The item itself is the existing blueprint node; searches of the DAG and both blueprint snapshots found no alternate node stating the same proper-open comparison composition and identity theorem.

## Review by Q127

I read the item node, `sec-smooth-purity.json`, and `sk-def-sf-operations.json`, together with the source locations recorded in all six proof steps. The statement keeps the hypotheses exactly: proper maps `u` and `v`, open immersions of the common `X`, the two compatibility equations, finite constant coefficient ring, bounded-below etale derived input, the canonical derived pushforward composition, and both the composition and identity conclusions. The item is in etale module categories with constant coefficients as required by its comparison definition; no structure-sheaf or pro-etale interpretation was introduced.

Step 1 constructs the natural restriction map `t_{w,L}` on a bounded-below injective representative. I checked the cited statements individually: proper composition supplies properness of `vu`; the injective-representative node supplies `I`; the direct-image definition supplies `w_*I`; open immersion etaleness and the inverse-image restriction proposition supply the sectionwise restriction; inverse-image exactness supplies termwise derived restriction; and the K-injective Hom node supplies independence of representatives and naturality. The displayed fibre-product map `delta_w(W)` is the actual section map, and the scalar-linearity check is written out.

Step 2 specializes to `L=j_{a!}K`. The proper-open-section statement supplies the open-and-closed section, etale restriction of injectives supplies the representative, derived open restriction supplies the sectionwise identification, clopen-section direct image supplies restriction to the distinguished component, and proper-open-identification states that this composite is the specified `theta`. I checked that the argument uses the statements of those nodes rather than an unrecorded formula from their proofs, and that no termwise vanishing on the complementary component is assumed.

Step 3 computes the composite maps on one injective `I`. Direct image preserves injectives, the direct-image definition computes both derived pushforwards, module-linear inverse-image composition supplies the fibre-product associator, and the right-derived-plus-injective node identifies this with the canonical derived composition. The two section maps compose to `delta_{vu}` using `u j_1=j_2` and `v j_2=j_3`, so the claimed equation for `t` follows degree by degree.

Step 4 uses the derived adjunction in the comparison definition, the open-square extension-by-zero base-change corollary, and the explicit extension-by-zero transpose formula. I checked that `j^{-1}j_!K` is identified with `K`, the unit is the identity under this identification, and the adjunction bijection detects equality after restriction. This is the only elementary step because it is a direct transpose calculation from the cited formulas.

Step 5 sets `A=j_{1!}K` and expands naturality of `t_v`. The cited comparison definition supplies the defining transpose equation for both `alpha_{vu,K}` and the composite `beta`; Steps 2–4 supply the displayed cancellation. Since `theta_{vu,K}` is invertible, injectivity of the same adjunction bijection gives equality. The algebraic cancellation and use of the already established equations are elementary once the cited comparison definition is in place.

Step 6 specializes the restriction map to the identity morphism. The fibre-product section is the canonical identity, Step 2 gives `theta=id`, and the comparison definition plus the adjunction unit identifies the comparison with the identity map. I checked the identity and empty/zero-input cases: the restriction formulas reduce to identity maps, and zero complexes give the unique zero morphisms. Every `uses` entry has a literal quote in `citations.json`; `proof_deps` is the union of the step uses. No Lean, compiler, Lake, build, or direct git command was run, and no file outside this sandbox was modified.

No new node is left unfinished. The existing dependency nodes remain the route's generic tools, and no tool-use declaration or statement change is needed for this delivery.
