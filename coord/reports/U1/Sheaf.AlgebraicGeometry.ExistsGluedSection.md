## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.Modules.existsGluedSection` with a
complete proof from explicit local Čech data and the existing transition-cocycle
module gluing theorem. The signature and public imports are unchanged.

Added two modules:

- `Sheaf.AlgebraicGeometry.NormalizedComponentSectionCover`: the geometric
  preparation from Stacks 09NE, asserting an open cover, component free frames,
  scalar expressions for the prescribed sections, and structure-section bijections
  on distinct overlaps. It has the delivery's only new hole.
- `Sheaf.AlgebraicGeometry.ComponentSectionCechData`: fully proves unit descent,
  identity/inverse/cocycle equations, frame-transition equations and compatibility
  of the scalar expressions from that normalized cover. No global module or
  section is asserted here.

The target constructs the invertible module using the existing Čech gluing theorem,
proves compatibility of the local multiples of its frames, and applies Mathlib's
sheaf gluing theorem to obtain the global section. Two proved private helpers
construct frame-preserving isomorphisms from matching transition functions.
The existing pullback-free-generator theorem and the unit identity for uniqueness
of left adjoints identify the component restrictions with the specified canonical
tensor-pullback unit. Local equality implies equality of global sections.

All three modules compile together in import order with lcompile.py, without warnings.
No existing statement, definition or visibility changed. No forced adaptation or
change record is needed.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.existsGluedSection` (node
`lem-sc-exists-glued-section`), 1 of 1 holes in the assigned module.

New and fully proved:
`AlgebraicGeometry.Scheme.Modules.exists_component_section_cech_data`
(node `lem-sc-component-section-cech-data`). Its unit ratios are constructed by
lifting their values and inverse values, then proving their product is 1.
Its private helpers prove restriction naturality and all cocycle/coefficient checks.

Added hole:
`AlgebraicGeometry.Scheme.Modules.exists_normalized_component_section_cover`
(node `lem-sc-normalized-component-section-cover`), exactly `:= by sorry`.
It is strictly the geometric local preparation: it asserts no transition units,
cocycle, glued module, or global section. This is a decomposition: one upper hole
closed and one lower hole added, not a net decrease in holes. No private helper has
a hole. The existing dependency
`AlgebraicGeometry.exists_invertible_of_cech_transition` remains unproved and is used
as intended; its module is unchanged.

Edge cases checked: an empty component index forces Y empty; the empty cover is
permitted on empty Y. Empty component preimages admit the unique vacuous free
generator. Empty intersection locus needs only disjoint component opens. Diagonal
transitions are explicitly 1, rather than inferred through a section comparison that
need not be injective on neighborhoods of intersection points. Every triple with
unequal indices uses an unequal pair to obtain injectivity; an all-equal triple is
proved directly from the identity transition. No reducedness hypothesis on the
component schemes is added.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.GlueComponentReducedCoverSections`
from the assigned module. Its node `lem-sc-glue-component-reduced-cover-sections` is
now needed only by the normalized-cover construction and remains imported there.
It is not pruned from the transitive closure.

No node or module is globally pruned. The transition-cocycle module remains needed.
`ExistsGluedInvertible` and `GlueComponentLineBundles` are not used as dependencies;
the latter depends on this theorem, so importing it would create a cycle.
All original public imports are retained because the statement needs them.

## Where the brief, the DAG or earlier work was wrong

The original node's single proof step combined geometric local normalization and
final assembly, but its two stated dependencies do not provide the normalized
frames or their common scalar expressions. The normalized-cover node states this
missing geometric preparation. The transition and coefficient algebra is now fully
proved, as are the global module/section assembly and component comparisons.

The supplied node has a broken blueprint ancestry (`blueprint.from.node = null`);
`tools/blueprint_refs.py ancestor lem-sc-exists-glued-section` confirms this. The new
nodes record the actual item's proof sentences and Stacks source, without inventing
an ancestor. Searches for 09NE, glue invertible, normalized, transition, discrete
intersections and free generator found no matching imported statement for either
new lemma.

The Stacks source is absent from this clone's literature directory; read the existing
local Stacks copy at `/home/ubuntu/c1-stacks-review/varieties.tex`, lines 7990–8067,
label `lemma-glue-invertible-sheaves`. This agrees with the node's cited source.
LeanSearch returned HTTP 500 and is recorded as unavailable. Separate LeanFinder
and Mathlib grep searches for both new lemmas returned general cover and section
lemmas, but no normalized closed-component frame-cover construction.

The next worker can use the existing, proved
`mem_nonvanishingLocus_iff_generatesAt` in `NonvanishingGeneratingLocus` to obtain the
normalized local frames, and Mathlib `IsDiscrete.iUnion` in `Topology.DiscreteSubset`
to prove discreteness of the finite closed intersection union. Both have been read;
these observations are recorded in the cover node's proof plan. The present delivery
already handles the remaining unit, cocycle, section and pullback algebra.

## New nodes

`lem-sc-normalized-component-section-cover`, in
`dag/nodes/sec-curve-estimates/lem-sc-normalized-component-section-cover.json`, with
module `Sheaf.AlgebraicGeometry.NormalizedComponentSectionCover`. This is the
geometric cover and normalized-frame construction from Stacks 09NE, before any
transition function is chosen. Its docstring and node carry the full source proof.
It contains the delivery's one new hole.

`lem-sc-component-section-cech-data`, in
`dag/nodes/sec-curve-estimates/lem-sc-component-section-cech-data.json`, with module
`Sheaf.AlgebraicGeometry.ComponentSectionCechData`. This proved theorem constructs
component-compatible transition units and scalar Čech data from the normalized
cover. No change record is required.

## Second reading by U1

1. Compared `ExistsGluedSection.lean` with the repository version. The target
   signature and all existing declarations are byte-for-byte unchanged; only the
   proof and proof-only imports changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. The target proof
   has no `sorry`; the only remaining hole is the explicitly named normalized-cover
   theorem, with its matching node and complete source docstring. No forbidden
   declarations occur. Verdict: pass.
3. Reviewed both split statements and searched the library and recorded Mathlib
   searches. The normalized-cover statement is a strict geometric prerequisite,
   while the Cech-data statement is a strict algebraic intermediate; neither
   restates the target or weakens it. Edge cases (empty index/cover and diagonal
   transitions) are addressed in the report and proof. Verdict: pass.
4. Checked the proof route and imports. The proof uses the Cech-data theorem,
   transition gluing theorem, pullback free-generator result, and sheaf gluing;
   the former direct gluing import was removed. The unit route and all realized
   steps remain represented in the DAG. Verdict: pass.
5. Checked DAG `proof`, `proof_deps`, and `proof_origin` against the Lean proof,
   and checked the new node metadata, docstrings, and report sections. Verdict:
   pass.

Changed only the report by adding this second-reading record; no Lean repair was
needed after compilation.
