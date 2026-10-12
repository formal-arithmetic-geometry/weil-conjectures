## What changed

Replaced the hole in `finiteSurjectiveSetDescent_compatible_locally_lifts` by a
compiled reduction to geometric stalk preimages and a proved private helper
`imageSieve_mem_of_geometric_germ_lifts`. The helper constructs geometric points
using algebraic closures, represents stalk preimages, realizes germ equality on
pointed refinements, uses naturality, and proves the refinement family covers.
Added the proof-only import of `FiniteSurjectiveSetDescentGermLifts` and the
algebraic closure import. The target signature is unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.finiteSurjectiveSetDescent_compatible_locally_lifts`
(node `lem-weil-pbc-sets-finite-descent-local-lifts`).
The private helper is proved without holes.

Added one hole:
`AlgebraicGeometry.finiteSurjectiveSetDescent_compatible_germ_lifts`
(node `lem-weil-pbc-sets-finite-descent-germ-lifts`). This is a decomposition:
one hole closed and one added, net zero. The lower statement concerns only the
stalk image; the representation/refinement/naturality/covering argument is proved.
No sorry remains in the item's module and no definition contains a sorry.
Both modules compile with no warnings through lcompile.py.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`,
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageStalkGerm`,
`Sheaf.AlgebraicGeometry.FinitePushforwardSetStalk`, and
`WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber` from the item.
The finite-stalk dependencies now belong to the new germ node's proof plan.
The following old direct proof dependencies are no longer used directly by the
local-lifts proof: `def-pc-fibre-product`, `def-weil-pbc-category-colimit`,
`def-weil-surjective-morphism`, `lem-weil-pbc-finite-composition`,
`lem-weil-pbc-finite-geometric-point-lift`, `lem-weil-pbc-finite-morphism-permanence`,
`lem-weil-pbc-sets-etale-inverse-image-composition-units`,
`lem-weil-pbc-sets-etale-inverse-image-stalk-germ`, and
`lem-weil-pbc-sets-finite-pushforward-stalk`; they move into the germ node.
`def-weil-pbc-etale-sheaf-of-sets` remains a statement dependency, but is no
longer a separate proof dependency: the cover proof uses the site axioms directly.
No module or node is claimed globally pruned. The elementary filtered-colimit
argument uses Mathlib directly through Point.toPresheafFiber_jointly_surjective,
Point.toPresheafFiber_eq_iff', and germ naturality. No separate new lemma for the
covering step is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The module did not directly import most of its DAG
proof dependencies; their signatures were inspected. A further reduction to
coordinate propagation was attempted, but rewriting the unit stalk map through
colimit.pre ran into transparency/elaboration difficulties. That attempt is not
part of the delivery. The compiled final reduction leaves the full stalk portion
as a sourced theorem strictly below the local lifting statement. Empty X makes
the new assertion vacuous and the proved cover argument uses the empty cover;
empty sheaf stalks create no false inhabitedness assumption.

The cited Stacks source file is absent in this checkout. The second reader checked the official pages
https://stacks.math.columbia.edu/tag/09Z2 and
https://stacks.math.columbia.edu/tag/09Z3 to confirm the cited diagonal argument.
The unit sk-thm-iff is not bypassed: this is a split below its realizing node.

## New nodes

`lem-weil-pbc-sets-finite-descent-germ-lifts` in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-sets-finite-descent-germ-lifts.json`
records original proof steps 1–9, with finite lift sets, the product stalk maps,
the diagonal unit, and compatibility of comparison maps. Its module is
`Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentGermLifts`. Its docstring gives
the full proof in words. No change record is required: existing public signatures
and definitions are unchanged, and new imports in the item are proof-only.

## Second reading by H3

1. PASS: Diffed the existing module and node against the repository and checked
   the original theorem signature byte for byte with a string comparison. No
   existing public declaration or definition changes. Both retained public
   imports supply names in the statement; new imports are proof-only.

2. PASS: Both modules compile cleanly through `lcompile.py --all`. A scratch
   `#print axioms` confirms the private covering helper uses only `propext`,
   `Classical.choice`, and `Quot.sound`. The item theorem additionally uses
   `sorryAx` through the named germ-lifts split. No forbidden declaration, hollow
   definition, or anonymous hole occurs. The split theorem is the only new hole.

3. PASS: Read the split's signature, docstring, node, finite-pushforward stalk
   theorem, inverse-image stalk/germ theorem, and composition-unit theorem.
   Checked Stacks 09Z2 and 09Z3: the product/diagonal equalizer calculation is the
   cited set-valued argument. With one lift compatibility is automatic and the
   unit stalk map is bijective; with two lifts compatibility equates both
   coordinates; empty stalks cannot produce a compatible section; empty X has
   no geometric points. This split removes the entire representation/refinement/
   covering argument, so it is strictly a part of the original proof, not a
   renamed local-lifting assertion. Independent searches using geometric-fiber
   equalizers, diagonal images, and stalk surjectivity found no duplicate in
   Mathlib or the source library; Loogle did not recognize the queried identifier.
   The remaining stalk calculation requires more than a short repair.

4. PASS: Read the helper from germ representation through pointed refinement,
   naturality, and joint coverage. It uses Mathlib directly and handles the empty
   cover without inhabitedness assumptions. The old imports and old direct node
   dependencies removed are now explicitly listed above. No module is globally
   pruned; the germ node retains the finite-stalk proof plan. The `sk-thm-iff`
   realized nodes and its chapter route are unchanged.

5. PASS: The existing node changes only proof, proof_deps, and proof_origin.
   Their dependencies equal the union of proof-step uses. The new node includes
   source, creation, searches, ancestry, and the matching Lean record. Its
   statement is now recorded verbatim. The retained proof plan is for the open
   stalk theorem, while the local node records the compiled two-step reduction.

Changes by the second reader: corrected the incomplete import/pruning report;
recorded the new Lean signature verbatim; checked the cited source and corrected
its report wording. No Lean proof or public signature required repair. This
remains one original hole closed and one strictly lower hole added, net zero.
