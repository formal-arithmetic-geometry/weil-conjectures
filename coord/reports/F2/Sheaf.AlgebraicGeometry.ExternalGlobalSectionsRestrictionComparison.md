## What changed

Replaced the sorry in `exists_externalSectionsRestrictionComparison` without changing its
signature, definitions or existing public import. Its proof-only import is the new
`Sheaf.AlgebraicGeometry.ExternalSectionsOpenComparison` module.

`Sheaf.AlgebraicGeometry.ExternalSectionsComponents` constructs the section maps explicitly:
`scalarUnitSection`, `scalarPullbackGlobalSection`, `externalSectionsBilinear`, and
`externalSectionsComponent`. The scalar structure-map identity `scalarMap_pullback` and
`externalSectionsComponent_naturality` are proved. The naturality argument compares pure
tensors using composition of restrictions, naturality of the adjunction unit, and
`tmulSection_map`. No new data is chosen from an unproved existence theorem.

The original module constructs a natural transformation from this family, proves its
top-open normalization by tensor extensionality and identity restriction, and uses the
single-open comparison to finish the local clause. The remaining geometric comparison
is isolated in `Sheaf.AlgebraicGeometry.ExternalSectionsOpenComparison`.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.exists_externalSectionsRestrictionComparison`
(node `lem-sc-external-global-sections-restriction-comparison`). There are no sorries left
in the item's module or in `ExternalSectionsComponents`.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.externalSectionsComponent_openComparison`
(node `lem-sc-external-sections-open-comparison`). Its proof is exactly `by sorry`.
It concerns one explicitly constructed component and its identification on an open
subscheme; it does not assert existence or naturality of a presheaf morphism or its
top normalization. The docstring and node give the complete adjunction-comparison argument.

This is a decomposition: one original hole closed and one strictly smaller hole added,
for net zero holes. The component construction, scalar-linearity checks, naturality,
normalization and assembly are actual Lean proofs.

## No longer needed

No imports removed and no modules pruned. The original statement import remains necessary.
The original node's direct proof dependencies are replaced by the component/naturality node,
the single-open comparison node, and `def-sc-scalar-global-sections-comparison`.
Its previous field-linear operations dependency is used in the component construction.
The previous open-immersion, composite-adjunction, conjugate-unit and module-pullback-tensor
nodes remain needed in the single-open comparison, so none is claimed as globally pruned.
No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The planned dependencies supply individual
comparison tools, not the assembled external section morphism. Searches found no existing
assembled result. LeanSearch returned an internal-server error, recorded as unavailable;
LeanFinder, Loogle and Mathlib grep found section/tensor/restriction tools.

The source read was Stacks Tag 0BED (the degree-zero construction and the omitted
canonical-map verification), with the restriction argument expanded using the existing
Tags 0096, 0097 and 01CD nodes. The new local statement requires neither affineness nor
quasi-coherence: restriction and pullback comparisons work for arbitrary module sheaves.
The empty open and zero modules are included; all section comparisons remain isomorphisms.

## New nodes

`lem-sc-external-sections-components`: explicitly constructed component family and its
restriction naturality, fully proved in `ExternalSectionsComponents`. It serves the first
step of the original node; its data is given by actual adjunction units and TensorProduct.lift.

`lem-sc-external-sections-open-comparison`: the source/target identification of a single
explicit component with the canonical external tensor map on X times V. This is the one
remaining sorry, serving the second step of the original node. It uses the original
open-immersion, adjunction-composition, unit-equation and tensor-pullback tools.

Both inherit the original chapter and unit, carry the blueprint provenance and actual
search records, and have no statement change to any existing node. No change record or
forced consumer adaptation is needed.

## Second reading by F2

1. **Existing interfaces — pass.** I compared the delivered
   `ExternalGlobalSectionsRestrictionComparison.lean` with the repository copy using
   `diff -u`. The signatures of `externalSectionsPushforward`, `externalSectionsTopIso`,
   and `exists_externalSectionsRestrictionComparison`, and both existing definition
   bodies, are byte-for-byte unchanged. The additions are a plain proof import, a local
   elaboration option, and the theorem proof. There are no forced adaptations or
   statement changes.
2. **Proof and data — pass.** All three delivered modules compiled individually in
   dependency order through `lcompile.py`, without errors or warnings. The only textual
   hole is `externalSectionsComponent_openComparison`, whose whole proof is `by sorry`.
   No forbidden declaration or hollow definition occurs. I inspected
   `exists_tensorPullbackAdjunction`: its statement specifies the unit sectionwise as
   the sheafified tensor `1 tensor eta(m)`, and its current proof constructs the
   adjunction. Thus `scalarUnitSection` uses determined unit data, rather than an
   arbitrary unproved witness. The new linear maps use this unit, actual restrictions,
   and `TensorProduct.lift`. The axiom check is recorded below.
3. **Split statement — pass as a decomposition.** I read the complete local comparison
   signature and its docstring against Stacks Tags [0BED](https://stacks.math.columbia.edu/tag/0BED)
   and [01CD](https://stacks.math.columbia.edu/tag/01CD), and the upstream restriction,
   adjunction-unit and composition comparison declarations. The source and target are
   the actual sections on the base-changed open, not an asserted bijectivity of the
   external section map. For `V = top` the comparisons reduce to identity transports;
   for `V = bottom` both section modules are zero and the square is the zero map.
   Zero F or G likewise gives zero tensors on both sides. The argument requires no
   quasi-coherence or affine hypothesis: these would be needed for a Kunneth
   isomorphism, whereas this statement only transports the same section map.
   This is strictly the local clause for an already constructed component; naturality,
   normalization and existence of the presheaf morphism are separately proved.
   Independent LeanFinder search for base change along an open immersion returned
   `restrict_map`, `restrict_obj`, `restrictAdjunction_unit_app_app` and
   `restrictFunctorIsoPullback`. Loogle confirmed the last isomorphism concerns
   Mathlib's `pullback`, not directly `tensorPullback`. Grep for
   `leftAdjointUniq.*unit|tensorPullback.*restrict|pullback.*tensor.*section` found
   adjunction uniqueness unit equations. Searches of `lean/Sheaf` and the upstream
   module files found no assembled comparison. The remaining geometric construction
   is not a short application of one of these results, so I left its named hole.
4. **Route and pruning — pass.** The original proof builds c from the explicit family,
   proves top normalization on pure tensors using identity restriction, and invokes
   only the local comparison for the remaining clause. All three imports are necessary
   for their respective definitions or signatures, except the original module's new
   import, which is correctly proof-only. The old direct proof dependencies no longer
   used directly by the assembled proof are:
   `def-sc-field-linear-module-cohomology-operations`,
   `def-weil-pbc-composite-adjunction`,
   `lem-weil-pbc-conjugate-iso-unit-equation`,
   `lem-weil-pbc-module-pullback-tensor`, and
   `lem-weil-pbc-open-immersion-module-pullback-restriction`.
   The first is used by the components; the other four remain in the local comparison's
   proof plan. None is globally pruned. The original scalar comparison dependency
   remains direct. I read the statement and step embedded in `dag/units/sk-prop-av-cube.json`:
   this refinement changes no unit statement, step or realized entry, and bypasses no
   realized node.
5. **DAG agreement — pass.** The original node now records assembly, pure-tensor top
   normalization and the local clause, matching the Lean proof; its proof dependency
   set is the union of those steps' uses. The component node records scalar compatibility,
   explicit bilinear construction and restriction naturality. The open-comparison node
   records the remaining restriction/pullback/tensor/unit argument. Their recorded Lean
   statements match the declarations; chapter, unit, provenance, source, search records,
   creation fields and module paths are present. Each new node belongs to this item.

Second reading changed the report only: added these explicit review findings and the
complete list of former direct proof dependencies. No Lean proof repair was needed.

The scratch `#print axioms` check passed: `scalarMap_pullback`, `scalarUnitSection`,
`scalarPullbackGlobalSection`, `externalSectionsBilinear`, `externalSectionsComponent`
and `externalSectionsComponent_naturality` use only `propext`, `Classical.choice` and
`Quot.sound`. The original existence theorem and `externalSectionsComponent_openComparison`
also use `sorryAx`, as expected from the one remaining named local comparison hole.
