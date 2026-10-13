## What changed

Proved `AlgebraicGeometry.exists_etale_generic_residue_field_model` in
`Sheaf.AlgebraicGeometry.EtaleGenericResidueFieldModel`, with its signature and
public imports unchanged. Added two proof-only imports:
`Sheaf.AlgebraicGeometry.EtaleNeighbourhoodPrescribedResidueField` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`.

Use the existing prescribed-residue-field neighbourhood, isolate its chosen point
in the discrete generic fibre by an open restriction, and prove genericity using
openness and inverse image of closure. Compose the open immersion's residue-field
isomorphism with the prescribed isomorphism and check the exact morphism equation.
Updated the node's proof, proof dependencies and proof origin to this route.
No definitions, statements, attributes, instances or visibility changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_etale_generic_residue_field_model`
(node `lem-sbc-etale-generic-residue-field-model`).
No holes remain and no holes were added; this is a full proof, not a decomposition.
Local compilation is clean. An explicit `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.
The nonreduced case uses only irreducibility and the open-map closure identity;
the degree-one extension is covered by the same construction.

## No longer needed

No pre-existing import was removed. The direct planned dependency
`lem-weil-pbc-etale-residue-polynomial-lift`, module
`Sheaf.AlgebraicGeometry.EtaleResiduePolynomialLift`, is no longer needed by this
proof and is not imported. The direct planned primitive-element dependency
`lem-weil-pbc-finite-separable-primitive-element` is replaced by the already proved
prescribed-residue-field neighbourhood; primitive elements still occur inside
that closed tool's proof, so this does not claim global elimination of that tool.
The explicit finite monic quotient, finite-map closed-image shrinking, and
flat-going-down construction in the old plan are unnecessary here.

Second reading removed the provisional DAG dependency
`lem-weil-pbc-etale-morphism-open-map`: its node has no Lean declaration and
the proof obtains openness from closed Mathlib instances directly.

Temporary imports of `WeilConjectures.Mathlib.RingTheory.Etale.Field` and
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` were removed after checking
that the two remaining proof imports expose the required tools. No new module
or node is delivered. Pruning claims refer to this item's route, not to global
unreachability from all targets.

## Where the brief, the DAG or earlier work was wrong

The old plan had no named dependencies for its substantial geometric shrinking
and genericity steps. They can be avoided entirely: discrete fibres let us
isolate the chosen point, and openness makes it generic. The node has been
updated accordingly. The existing docstring records the alternative monic
construction; the delivered proof uses the shorter route described above.
The unit `sk-prop-normal-form` has empty realized lists and this argument uses
closed tools; none of its fixed statement or proof steps was changed.

## Second reading by V2

1. **Interface unchanged: pass.** Read the complete repository/sandbox module diff.
   The sole existing declaration, `AlgebraicGeometry.exists_etale_generic_residue_field_model`,
   has its signature byte for byte unchanged, including both morphism hypotheses, universes,
   genericity, image equality and the prescribed morphism equation. Public imports, attributes,
   namespace, visibility and definitions are unchanged. Only two plain proof imports and the
   proof body were added; no change record or forced adaptation is required.

2. **Proof and axioms: pass.** Compiled the delivered file through `lcompile.py`: clean,
   about three seconds. Compiled a scratch copy ending in `#print axioms` for the theorem:
   exactly `propext`, `Classical.choice`, `Quot.sound`. No remaining or added holes,
   prohibited declarations or hollow definitions. The algebra structure is explicitly
   `(Spec.preimage yη).hom.toAlgebra`; the chosen neighbourhood comes from a proved theorem,
   and the open subscheme and both field isomorphisms are explicit constructions.
   In `hfields`, the equation `he` is transported through the open immersion residue-field
   map, with the base-point equality handled by `residueFieldCongr`; the final Spec
   naturality calculation proves the exact requested equation.

3. **Split statements and searches: pass.** None were split off, and no new declarations or
   nodes are delivered. Read the existing prescribed-residue-field theorem and its proof,
   whose compatibility clause is essential here. Independently searched via `msearch.py`
   LeanFinder for an open etale neighbourhood realizing a specified generic residue field
   extension, and grep for `IsGenericPoint.*Etale|etale.*generic|exists.*residueField`.
   The eight LeanFinder and fourteen Mathlib grep hits provide ring-level/local tools,
   not this scheme statement. Read the existing `EtaleGenericIrreducibleNeighbourhood`: its
   Noetherian hypotheses prevent using it here. Checked the degree-one case and an
   irreducible nonreduced base: the fibre isolation and open-map closure argument use
   neither reducedness, Noetherianity nor a nontrivial extension degree.

4. **Route, imports and pruning: pass.** Read Stacks
   [0551](https://stacks.math.columbia.edu/tag/0551) for the original monic route,
   [02LF](https://stacks.math.columbia.edu/tag/02LF) for prescribed neighbourhoods,
   [02GL](https://stacks.math.columbia.edu/tag/02GL) for discrete etale fibres, and
   [03WT](https://stacks.math.columbia.edu/tag/03WT) for openness.
   The replacement route uses an already closed neighbourhood tool, isolates its point
   by an ambient open, and identifies the closure of its singleton with all of the
   restriction. Both new proof imports are needed: removing the neighbourhood import
   in a scratch copy loses `exists_etale_neighbourhood_prescribed_residueField`; removing
   QuasiFinite loses `isDiscrete_preimage_singleton`. The three public imports serve the
   existing signature. Both old `proof_deps` (primitive element and residue polynomial
   lift) are reported under No longer needed, with the stated transitive-use caveat.
   Read `dag/units/sk-prop-normal-form.json`: its statement and two steps have empty
   realized lists; this auxiliary argument changes none of that fixed route.

5. **DAG agrees with Lean: repaired, then pass.** Compared the complete node diff: changes
   are confined to `proof`, `proof_deps`, `proof_origin`. Steps match the induced algebra,
   neighbourhood, discrete-fibre restriction, openness/closure, and field-map calculation.
   The first worker cited `lem-weil-pbc-etale-morphism-open-map`, whose node has no Lean
   declaration. The code instead uses the closed Mathlib `UniversallyOpen.of_flat`
   instance (etale implies flat and locally of finite presentation) and
   `Scheme.Hom.isOpenMap`. Removed that misleading dependency and named these actual
   tools in the proof step and proof origin. The dependency list is the union of the
   revised steps. No new-node requirements apply.

Second reading changed only the DAG openness dependency/explanation and this report.
The Lean proof was read and retained unchanged. Closed one original hole, added zero:
`AlgebraicGeometry.exists_etale_generic_residue_field_model` is fully proved.
