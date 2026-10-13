## What changed

`Sheaf.AlgebraicGeometry.FlatFibreDimensionStrataCore` now proves
`AlgebraicGeometry.exists_fibre_dimension_opens_of_flat_restrict` from one strictly
smaller local-neighbourhood theorem. Its signature and public imports are unchanged.
The new imports are proof-only: `Mathlib.AlgebraicGeometry.Properties` and
`Sheaf.AlgebraicGeometry.FlatFibreDimensionNearZeroDimensionalStalk`.

The family is explicitly constructed as the interiors of the dimension level sets
intersected with the inverse image of U. A proved private helper identifies the fibre
stalk dimension at a component generic point as zero, using maximality of its
irreducible closure and Mathlib's stalk-dimension/coheight equality. The proof then
transports the point through `fiberHomeo`/`asFiber`, applies the neighbourhood theorem,
and uses inclusion in the interior and density of generic points. No object is
chosen by a public definition from an unproved existence theorem.

Compiled both delivered modules together through `lcompile.py --all`; no errors or
warnings. The DAG copy records the actual proof and its dependencies.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_fibre_dimension_opens_of_flat_restrict`
(node `lem-sbc-flat-fibre-dimension-strata-core`). Its body contains no sorry.
The private helper `ringKrullDim_stalk_eq_zero_of_generic` is fully proved.

Added one hole:
`AlgebraicGeometry.exists_constant_fibre_dimension_neighbourhood_of_stalk_dimension_zero`
(node `lem-sbc-flat-fibre-dimension-near-zero-dimensional-stalk`, module
`Sheaf.AlgebraicGeometry.FlatFibreDimensionNearZeroDimensionalStalk`). Its proof is
exactly `by sorry`. This is a decomposition, closing one hole and adding one;
it is not a sorry-free proof of the original theorem. The remaining theorem concerns
one point satisfying a dimension-zero stalk hypothesis and supplies one constant-
dimension neighbourhood. It asserts neither fibrewise density nor a global family.

## No longer needed

No original import or original proof-dependency node was removed: the input node
had no proof dependencies and the module had only statement imports. No existing
module is claimed globally unreachable. The density part of Tag 045U and the
existence of a global enumeration of all Cohen-Macaulay dimension pieces are not
needed as additional theorem interfaces: density follows from Mathlib generic
points and the family is constructed using interiors. Only the local openness and
relative-dimension decomposition arguments of Tags 045U/02NM remain in the new item.
No separate Cohen-Macaulay-locus definition, depth module, dense-locus existence
lemma, or arbitrary chosen family is added or imported.

## Where the brief, the DAG or earlier work was wrong

The original node was marked split but had one non-elementary prose step with no
proof dependencies; there were no stated lemmas corresponding to its cited
Cohen-Macaulay arguments. The replacement records a local-neighbourhood interface
and proves all of the density and assembly argument in Lean.

The ring dimension of a generic fibre stalk is zero even when local topological
fibre dimension is positive. They must not be identified: the generic point of an
affine line has ring dimension zero and local topological dimension one. The new
statement deliberately allows any n. Its hypotheses cover nilpotent generic
stalks (zero-dimensional Noetherian local rings are still Cohen-Macaulay), and
empty fibres, empty schemes, and U empty introduce no nonemptiness assumptions.
No target signature, existing definition, other module, or unit route changed.

LeanSearch returned Internal Server Error, recorded as unavailable. LeanFinder
and source grep ran and found no matching local-neighbourhood theorem. The smooth
relative-dimension constancy theorem in the source library requires smoothness
and does not apply to a general flat locally finitely presented morphism.
The blueprint searches for 045U, 02NM and Cohen-Macaulay found no duplicate; broader
fibre-dimension and zero-dimensional searches found only different statements.

## New nodes

`lem-sbc-flat-fibre-dimension-near-zero-dimensional-stalk` states the local part of
Tag 054T, obtained by combining the open Cohen-Macaulay locus (045U), its
pure-relative-dimension decomposition (02NM), and fibre-open dimension invariance.
Its docstring and node explain the restriction/fibre-stalk identifications,
zero-dimensional Cohen-Macaulayness, neighbourhood construction, and local
(topological) dimension comparison. It inherits chapter, unit and blueprint
ancestor from the original node. There are no change records or forced adaptations.

## Second reading by M1

1. **Interface: pass.** Compared both delivered modules with the repository.
   The original theorem signature is byte-for-byte identical, as are its public
   imports and visibility. The only other module is new; no existing definition
   or target changed. No change record or forced adaptation is needed.
2. **Proof: pass as a decomposition.** Compiled both modules in import order
   through lcompile.py, without errors or warnings. Inspected every declaration:
   one named theorem has exactly `by sorry`; no data definitions, hidden holes,
   forbidden axioms, unsafe declarations or implementation overrides were added.
   A scratch copy with #print axioms showed propext, Classical.choice and
   Quot.sound for ringKrullDim_stalk_eq_zero_of_generic. The original theorem
   and the new neighbourhood theorem additionally use sorryAx, as reported.
   The scratch copy was removed. One original hole closed, one hole added: net
   zero, not a completed sorry-free proof.
3. **Split statement: pass.** Independently read Stacks
   [045U](https://stacks.math.columbia.edu/tag/045U),
   [02NM](https://stacks.math.columbia.edu/tag/02NM),
   [02NJ](https://stacks.math.columbia.edu/tag/02NJ), and
   [054T](https://stacks.math.columbia.edu/tag/054T).
   Zero-dimensional Noetherian fibre stalks are Cohen-Macaulay, so the open
   Cohen-Macaulay locus and its relative-dimension pieces give the stated
   neighbourhood. The integer is not forced to be zero: the generic point of
   an affine line has stalk dimension zero and local topological dimension one.
   Nonreduced Artinian stalks also satisfy the argument. Empty X, empty U and
   empty fibres add no hidden nonemptiness assumptions. The statement has a
   complete sourced docstring and matching node. It is the local constancy
   step; the generic-stalk calculation, canonical interior construction,
   fibre-point transport and density are genuinely proved in the core module.
   Repeated LeanFinder search with Cohen-Macaulay-point wording, Loogle search
   for topologicalKrullDimAt, and source grep for equidimensionality, constancy
   and zero-dimensional stalks found no duplicate theorem. Smooth constancy
   requires a stronger hypothesis. The remaining theorem is not closable in
   a few minutes from the available APIs.
4. **Route and pruning: pass.** Read the unit sk-prop-normal-form and its
   realized fields. This supporting node is not a unit realization, and the
   slicing/relative-connectedness route is unchanged. Mathlib supplies generic
   point density and stalk/coheight comparison directly; no extra density
   hole or arbitrary chosen family is introduced. Both added core imports
   are proof-only and used. No old proof dependency or import is removed, so
   `No longer needed` is complete. The new module's DAG plan uses restricted
   fibre Noetherianity; added its missing proof-only import, as required for
   a still-open theorem's proof plan.
5. **Nodes: pass.** Checked the existing node changes are confined to proof,
   proof_deps and proof_origin; its Lean record is unchanged. Dependency lists
   equal the unions of step uses. The stalk-dimension dependency has an exact
   Mathlib match in Properties, which the proof invokes. The new node has the
   required source, statement dependencies, proof steps, searches, split status,
   creation provenance, blueprint ancestry, chapter/unit and verbatim Lean
   signature. Its restricted-fibre dependency now also has its module imported.

Second reading changed only the new module's missing proof-only import of
Sheaf.AlgebraicGeometry.RestrictedFibreLocallyNoetherian and this review report.
No proof or statement repair was necessary.
