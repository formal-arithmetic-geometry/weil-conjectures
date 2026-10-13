## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.GeometricGenericCoverSpread`,
`AlgebraicGeometry.exists_open_spreading_geometric_generic_cover`, with a complete Lean
assembly of the source argument. The existing signature and docstring are unchanged.
Added proof-only imports of `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`,
`Sheaf.AlgebraicGeometry.GeometricGenericCoverModel`,
`Sheaf.AlgebraicGeometry.GenericClosedSubsetFibreNonempty`, and
`Sheaf.AlgebraicGeometry.CommonFieldFibreComparison`.

The proof takes the closed cover on an etale model, obtains one open neighbourhood for
each generic edge, intersects these finitely many opens, and takes its open image in S.
For each test field it constructs the B_i as inverse images on a common-field fibre.
The cover is proved by inverse images of unions. Each intersection point is lifted
first using `range_fiberι` and then using surjectivity of field base change.

`CommonFieldFibreComparison` is fully proved from Mathlib: choose a point of the
product of the two field spectra over S, take its residue field, and compose five
canonical pullback isomorphisms. The comparison morphism is the resulting isomorphism
followed by the surjective projection of a field base change. No arbitrary data is
chosen in a definition from an unproved existence theorem; all choices occur inside
proofs. The two remaining geometric steps have individual modules and nodes.

All four modules compile together, without warnings. The unit `sk-prop-normal-form`
and its realized fields are unchanged. This continues the existing Tag 055G route
below the slicing unit.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.exists_open_spreading_geometric_generic_cover`
(node `lem-sbc-geometric-generic-cover-spread`). This is a decomposition into two
strict parts of its argument, not an axiom-free proof of the whole spreading result.

Added two holes, each exactly the whole proof of one public theorem:

- `AlgebraicGeometry.exists_geometric_generic_cover_model`
  (`lem-sbc-geometric-generic-cover-model`): spreading the cover and its geometric
  irreducibility on a single etale model. It asserts generic incidence only and
  does not assert persistence of intersections or the target's arbitrary test-fibre
  conclusion.
- `AlgebraicGeometry.exists_open_closed_subset_fibre_nonempty`
  (`lem-sbc-generic-closed-subset-fibre-nonempty`): one fixed closed subset meeting
  the generic fibre meets every fibre over some open. There is no covering family,
  geometric irreducibility, etale extension, or comparison scheme in this statement.

Also proved, with no sorry dependencies:
`AlgebraicGeometry.exists_common_field_fibre_comparison`
(`lem-sbc-common-field-fibre-comparison`). Its proof uses only Mathlib and has no
finite-type or etaleness hypotheses. The main module has no textual sorry left.
The delivery closes 1 hole and adds 2; its net textual hole change is +1.

## No longer needed

None. No existing imports were removed, and the original node had no recorded proof
dependencies to prune. The three original public Mathlib imports remain necessary
for the unchanged statement. Each added proof-only import is used.

The cover-model step treats the empty index type by Tag 054W; the assembly then
handles it uniformly through an empty finite intersection and inverse images of
an empty union. A separate empty-index theorem is unnecessary, so none was added.
The common-field step requires no faithfully-flat theorem: surjectivity of a map
between field spectra and its base change suffices, directly from Mathlib.

## Where the brief, the DAG or earlier work was wrong

The original node supplied a complete prose route but an empty `proof_deps` and a
single non-elementary step with no `uses`. There was consequently no list of
existing declarations from which its full plan could be assembled. The two
geometric conclusions now have explicit statements; the bookkeeping and field
comparison are fully formalized.

`GenericFlatness.exists_nonempty_open_flat_restrict` (existing node
`lem-sbc-generic-flatness`) gives flatness only, whereas the intersection-image
argument also needs finite presentation. It cannot alone supply the open image
without additional work. No statement of that module was changed or imported.
The available generic finite-etale model theorem requires an integral Noetherian
base and torsor data, which the present statement does not assume. It was not used.

LeanSearch was unavailable (HTTP Internal Server Error); the failed requests are
recorded, alongside successful LeanFinder/Loogle and source searches. No exact
Mathlib spreading theorem was found. Blueprint searches for Tag 0559, generic
flatness, and common field yielded no duplicate statement.

Edge cases checked in the new statements: empty I is allowed in the model step;
nonempty I with empty generic fibre contradicts the supplied irreducibility;
repeated C_i and absent generic edges require no extra assumption. The one-subset
step excludes an empty C by its own nonemptiness hypothesis, works over a nonreduced
irreducible base via reduction, and does not assume Noetherianity. The field step
works for empty X and arbitrary g because the product of the two field spectra
is nonempty at the common image s. Residue fields and pullbacks stay in universe u.

## New nodes

`lem-sbc-geometric-generic-cover-model`, in
`lean/Sheaf/AlgebraicGeometry/GeometricGenericCoverModel.lean`, records the cover and
geometric-irreducibility portion of Tags 0551, 054Y, and 0559, with the empty-family
case from Tag 054W. Its theorem is one of the two remaining holes.

`lem-sbc-generic-closed-subset-fibre-nonempty`, in
`lean/Sheaf/AlgebraicGeometry/GenericClosedSubsetFibreNonempty.lean`, records the
single closed-subset image argument from Tag 055G using Tags 052A and 01UA. Its
theorem is the other remaining hole.

`lem-sbc-common-field-fibre-comparison`, in
`lean/Sheaf/AlgebraicGeometry/CommonFieldFibreComparison.lean`, records the fully
proved common-field and pullback-comparison argument. The new nodes inherit the
original chapter, unit, and blueprint ancestor. The original node's proof,
proof_deps, and proof_origin now describe the Lean assembly. No change record is
needed: existing signatures, definitions, public imports, and visibility stay
identical, and no other existing module was adapted.

## Second reading by P4

1. I compared the delivered item module with the repository version. The existing theorem
   signature and all existing declarations are byte-for-byte unchanged; only proof-only
   imports and the proof body were added. Verdict: pass.
2. I compiled all four delivered modules with `lcompile.py --all`. There are no compile
   errors, forbidden declarations, or sorries in definitions. The common-field theorem
   has only `propext`, `Classical.choice`, and `Quot.sound`; the item theorem's remaining
   `sorryAx` comes only through the two explicitly split-off geometric theorems. Verdict:
   pass.
3. I reviewed the three split-off statements and their nodes. Each is a strict component
   of the original argument, has a source, proof prose, and a matching Lean declaration;
   the common-field statement is fully proved. Edge cases (empty index family, empty
   fibres, and arbitrary field-valued points) are covered by the stated hypotheses and
   constructions. Verdict: pass.
4. I checked the proof route and imports. The assembly uses the three split-off nodes and
   `UniversallyOpen`; all four added imports are used, and no old import or proof
   dependency is unnecessary. The unit route and realized fields are unchanged. Verdict:
   pass.
5. I checked DAG agreement: the item node's proof and `proof_deps` match the Lean proof,
   and each new node records its module, declaration, source, proof plan, and blueprint
   ancestry. Verdict: pass.

I changed only this report section; no Lean statements, definitions, or proofs required
repair after the audit.
