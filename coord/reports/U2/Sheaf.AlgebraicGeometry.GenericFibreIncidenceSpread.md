## What changed

Replaced the proof of
`AlgebraicGeometry.exists_open_generic_fibre_incidence_spread` in
`Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread`, preserving its signature and
all existing public imports. Added proof-only imports of
`Mathlib.AlgebraicGeometry.Noetherian`,
`Sheaf.AlgebraicGeometry.GenericComponentsSplit` and
`Sheaf.AlgebraicGeometry.GeometricGenericCoverSpread`.

The proof first applies component splitting to the generic fibre. It constructs
`G` as the pullback, `I` as the subtype of irreducible components of `G`, and `A`
as their underlying subsets. Mathlib proves that `G` is noetherian, that `I` is
finite, that each `A i` is closed and irreducible, and that their union is the
whole space. Spreading the supplied geometric cover then supplies `W` and the
special-fibre covers. The original node's proof and proof dependencies now follow
this argument. No definitions, existing statements, or interfaces were changed;
there are no forced adaptations or change records.

Source checked: Stacks Project Tags
[055G](https://stacks.math.columbia.edu/tag/055G),
[0551](https://stacks.math.columbia.edu/tag/0551),
[054R](https://stacks.math.columbia.edu/tag/054R),
[0559](https://stacks.math.columbia.edu/tag/0559), and
[054Y](https://stacks.math.columbia.edu/tag/054Y).
The unit `sk-prop-normal-form` has no realized-node constraints on this item;
the component-cover portion of slicing follows the same route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_open_generic_fibre_incidence_spread`
(node `lem-sbc-generic-fibre-incidence-spread`). Its proof contains no `sorry`.

Added two named holes, each the entire proof of a public theorem in its own module:

- `AlgebraicGeometry.exists_finite_etale_geometric_component_extension`
  in `Sheaf.AlgebraicGeometry.GenericComponentsSplit`,
  node `lem-sbc-generic-components-split`.
- `AlgebraicGeometry.exists_open_spreading_geometric_generic_cover`
  in `Sheaf.AlgebraicGeometry.GeometricGenericCoverSpread`,
  node `lem-sbc-geometric-generic-cover-spread`.

This is a decomposition, not a sorry-free proof of the geometric theorem:
one hole closed and two added, net minus one. The first remaining theorem concerns
only a finite type scheme over a field and asserts no shrinking or special-fibre
conclusion. The second takes the generic extension, finite index and geometric
closed cover as fixed inputs; it constructs none of those generic data. They are
strict parts of the original argument. The finite index and ordinary component
cover are constructed in Lean using Mathlib, not supplied by another hole.
There are no hollow definitions or unproved choices in any definition.

All three delivered modules compile with `lcompile.py --all`, without warnings.
The delivery dry run also compiles the modules and runs the axiom probes.

## No longer needed

None. The original node had no proof dependencies or proof imports to prune.
All three added proof imports are used. Generic component splitting and generic
incidence persistence remain necessary; the proof never uses a connectedness
assumption or the connected-graph step of Tag 055G. No existing node or module is
claimed to become unreachable from the targets.

## Where the brief, the DAG or earlier work was wrong

The item was supplied with an empty `proof_deps` list despite its non-elementary
four-step geometric proof plan. There were no named statements to import for
those steps. The delivery makes two of those geometric parts into independent
items and implements their combination in Lean. Existing generic-component
clopen results concern connected components and do not supply geometric
irreducibility or incidence persistence, so they were not used.

Mathlib searches were run through `msearch.py`, with separate three-kind searches
for both new nodes and an initial search for the whole item. LeanSearch returned
HTTP Internal Server Error, recorded as unavailable. LeanFinder and Mathlib grep
found the finite-components theorem and general geometric APIs, but no matching
component-splitting or cover-spreading theorem. Blueprint searches for 0551,
054R and generic covers found no exact existing node. Local literature source
files are unavailable in this checkout, so the named Stacks pages were read online.

Edge cases checked mathematically: the empty scheme has no components, and the
identity field extension satisfies the splitting theorem vacuously. An empty
index in the spreading theorem forces the generic fibre to be empty and is
handled by Tag 054W. Every geometric irreducibility hypothesis asserts
nonemptiness, so no empty member of a nonempty cover is admitted. Repeated members
of a cover are allowed. Nonreduced bases are handled by reducing the affine
finite etale model; reduction preserves the relevant topology and residue fields.
The cover lemma uses Tag 054Y rather than assuming the complement of closures is
quasi-compact over a nonnoetherian base. Only generic edges are retained, and no
claim that empty generic intersections stay empty is needed. The common test
field extension can be chosen in universe `u`, since it is a residue field of a
tensor product of two `u`-small fields. No target statement changed.

## New nodes

`lem-sbc-generic-components-split` in
`dag/nodes/sec-smooth-base-change/lem-sbc-generic-components-split.json`
records finite separable component splitting (Stacks Tag 054R). Its Lean module
is `Sheaf.AlgebraicGeometry.GenericComponentsSplit`. Its statement quantifies
field base changes explicitly as inverse images under the first pullback map,
so it expresses nonempty geometric irreducibility of each closed component.

`lem-sbc-geometric-generic-cover-spread` in
`dag/nodes/sec-smooth-base-change/lem-sbc-geometric-generic-cover-spread.json`
records the closure, shrinking, edge-image and common-field portion of Tag 055G.
Its Lean module is `Sheaf.AlgebraicGeometry.GeometricGenericCoverSpread`. It
accepts any supplied finite geometric closed cover; maximality of its members as
components is unnecessary for this portion of the argument.

Both nodes have complete proof sketches in their theorem docstrings, the parent
chapter and unit, blueprint ancestry through the parent node, and actual logged
Mathlib searches. Neither is a renamed version of the original statement.

## Second reading by U2

1. **Interface check: pass.** Read all three delivered modules and compared
   `GenericFibreIncidenceSpread.lean` with the repository using `diff -u`.
   The complete existing theorem signature is byte-for-byte identical; its
   docstring, namespace, universes, visibility and three public imports are
   unchanged. Only its proof and three proof-only imports differ. The other
   two modules are new, with one public theorem each. There are no definitions,
   adaptations or statement changes.
2. **Proof and kernel check: pass as a decomposition.** Independently ran
   `lcompile.py --all`; all three files compiled without warnings. Compiled
   temporary copies through `lcompile.py` with `#print axioms` for each of
   the three declarations. Each reports exactly `propext`, `Classical.choice`,
   `Quot.sound` and `sorryAx`, the latter expected from the two listed open
   theorems. The original proof contains no `sorry`; each new theorem has
   exactly its single whole-proof `by sorry`. No prohibited declarations,
   attributes or hollow definitions occur. The existential witnesses are
   eliminated inside a proof of a proposition, not used to define data from
   an unproved existence theorem.
3. **Split statements: pass.** Checked every hypothesis and conclusion of
   both new Lean statements against their node records and the cited Stacks
   proofs. Tag 054R directly provides the finite separable extension; finite
   type over a field gives the finiteness hypothesis it requires. The first
   projection in the field-base-change condition has domain `G times_L E`,
   codomain `G`, and its inverse image is the underlying closed-subscheme
   base change. The second lemma fixes the extension, finite index and cover;
   it proves only their spreading. Neither reasserts the original existential
   generic-data construction. Tag 054Y accepts arbitrary finite closed covers,
   so maximality as irreducible components is unnecessary. Re-read Tags 0551,
   0559, 052A, 01UA and 054W: reduction makes the model base integral before
   applying generic flatness, and a closed immersion preserves finite type,
   so those steps do not require a Noetherian base. Checked the empty scheme,
   empty index, repeated cover members, diagonal incidence edges, inseparable
   test-field extensions, nonreduced bases and universes. Field-extension
   faithful flatness preserves nonempty intersections; a residue field of
   the nonzero tensor product provides the common field in universe `u`.
   Ran fresh logged LeanFinder searches using “absolutely irreducible” and
   “dense open” formulations and a Mathlib grep of the geometric APIs;
   searched both local Lean roots and the DAG. No theorem closes either hole
   directly. Neither geometric lemma can be completed in a short local pass.
4. **Route and pruning: pass.** Followed the original proof from the top:
   split the generic components; construct their finite subtype and underlying
   sets using Mathlib; obtain closedness, nonempty irreducibility and the union
   identity; apply the supplied-cover spreading lemma; assemble the unchanged
   conclusion. Read the recorded dependency
   `lem-weil-pbc-noetherian-finite-components` in `sec-smooth-purity`; its
   Mathlib match is precisely the finite-components theorem used. The original
   node has an empty `proof_deps`, so there are no old nodes to list as unused.
   All three added imports are proof-only and supply used declarations or
   instances. The new modules expose the dependencies of their signatures.
   Read `dag/units/sk-prop-normal-form.json`: its realized statement and both
   realized step lists are empty, and the component-cover route is preserved.
   No pruning or change to the unit is claimed.
5. **Node and report check: pass.** The only changed fields of the existing
   node are `proof`, `proof_deps` and `proof_origin`, with dependency union
   exactly the three nodes used in its steps. Both new nodes have their source,
   full natural-language proof, self-contained statement, existing statement
   dependencies, search records, creation record, blueprint ancestry, parent
   chapter/unit and complete Lean record. Their recorded Lean signatures occur
   verbatim in their modules, and all dependency IDs exist. The report names
   the one closed hole and both added holes and explicitly reports net minus
   one, rather than calling the decomposition a sorry-free proof.

**Changes by the second reader:** added this independent review and fresh search
logs. No fault requiring a Lean or node edit was found; those files were retained.
The delivery remains one original hole closed out of one, two split-off holes
added, and no modules pruned.
