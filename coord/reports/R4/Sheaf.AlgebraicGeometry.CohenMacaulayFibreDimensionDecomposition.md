## What changed

Replaced the submitted neighbourhood/topology split after the second reading found
that local constant neighbourhoods merely repackage the target. The unchanged target
`AlgebraicGeometry.exists_fibre_dimension_open_partition_of_depth_eq_ringKrullDim`
now obtains equidimensional fibre pieces, proves local finite type of the original
fibre through the restriction pullback and residue-field isomorphism, and applies
the separate locally algebraic equidimensional-open dimension comparison.

Added two proof-only imports to the target: `EquidimensionalFibreOpenPartition` and
`EquidimensionalOpenLocalDimension`. The first new module imports the existing
`RestrictedFibreLocallyNoetherian` for its proof plan. All original signatures,
definitions, public imports and docstrings remain unchanged. The provisional
`LocalFibreDimensionNeighbourhood` and `PartitionOfLocalFibreDimension` modules and
nodes are removed from the delivery.

## Proved and sorry left

Closed the direct hole in
`AlgebraicGeometry.exists_fibre_dimension_open_partition_of_depth_eq_ringKrullDim`
(1 of 1 original holes). Added exactly two lower holes:

- `AlgebraicGeometry.exists_equidimensional_fibre_open_partition_of_depth_eq_ringKrullDim`
  — node `lem-sbc-cohen-macaulay-equidimensional-fibre-pieces`.
- `AlgebraicGeometry.topologicalKrullDimAt_eq_of_equidimensional_open`
  — node `lem-sbc-equidimensional-open-local-dimension`.

This is a decomposition, not a complete proof: one upper hole becomes two lower
holes, so the direct hole delta is -1. No claim of positive ledger progress is made.
The first hole supplies the geometric part of the original plan, with dimensions
of irreducible components rather than local dimensions at points. The second is a
general comparison over any field; it has no flatness, Cohen-Macaulay, base-open,
or partition hypothesis. The target performs the finite-type transport and
comparison explicitly. No object is defined by choosing an arbitrary witness of
an unproved existence theorem: the proof only eliminates an existential in Prop.

All three delivered files compiled. Explicit `#print axioms` in a scratch copy
shows only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` (the two
reported holes and their transitive uses); no other axiom is used.

## No longer needed

No repository import or transitively needed module is pruned. Both old direct
proof dependencies are retained downstream: `lem-sbc-restricted-fibre-locally-noetherian`
in the geometric-piece proof plan, and
`lem-weil-pbc-dimension-at-point-open-subspace` in the comparison proof plan.
They are replaced as the target's direct proof dependencies by the two new nodes.
The two provisional submitted modules/nodes were never repository dependencies;
removing them does not count as pruning repository modules.

## Where the brief, the DAG or earlier work was wrong

The submitted local-neighbourhood hole was equivalent to the target up to the
unproved elementary topology partition step; it did not isolate the substantial
geometric argument. The submitted node statements also omitted their hypotheses,
their blueprint ancestors named a non-blueprint node, their search records were
not present in this sandbox's search log, and the target DAG still described the
old route. These faults are repaired. The original target is mathematically
consistent with Stacks 02NM, 02NJ and 0A21; no target correction is needed.

## New nodes

`lem-sbc-cohen-macaulay-equidimensional-fibre-pieces` carries the 02NM/02NJ
geometric decomposition after restriction to W over U. Its statement is
self-contained and does not assert local dimension equalities. The existing
restricted-fibre locally-Noetherian node supports the depth formulation.

`lem-sbc-equidimensional-open-local-dimension` carries the 0A21 (3), (5)
comparison for an arbitrary open in a scheme locally of finite type over a field.
The irreducible-only existing `dimension_locally_algebraic` declaration does not
state this reducible version. No change records are needed: no existing interface
is changed.

## Second reading by R4

1. Compared the target module with the repository using diff. Its only changes
   are two plain proof imports and the replacement of its proof body; the existing
   theorem signature, public visibility and all definitions are byte-for-byte
   unchanged. The new modules have no repository counterpart and introduce only
   named theorems. No changed statement or definition needs a change record.
2. Compiled all three modules through lcompile.py in import order and checked the
   forbidden-declaration scan. Exactly the two reported named theorem bodies are
   `by sorry`; there are no definitions, unsafe declarations or additional axioms.
   The explicit axiom print in the scratch copy confirms the allowed list with
   `sorryAx`. The target proof uses the genuine restricted-fibre pullback, its
   inverse isomorphism and the residue-field isomorphism; these are determined
   constructions, not data from an arbitrary existence witness.
3. Read Stacks https://stacks.math.columbia.edu/tag/02NM (flat + locally finitely
   presented + Cohen-Macaulay fibres) and 02NJ (equidimensional nonempty fibres),
   and https://stacks.math.columbia.edu/tag/0A21 (3), (5). The geometry statement
   matches these hypotheses after open restriction and stalk transport. The
   comparison requires local finite type over a field, which the target explicitly
   proves before using it. Tested empty W, empty fibres, empty O, n=0, reducible
   equidimensional fibres, and points which are generic rather than closed.
   Components through a point exist; their common dimension n makes the maximum
   in 0A21 (5) equal to n. No closed-point hypothesis or global quasi-compactness
   is silently used. Searches via msearch.py used new equidimensional-component
   wording (LeanFinder, LeanSearch, grep), and rg checked both library roots and
   upstream components/dimension declarations. LeanSearch was unavailable and is
   recorded as such. No existing declaration gives either exact new statement.
4. Reviewed from the target downward. Removed the equivalent-neighbourhood split
   and the gratuitous unproved topology step. The replacement follows the original
   source route: geometric pieces, then local dimension comparison. The existing
   irreducible-only comparison does not cover reducible equidimensional opens.
   All statement imports are public and added target proof imports are plain.
   `dag/units/sk-prop-normal-form.json` has empty realized statement/step lists;
   no realized unit node is bypassed. The old proof dependencies remain downstream,
   so the pruning list correctly reports none.
5. Read each new node beside its Lean statement and checked its verbatim lean
   signature, complete hypotheses, source, proof sketch, proof-dependency union,
   three search records, creation fields, chapter/unit and blueprint ancestor
   `sbc-lem-slicing`. Blueprint search found no same statement (the smoothness
   definition hit for equidimensional is not a theorem). Updated the original
   node's proof, proof_deps and proof_origin to match the actual three-step Lean
   reduction, including the explicit finite-type transport. The node's statement
   and its lean signature are unchanged.

Changes made by the second reading: replaced both provisional helpers by the
source's geometric-piece/comparison reduction, implemented the restricted-fibre
finite-type transport, rebuilt both new nodes with self-contained statements and
logged searches, updated the target DAG route, and corrected the progress report
from an apparent proof to an explicit two-hole decomposition.
