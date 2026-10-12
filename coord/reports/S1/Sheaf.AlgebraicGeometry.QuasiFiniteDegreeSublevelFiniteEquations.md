## What changed

The target theorem is proved by applying two new geometric sublemmas in
`Sheaf.AlgebraicGeometry.FiniteEquationsOfClosedAffine`: the specialized finite-generation
step for the quasi-finite degree sublevel locus and the finite-generator basic-open
characterization. The new module is imported privately by the target module.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Hom.exists_finite_equations_degree_sublevel_inter_affine`.
This is a decomposition: the two lower statements remain open:
`AlgebraicGeometry.Scheme.Hom.exists_finitely_generated_zeroLocus_ideal_degree_sublevel_inter_affine`
(node `lem-weil-pbc-finite-equations-of-isClosed-inter-affine`) and
`AlgebraicGeometry.Scheme.Hom.exists_finite_equations_of_finitely_generated_zeroLocus`
(node `lem-weil-pbc-finite-equations-of-finitely-generated-zeroLocus`). No definition contains
`sorry`.

## No longer needed

None. The target's existing proof-dependency route is replaced by the two strictly lower
geometric steps, both of which are used by the proof.

## Where the brief, the DAG or earlier work was wrong

The first worker's generic theorem claiming that every closed subset on an affine open is the
zero locus of a finitely generated ideal is false for non-Noetherian affine schemes. It was
replaced by the source-appropriate statement specialized to the degree sublevel locus and its
finite-presentation hypotheses.

## Second reading by S1

1. Compared the target module with the repository version: the target statement and all existing declaration signatures are byte-for-byte unchanged; only the proof and a private import changed.
2. Compiled both modules with `lcompile.py --all`; compilation succeeds with no errors. The only remaining holes are the two named split-off theorems above.
3. Checked the corrected split-off statements. The specialized finite-generation statement is the needed Stacks argument and the finite-generator/basic-open statement is true and exactly strong enough. The false generic statement was removed.
4. Checked the proof route and unit: it uses both lower nodes and retains the planned affine finite-equations route.
5. Updated both DAG node metadata and verified their declarations match the Lean code.

Changed: corrected the affine finite-generation theorem and node, adapted the target proof, and
updated the target node's proof dependencies.

## New nodes

`lem-weil-pbc-finite-equations-of-isClosed-inter-affine` records the specialized finite-generation
statement in `lean/Sheaf/AlgebraicGeometry/FiniteEquationsOfClosedAffine.lean`.

`lem-weil-pbc-finite-equations-of-finitely-generated-zeroLocus` records the finite-generator
basic-open statement in the same module.
