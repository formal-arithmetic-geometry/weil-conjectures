## What changed

Added the sieve intermediate and proved
`AlgebraicGeometry.Etale.exists_cartesianHigherImage_affine_section_local_zero`
from it by finite affine refinement. The existing finite-cover separatedness
theorem was rechecked unchanged: its proof constructs the integer-scalar
morphism into the later stage, proves it is zero after restriction to every
cover arrow, and evaluates it at `1`. The unused proof-only imports
`Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit` and
`Sheaf.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison` were removed.

## Proved and sorry left

Closed the sorry in `exists_cartesianHigherImage_affine_section_local_zero`.
The new theorem `cartesianHigherImage_affine_section_local_zero_sieve` remains a
single named sorry (the cohomology-continuity and affine-descent argument in its
docstring is still pending).

## No longer needed

Removed the proof-only imports `Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit`
and `Sheaf.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison`; their
nodes are not needed by the proved finite-cover separatedness argument.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan did not expose the finite-affine refinement wrapper, so the
target is proved by splitting out the covering-sieve statement and applying the
existing finite-cover separatedness theorem. No statement was changed.

## New nodes

`lem-sc-cartesian-higher-image-affine-section-local-zero-sieve` records the
strictly weaker covering-sieve intermediate theorem
`cartesianHigherImage_affine_section_local_zero_sieve`; its proof still requires
the affine cohomology-continuity and descent construction described in the node.

## Earlier second reading (a previous round; superseded)

The finite-cover proof was checked against the unchanged statement. The new sieve intermediate is strictly weaker and is used only to select a finite affine family.

## Second reading by F3

1. Compared the delivered module with the repository version. Existing declaration
   signatures are unchanged; the added sieve theorem is recorded by the new node.
2. Compiled the module successfully with `lcompile.py`. The finite-cover theorem has
   no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`; only the new
   sieve theorem intentionally retains its named `sorry` hole.
3. Checked the split-off sieve statement against the hypotheses and conclusion. It is
   strictly weaker than the finite affine-family target and has a source, proof
   description, and DAG node; no duplicate declaration was found in the library.
4. The proof uses sheaf hom-extensionality and the finite affine refinement API. The
   removed cohomology imports are unnecessary for the proved declarations. The
   pending sieve theorem retains the planned cohomology-continuity route, and the
   unit route is unchanged.
5. The node and Lean declaration agree on the theorem name and statement, with the
   new node marked `split`; no definition or target statement was changed.

Changed the delivered module by adding the sieve intermediate, using it to prove
the finite affine-family wrapper, and removing two proof-only imports.
