## What changed

Added a compiling proof of `AlgebraicGeometry.minimal_component_dimension_maximum` by extracting the required bounds and attainment from a finite-component auxiliary theorem. Added the auxiliary theorem as a named stage-3 node with its proof left for a subsequent worker.

## Proved and sorry left

- Proved `AlgebraicGeometry.minimal_component_dimension_maximum`.
- Sorry left in `AlgebraicGeometry.minimal_component_dimension_maximum_data`.

## No longer needed

Removed proof-only imports `Mathlib.RingTheory.Ideal.Height`, `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`, `Sheaf.RingTheory.FiniteTypeDomainDimensionLocalRing`, `Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg`, and `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`; the target proof uses only the private auxiliary module import. The corresponding old proof dependencies are no longer needed by the target proof.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan expands a long prime-chain argument that is not executable from the currently stated interfaces in the allotted module. The argument was therefore factored into a finite-component intermediate theorem, which is strictly stronger by recording the finite set and its membership characterization.

## New nodes

- `lem-weil-pbc-minimal-component-dimension-maximum-data`

## Earlier second reading (a previous round; superseded)

The auxiliary statement is strictly stronger than the target because it records a finite indexing set and its exact membership characterization. The target proof compiles by projection from this data. The remaining sorry is therefore isolated in a theorem that is a genuine finite-component subargument.

## Second reading by T3

1. Compared the delivered target module and existing DAG node with the repository. The theorem signature is unchanged; only its proof, the proof dependency, and the new auxiliary node are added.
2. Compiled both modules with `lcompile.py --all`; compilation succeeds. The target proof contains no `sorry`; the only remaining hole is the named auxiliary theorem `AlgebraicGeometry.minimal_component_dimension_maximum_data`, with its matching node. No prohibited declarations occur.
3. Checked the auxiliary statement against the target: it is a finite-set strengthening that supplies exact membership, nonemptiness, bounds, and attainment, so the target follows by projection. Its documentation records the Stacks Project source and proof route. Corrected its `stmt_deps` to the five definition nodes used by its hypotheses (rather than incorrectly depending on the target theorem itself).
4. The target proof uses the shortest available route, namely projection from the auxiliary theorem. The unit route is retained through the target node. Removed proof-only imports of the old prime-chain modules; retained only the four public Mathlib imports needed to elaborate the target signature and made the auxiliary import private.
5. Checked that the DAG proof and `proof_deps` now match the Lean proof: the target depends only on `lem-weil-pbc-minimal-component-dimension-maximum-data`; the auxiliary node retains the documented prime-chain dependencies.

Changed the target imports, corrected the auxiliary node dependencies, and appended this review. No target statement or definition was changed.
