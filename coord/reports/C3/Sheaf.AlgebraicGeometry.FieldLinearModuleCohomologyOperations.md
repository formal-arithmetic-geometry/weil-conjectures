## What changed

Proved `scalarCohomologyExtMap_smul` in
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`. A private construction and four proved helpers provide
multiplication on the structure sheaf, verify its action on the constant scalar unit, and identify
scalar multiplication under the recorded injective-resolution comparison. A private generic Ext
identity then combines exact-functor transport with degree-zero precomposition.

Added the proof-only import `Mathlib.Algebra.Homology.ConcreteCategory` for cycle representatives.
The section-local irreducibility of `scalarMap`, `scalarUnitLinear`, `scalarSheaf`, and the private
scalar endomorphism prevents unnecessary unfolding. It ends at the existing section boundary.
No public signature, definition body, visibility, or global attribute changed. The conservative
static command check is documented in
`coord/changes/field-linear-scalar-proof-scope-C3.md`, including all direct importers.
The full module compiled without errors or warnings in 46.5 seconds through `lcompile.py`.
The first dry run also passed compilation and the axiom probe; its sole non-reader finding
was the missing scope-change record, now supplied.

## Proved and sorry left

Closed one of the two original holes: `AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_smul`.
Its proof is complete and adds no holes. This is a proof, not a decomposition.

The sole remaining hole is the unchanged named theorem
`AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_bijective`, with node
`def-sc-field-linear-module-cohomology-operations`.

## No longer needed

No existing imports, modules, or DAG dependencies are pruned. The proof does not need the
downstream `ScalarCohomologyExtCoefficientNaturality` module; importing it would create a cycle.
The earlier attempt's unlanded `lem-sc-field-linear-ext-map-smul` and
`lem-sc-field-linear-ext-map-bijective` restatement node copies were discarded. No new nodes are
added, and the existing fixed-resolution comparison remains needed by `exists_moduleExtEquiv`.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left both original holes and could not pass the delivery gate. Its proposed
scalar Ext helper restated scalar linearity rather than reducing it. The direct cocycle argument
is usable: the actual missing glue was specifying the adjunction's evaluation morphism and
isolating the generic Ext identity before specializing it. Explicit universes and objects avoid
expensive inference at the specialization. The mathematical statements and the unit's route are
unchanged. The zero scalar, zero module, degree zero, and empty scheme require no extra hypothesis
in any of the constructions or proofs.

## Second reading by C3

1. Compared the complete delivered module against the repository with `diff`, and compared
   all 65 original declaration records with the project's declaration parser. Every existing
   signature, definition body, visibility and docstring is byte-for-byte unchanged. The only
   new import is plain, proof-only `Mathlib.Algebra.Homology.ConcreteCategory`. Additional
   universe names serve the private Ext identity, and new irreducibility attributes are local
   to the existing section. The scope-change record accurately describes these changes. Pass.
2. Independently compiled the delivered file through `lcompile.py`: no errors or warnings.
   Scanned its source for forbidden trust mechanisms and definition holes: none. There is
   exactly one remaining `sorry`, in the unchanged named bijectivity theorem. The explicit
   scalar endomorphism uses compatible sections and `unitHomEquiv`, not an existence witness.
   The resolution representative is obtained from proved Ext surjectivity; the chosen
   comparison is determined by its cocycle characterization. Pass.
3. No statements were split off and no new holes were added. Read all five private helpers:
   their statements are strictly intermediate and their proofs are complete. Multiplication
   is compatible with restriction; the adjunction calculation evaluates the scalar-unit map;
   the cycle argument uses module-linear homology projection and comparison. Zero scalars,
   zero coefficients, degree zero and the empty scheme introduce no extra condition: the
   proofs use ring/module identities, and `n + 1` works also at zero. Pass.
4. Searched independently using LeanFinder, Loogle and grep through `msearch.py`, plus `rg`
   across both library roots and the relevant Mathlib sources. The generic linear-functor
   lemma requires a linear structure on the source category and a linear functor; these are
   not supplied here. The proof instead uses existing Ext composition and cocycle lemmas
   directly. The similar downstream coefficient-naturality result would introduce an import
   cycle and does not replace this scalar argument. The new ConcreteCategory import supplies
   `cyclesMk` and `i_cyclesMk`. No old dependency is retired; `## No longer needed` is complete.
   Read `dag/units/sk-prop-av-cube.json`: its statement, steps and realized fields are unchanged,
   and no unit step is bypassed. Pass.
5. Compared the node JSON with the repository. Only `proof` and `proof_origin` change; the
   added step follows the scalar-endomorphism, adjunction, cocycle and Ext-composition argument
   exactly. `proof_deps` retains `lem-sc-module-resolution-homology-ext`, still used through
   `exists_moduleExtEquiv`. No new node needs to be supplied. Pass.

Second reading replaced the goal-wide `unfold moduleExtEquiv` in the private cycle helper
with direct `with_unfolding_all exact Classical.choose_spec ...`. Profiling reduced that local
characterization subproof from about 5.3 seconds to 1.2 seconds, preserving its statement and
argument. No DAG change was needed. The scratch `#print axioms` check for scalar linearity
shows exactly `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`. Closed: `AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_smul`. Added
holes: none. The original bijectivity obligation is left unchanged, not split off.
