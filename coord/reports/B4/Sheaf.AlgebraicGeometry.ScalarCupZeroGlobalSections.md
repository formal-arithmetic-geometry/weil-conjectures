## What changed

Proved `scalarCohomologyCup_zero_globalSections` with its signature and docstring unchanged.
Added proof-only imports of `ScalarCohomologyExtZeroGlobalSections` and
`ScalarTensorGlobalSectionsMorphism`, each containing one proved public theorem.
The first identifies a degree-zero cohomology class with mk₀ of its scalar section
morphism. The second proves the ordinary tensor-morphism identity by the
sheafification adjunction, the lax monoidal unit law, and the existing pure-tensor
coefficient evaluation. The target follows by expanding scalarExtCup, applying
mk₀ transport and composition identities, and using the two comparison inverse laws.
All three modules compile without warnings under lcompile.py.

## Proved and sorry left

Closed the one original hole: `scalarCohomologyCup_zero_globalSections`
(node `lem-sc-scalar-cup-zero-global-sections`).
Also proved `scalarCohomologyExtEquiv_zero_globalSections`
(node `lem-sc-scalar-cohomology-ext-zero-global-sections`) and
`scalarTensorCoefficient_globalSections_morphism`
(node `lem-sc-scalar-tensor-global-sections-morphism`).
No sorry remains in any delivered module; no holes were added or split off.
Existing imported definitions and theorems retain their existing holes.

## No longer needed

No original import was removed, and neither of the original definition nodes is
pruned: both provide the definitions used by the statement and proof.
No additional resolution-product or degree-one cup module is needed.
The new tensor-morphism module imports FieldLinearModuleCohomologyOperations directly;
it does not require ScalarGlobalSectionsComparison or ScalarExtCupDegreeZero.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or definition was changed. The original prose plan was
correct but did not expose the degree-zero comparison and tensor section-morphism
identities as separate usable interfaces. Both have now been proved.
The edge cases require no extra hypotheses: all section formulas and categorical
identities hold for zero sections, zero coefficient sheaves, and the empty scheme.

## New nodes

`lem-sc-scalar-cohomology-ext-zero-global-sections` records the proved comparison
between the right-derived degree-zero global section and its scalar mk₀ class.
Its proof uses the defining resolution cocycle formula and an augmentation identity
specialized from Mathlib's InjectiveResolution.extMk_hom. The small private augmentation
proof follows the existing AbelianCechComparisonNormalization proof, without importing
that broader cohomology module.

`lem-sc-scalar-tensor-global-sections-morphism` records the proved tensor identity
for scalar section morphisms. The proof establishes the scalar-unit and section
morphism evaluation at every open, then uses the lax monoidal inverse unit law,
tensorator naturality, and exists_scalarTensorCoefficient. The comparison node is
not needed by this ordinary morphism calculation. Both nodes lie below the existing
cube-theorem unit route; no unit statement or realized step was bypassed.

## Second reading by B4

1. **Interfaces and accidental changes.** Compared every delivered module with the
repository versions. The original target signature is byte-for-byte unchanged; the two
additional modules and three node records are intentional additions. No unrelated file
was changed.

2. **Proof validity.** Compiled all three delivered modules with `lcompile.py --all`.
There are no `sorry`s, axioms, unsafe declarations, or hollow definitions in the
delivered files; the proofs use only the permitted categorical and classical machinery.

3. **Statements and split nodes.** Checked both split-off statements against their
docstrings, sources, and existing declarations. The comparison theorem and tensor
morphism theorem are true, strictly simpler than the target, and needed by the target;
neither duplicates an existing library declaration.

4. **Pruning and imports.** The target proof uses both new interfaces and retains the
unit route. Imports in the new modules are required by their public signatures or proof;
the target's two added imports are proof-only imports. No old proof dependency can be
removed.

5. **DAG agreement.** Checked each node's Lean declaration, proof steps, proof
dependencies, source, unit, and blueprint against the code. The realized unit route is
preserved and all three nodes accurately record the delivered proofs.

Changed after review: added this second-reading record only; no Lean proof or statement
required repair.
