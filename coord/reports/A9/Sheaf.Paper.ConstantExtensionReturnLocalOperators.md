## What changed

Reduced `WeilConjectures.constantExtensionReturnLocalOperators` to three strictly
smaller, separately assigned mathematical steps and wrote the complete Lean assembly.
Its original signature, hypotheses, universes and conclusions are unchanged.

The assembly obtains the specified return equivalence, applies the finite/rational
transport clauses and the local spectrum comparison, and proves punctual purity
by replacing the eigenvalue predicate at every closed point. It then constructs
the subobject order isomorphism explicitly by lowering `MonoOver.congr` to the
thin skeleton. Preservation of cokernels identifies its quotient objects.
`OrderIso.arrowCongr` transports every finite chain; injectivity and preservation
of bottom/top prove its endpoint conditions. Finally the proof maps the actual
mixed filtration through the functor and inverse equivalence, preserving each
monomorphism, zero object, cokernel, pure quotient weight and weight upper bound.
The unit identifies the last inverse image with the original sheaf.

Moved the existing comparison interfaces, unchanged in mathematical content, to
`Sheaf.Paper.ConstantExtensionReturnData`, publicly reexported by the item module.
This lets the three new theorem modules use those predicates without importing
the theorem which imports them. All 18 original public declarations are retained;
all original signatures and non-theorem bodies are unchanged. The three existing
normalization proofs are retained in the extracted interface. The definitions
still use exactly the prescribed compositors and uniquely fixed stalk formula.
No arbitrary witness, source-library modification or target change is introduced.

The remote single-file compile of the complete main assembly passed without errors
or warnings in 20.4 seconds. The interface and all three new statement modules also
passed their single-file compiles. The delivery tool runs the final compile and
preflight over the exact packet before pushing.

The change record is `coord/changes/A9-sheet-return-comparison-interface.md`.
The revised parent node records the assembly; the new statement nodes retain the
original eleven-step mathematics at the relevant smaller steps. The unit's
statement and realized proof steps are unchanged.

## Proved and sorry left

The current library baseline has one hole in this item:
`WeilConjectures.constantExtensionReturnLocalOperators`, node
`lem-zl-constant-extension-return-local-operators`.
That upper hole is closed by a complete assembly from the following three
new, strictly smaller theorem holes:

- `WeilConjectures.sheetReturnExactFunctor`, node
  `lem-zl-sheet-return-exact-functor`: construction of the normalized return
  equivalence only; no transport, local spectra, purity or filtration claims.
- `WeilConjectures.sheetReturnTransportComparison`, node
  `lem-zl-sheet-return-transport-comparison`: finite and whole-tower ordered
  block laws and rational operator/naturality/scalar equations only.
- `WeilConjectures.sheetReturnLocalSpectra`, node
  `lem-zl-sheet-return-local-spectra`: assuming the rational operator and
  scalar equations and any specified return functor, prove the common-stage
  spectra, residue-degree/cardinality formula and local conjugacy only.

This is a decomposition, not a net proof gain: one upper hole closed, three lower
holes added, zero unconditionally proved original holes beyond the prior Q4
landing. There are zero actual `sorry`s in the item module, zero in the interface,
and three total in the delivery. Each remaining proof is exactly `:= by sorry`,
in its own public theorem/module, with source, complete proof in words and node.

The three normalization lemmas `SheetReturn.powerEquality`,
`sheetReturnPointFibre_eq`, and `sheetReturnStalkIso_existsUnique` are proved and
preserved. At session start the shared Lean source still showed their holes,
although the Q4 report/ledger already recorded their proofs; the source refreshed
during this session. They are not counted again as new progress.

## No longer needed

No module is withdrawn and no mathematical dependency is claimed globally unused.
The downstream scan found zero current importers, but the DAG parents still need
this item and are retained. No unit route is bypassed.

The item now imports only its public interface, the three proof steps, and the
categorical helpers it uses. Its original public prerequisites are all preserved
through the interface's public imports. The original private proof-plan imports
remain dependencies in the relevant smaller statement nodes rather than
directly imported by the assembly: `IteratedReturnTransportScalarCalculus`,
`IntegralPullbackComparisonRealization`, `LocalFrobeniusConjugacyClass`,
`SemilinearScalarLocalization`, and `ClosedPointField`. The redundant direct
`IntegralFinitePullbackComposition` import is unnecessary because its public API
already comes through `PointTransportComposition` and the tower interface.
The new holed theorem modules import only the interface their statements need;
unused proof-only imports were removed. These dependencies remain in the smaller
nodes' proof plans; they are not pruned
from the mathematical argument.

The separate abstract cyclic-return subobject/finite-chain clauses are not used
by the assembly: it proves these from the returned equivalence with Mathlib's
`MonoOver.congr`, subobject thin skeleton, and order-hom congruence. The cyclic
return equivalence itself remains required to construct that equivalence in
`sheetReturnExactFunctor`.

## Where the brief, the DAG or earlier work was wrong

The staged dependency declarations are present, but joining their concrete
sheet coordinates, cyclic fixed-pair categories and normalized power transports
requires substantial interface glue. The delivery states those strict argument
parts without renaming the whole original theorem. Purity, subobjects, quotient
weights, chain endpoints and both directions of mixedness are proved explicitly.

The source/ledger discrepancy at session start is described above; it does not
justify counting the three earlier normalization proofs twice. No new mathematical
counterexample or statement dispute was found. Small cases checked against each
new step are m=1, r=0 (one positive block), zero stalks, the empty scheme,
repeated subobject terms and length-zero filtrations. The assembly does not use
nonzero eigenvectors on zero stalks, strict inclusions or positive chain length.
No new dependency path returns to the parent item.

## New nodes

`def-zl-sheet-return-data` owns the extracted, unchanged concrete definitions and
three proved well-definedness/normalization lemmas in ConstantExtensionReturnData.
It carries no hole and introduces no chosen object.

`lem-zl-sheet-return-exact-functor` is original step 1: compose sheet coordinates
and cyclic return, checking the actual carrier/structure normalization. Its
conclusion is independent of local operators and weights.

`lem-zl-sheet-return-transport-comparison` is original steps 3--7 before common-stage
descent: ordered factor/block induction, whole-tower realization, rational descent,
naturality and finite coefficient compatibility. It asserts no existence of R,
local common-stage conjugacy, weights or filtrations.

`lem-zl-sheet-return-local-spectra` is original steps 2, 7--9 before weights:
residue-field degree/cardinality, common-stage descent of the assumed rational
comparison, arbitrary residue-embedding conjugacy and equality of eigenvalues.
It constructs no return functor and contains no filtration or mixedness claim.

All four nodes lie in the same chapter and unit as the parent. The change record
is `coord/changes/A9-sheet-return-comparison-interface.md`.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
