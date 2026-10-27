## What changed

Reduced `WeilConjectures.SystemTensorMate.tensorPresentationIdentification` to two
independent, strictly partial construction steps. `semilinearPresentation_realization`
constructs operations realizing the supplied source calculus, without comparing them to
an arbitrary target package. `tensorPresentationCore_nonempty` compares two normalized
operation packages through their tensor/pullback and adjunction normalization, without
assuming any projection or open tensor mate equation.

The item proves the missing mate consequences using private generic category lemmas
and instantiates them with the core comparison. `projection_comparison` expands
the proper-adjunction transpose and substitutes unit, counit, tensor naturality and mu.
`delta_inverse_comparison` applies the open Hom bijection, transports its transpose by
the open unit equation, and rewrites inverse mu and tensor naturality.
`delta_comparison` cancels the inverse open tensor map. `completeComparison` assembles
all original fields, and the theorem combines this with the source realization.

Extracted the comparison interfaces needed by the construction steps to the publicly re-exported
`SystemTensorPresentationData` module so the two new statement modules can be imported
without a cycle. This extraction is needed for the reduction, not for a time limit.
The separate Realization interfaces remain in the item. The full comparison extends
the new core instead of repeating its long field telescope; its inherited field types,
universes and normalization equations are unchanged. Theorem signatures and other
data bodies are preserved. The retained realization record names its exact square
proposition as squareCompatibility so the kernel need not repeatedly expand the
large preceding field telescope; its equation and binders are unchanged.
No source-library module or target statement was changed.

Validation: launcher single-file compilation passed for all four delivered modules
in import order, with no errors or warnings in the exact packet. Both generic mate
proofs also compiled in small category-only scratch files. The final delivery tool
runs the mandatory server preflight.

## Proved and sorry left

Original module: two named theorem holes. One is closed by a decomposition, not an
independent proof of the underlying construction: `tensorPresentationIdentification`.
Two new named theorem holes are added, so this delivery has net one additional hole.
The real Lean work proves the projection mate and both open tensor consequences from
the strictly smaller core data, rather than renaming the original theorem.

Every remaining hole in this packet:

- `WeilConjectures.SystemTensorMate.tensorPresentationCore_nonempty`, node
  `lem-pur-system-tensor-presentation-core-existence`, in
  `Sheaf.Paper.SystemTensorPresentationCoreExistence`.
- `WeilConjectures.SystemTensorMate.semilinearPresentation_realization`, node
  `lem-pur-system-tensor-semilinear-realization`, in
  `Sheaf.Paper.SystemTensorSemilinearRealization`.
- `WeilConjectures.SystemTensorMate.Realization.properOpenFactors`, unchanged, node
  `lem-pur-system-tensor-presentation-identification`, in the item module.

No hole occurs in a definition or a private helper. The witnesses of the two new
existence statements are used only inside the proof of the original proposition.

## No longer needed

No module or DAG dependency is globally pruned: the separate `properOpenFactors` hole
still has the original universe-transport plan and its dependencies. No withdrawal
is claimed merely from the zero current Lean importers; both unfinished DAG parents
retain this item and the unchanged theorem signature.

The item's old proof-only imports are replaced by the two new step modules. The
interface module needs none of the following old proof-only imports:
`Sheaf.Paper.CoefficientRingedSequenceSite`, `Sheaf.Paper.SemilinearSystemModels`,
`Mathlib.CategoryTheory.Localization.Predicate`, `Mathlib.CategoryTheory.Adjunction.Mates`,
`Sheaf.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat`,
`Sheaf.Algebra.Homology.CochainTensorModelRigidity`,
`Sheaf.CategoryTheory.ExactPostcompositionKInjectiveDescent`,
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
`Sheaf.Paper.SemilinearOperationsExistence`, `Sheaf.Paper.SemilinearGeometryDerived`,
and `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
The new construction-step modules import only their statement interface. Their
documented future proofs still name the generic tools in the DAG; those imports are
left for the workers proving the steps.
The item's public prerequisite imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The nine-step plan omits the typed algebra that turns its
comparison data into the two mate consequences; this delivery supplies that algebra.
The source interfaces had to move to a dependency module to state independent steps
without an import cycle. Profiling then motivated the core inheritance refactor; it
removes duplicated field telescopes while keeping every normalization condition. The source-realization step is distinct from the generic
comparison of normalized operation choices. The separate ULift theorem is not proved
by an identity reindexing and remains explicitly open.

Edge cases: the mate algebra uses only naturality, units/counits, invertible mu and
invertible open tensor maps. It includes zero objects, empty or whole opens, identity
maps, and arbitrary unbounded systems with nonflat quotient transitions. The new
existence steps retain all original universes and all K-flat and section normalizations;
no cartesianness, flat-transition or boundedness hypothesis was introduced.
The blueprint unit and its realization record are unchanged.

## New nodes

`def-pur-system-tensor-presentation-core` owns the extracted original source and tensor interfaces and
the new strictly partial core interface in `SystemTensorPresentationData`. It introduces
no chosen data and states no existence claim.

`lem-pur-system-tensor-presentation-core-existence` states Steps 1--7 for two normalized
operation packages, omitting the projection and both open tensor mate equations. Its
proof in words uses the existing adjoint uniqueness, localization, exact-equivalence
K-flat descent, K-injective normalization and cochain-rigidity declarations.

`lem-pur-system-tensor-semilinear-realization` states the independent source-realization
paragraph: retain the supplied a W.systems, compare actual geometric inverse-image
coefficients and localization via their section-normalized adjunctions. It contains
no arbitrary target package, final comparison or universe-lift realization clause.

All three record LeanSearch, Loogle/LeanFinder and grep searches. The search found the
generic Mathlib adjoint uniqueness API, but no concrete strict-system comparison.
The source is the agent comparison in the original node, using the Stacks 0B56
projection transpose and 0E8I open tensor normalization. The change record is
`coord/changes/W7-system-tensor-presentation-interfaces.md`.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
