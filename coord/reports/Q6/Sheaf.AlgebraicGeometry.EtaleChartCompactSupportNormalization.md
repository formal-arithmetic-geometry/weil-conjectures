## What changed

Proved `AlgebraicGeometry.Etale.etaleChartCompactSupportNormalization` in its assigned
module. The definition and theorem signature are unchanged. The proof establishes
coefficient finiteness, annihilation and invertibility; installs the Noetherian,
finite-type, separated and compactification consequences; uses finite direct-image
exactness for the closed immersion; and assembles exactly the specified unbounded
comparison. The refinement square is a componentwise consequence of the existing
comparison cocycles.

Updated the assigned DAG node's proof, proof dependencies and proof origin to the
actual route. Removed obsolete tool-use approvals, preserving the order of those
still used. There are no new modules or nodes, and no definition or statement repairs.
The public-import change is recorded in
`coord/changes/q6-etale-chart-compact-support-imports.md`.

Removed unused direct imports, including the three public imports listed below.
`tools/downstream.py` reports zero downstream modules and no external declaration
users, so no consumer adaptations are necessary. The definition itself only uses
constants retained by the remaining public imports. No source-library file changes.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Etale.etaleChartCompactSupportNormalization`
(node `lem-pur-etale-chart-compact-support-normalization`). Original count: 1;
remaining count: 0; holes added: 0; statements split off: 0. The module's definition
contains no holes. This is a complete proof from existing library declarations,
not a decomposition. Existing imported results retain their own axiom status.

Validation: single-file server compilation of the completed proof succeeded;
final import-pruned compilation passed cleanly in 13.2 seconds. The delivery
tool records the server preflight result.

## No longer needed

The proof does not need the quasi-finite proper-support construction: finite
closed direct-image exactness and the existing proper derived comparison suffice.
The open adjunctions already exist, and the normalized isomorphism is required
literally as a composite of existing maps, so no new homotopy/localization descent
or separate source-open normalization proof is needed. Scheme-level typeclass
instances also avoid expanding affine-cover and fibrewise arguments.

Removed direct imports (many remain transitively available through retained imports;
this is local pruning, not a claim that these modules can be withdrawn globally):

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`.
- `Mathlib.CategoryTheory.Localization.Predicate`.
- `Mathlib.NumberTheory.Padics.PadicNumbers`.
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`.
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle` (public import).
- `Sheaf.AlgebraicGeometry.OpenSourceComposition` (public import).
- `Sheaf.AlgebraicGeometry.ProperSupportSheafComposition`.
- `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` (public import).
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
- `WeilConjectures.Compactification.Dense`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.

Removed from the node's proof dependencies:

- `def-weil-finite-type-morphism`.
- `lem-amb-compact-support-open-source-composition`.
- `lem-cbc-proper-support-sheaf-composition`.
- `lem-sfb-quasifinite-compact-support-exact`.
- `lem-weil-pbc-closed-immersion-base-change`.
- `lem-weil-pbc-localization-universal-property`.
- `lem-weil-pbc-termwise-adjunction-homotopy`.
- `lem-weil-valued-dvr-finite-quotients`.
- `pqf-def-quasifinite`.
- `pqf-lem-affine-open-locnoeth`.
- `prop-weil-pbc-inverse-image-modules-exact`.

Removed obsolete top-level tool-use approvals:

- `lem-amb-compact-support-open-source-composition`.
- `lem-cbc-proper-support-sheaf-composition`.
- `lem-sfb-quasifinite-compact-support-exact`.
- `lem-weil-pbc-closed-immersion-base-change`.
- `lem-weil-pbc-localization-universal-property`.
- `lem-weil-pbc-termwise-adjunction-homotopy`.
- `lem-weil-valued-dvr-finite-quotients`.
- `pqf-lem-affine-open-locnoeth`.
- `prop-weil-pbc-inverse-image-modules-exact`.

The node's statement dependencies remain unchanged: they record the original
mathematical normalization terminology. No node, module or unit-route step is
withdrawn. The containing unit `sk-thm-purity-transport` and its realized steps
are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan unnecessarily reconstructs exactness through quasi-finite
proper-support functors and reconstructs derived open adjunctions. Those APIs
already exist. The actual statement's final refinement equation requires only
the pairwise comparison cocycle and inverse cancellation; it does not require
reproving all general composition/base-change coherence.

The complement equality and positivity of the characteristic are retained as
original hypotheses. The proof works without using them: the open embedding
alone proves the needed geometry of W, and characteristic unequal to ell with
p not equal to one suffices for invertibility. Empty charts, r=0 and zero global
section rings require no extra assumptions.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
