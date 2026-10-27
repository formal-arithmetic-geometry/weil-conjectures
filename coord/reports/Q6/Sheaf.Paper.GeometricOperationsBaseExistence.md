## What changed

Replaced the hole in `Sheaf.Paper.GeometricOperationsBaseExistence` by an assembly proof with the original theorem statement unchanged. The proof explicitly transports the coefficient rings through inverse image and constructs their transition maps using the addition, multiplication and unit graphs. It obtains the target system calculus from `semilinearSystemData` and resolution instances from the Grothendieck abelian module and system categories. Both derived adjunctions are the canonical derived adjunctions of the ordinary ones. A proved private helper derives the two required K-injective transpose formulas from the derived unit factorization and right-derived-unit naturality.

The proved new module `GeometricCoefficientTower` exposes the coefficient transport step as `geometricCoefficientTower`, using concrete transported ring objects and their graph laws. Its theorem is independent of all source/target derived calculus data.

Three further new modules isolate strictly separate remaining parts: ordinary termwise realization (`GeometricOrdinaryRealization`), right-derived evaluation and scalar comparisons (`GeometricDerivedEvaluation`), and localization of the pure-tensor comparisons (`GeometricTensorLocalization`). The ordinary interface contains actual horizontal transitions and identity-on-section comparisons, but no derived operation. The other two interfaces take that ordinary realization and the already chosen source and target calculi. Exact left evaluation and the passage from ordinary data to `GeometryBase` are implemented definitions, without holes. The upper proof combines their conclusions into every field of `Geometry`.

Remote `lcompile.py --all` compiled all five modules; the assigned module took 34.7 seconds, within the 60-second delivery limit. Two style warnings in that module were corrected before the delivery check.

No existing definition, public import, declaration signature, target, or consumer interface is changed. The new interfaces contain no choice from an unproved existence theorem. All new choices from the split statements occur inside theorem proofs. The source library is unchanged.

## Proved and sorry left

Closed the original syntactic hole in `WeilConjectures.SemilinearSections.semilinearGeometryBaseExistence` (one original hole). Its proof depends on the following three new holes, so this is a decomposition, not a completed proof of the geometric existence theorem; the net change in syntactic holes is +2 before reachability accounting.

- `WeilConjectures.SemilinearSections.semilinearGeometryOrdinary`: node `lem-coef-semilinear-ordinary-geometric-realization`.
- `WeilConjectures.SemilinearSections.semilinearGeometryEvaluation`: node `lem-coef-semilinear-geometric-derived-evaluation`.
- `WeilConjectures.SemilinearSections.semilinearGeometryTensor`: node `lem-coef-semilinear-geometric-tensor-localization`.

These are the only `sorry`s in the delivery. The new public theorem `WeilConjectures.SemilinearSections.geometricCoefficientTower` has a complete proof and closes node `lem-coef-geometric-coefficient-tower`. Each is an entire public theorem body, with a source and a proof in words. The original module has zero holes. The coefficient-tower construction and canonical transpose helper are proved; neither is a renamed existence assumption. The exact localization definition and `GeometryOrdinary.toBase` are also implemented.

Edge cases checked in the mathematical statements: a constant coefficient tower, identity geometric morphism, zero module systems, m=n scalar restriction, and n=0 singleton extension. No surjectivity or flatness of the transition ring maps is assumed. The singleton argument uses derived scalar extension below n, not ordinary scalar extension of an arbitrary complex. Derived evaluation is not assumed to preserve K-injectives or detect equality of morphisms. The tensor comparison is normalized on actual signed total complexes before localization.

## No longer needed

No original Lean imports were removed, and no module is withdrawn. The original file only publicly imported `Sheaf.Paper.SemilinearGeometryOps`; that import remains.

The original proof-only dependency on `def-coef-semilinear-geometry-ops` is unnecessary for assembling `Geometry`; it remains a statement dependency and its original public import is retained.

The original node's direct proof dependency `lem-weil-pbc-ringed-projection-mate-exact` (`Sheaf.Paper.ProjectionMateExact`) is unnecessary here: this obligation only constructs inverse-image tensor comparisons, while projection mates are defined later by `SemilinearGeometryOps`. The stronger projection package is not imported.

The original direct dependency `lem-weil-pbc-ringed-topoi-module-adjunction` (`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`) is replaced by the ordinary-realization step. Its equal-site-universe interface does not supply the normalized horizontal system operations required here; the lower ordinary node records the mixed-universe independent module adjunction and the underlying transport argument instead. The old module remains in the library and may remain needed by other nodes.

The independently sized scalar inverse-image theorem `lem-per-independent-scalar-inverse-image` fixes the ordinary coefficient comparison and its unit; it is recorded as a generic lower tool for derived evaluation. The system singleton geometric-pullback and scalar-restriction-normalization nodes are lower tools for the derived-evaluation argument, not substitutes for the full existence theorem. No unit statement or proof step is bypassed. No whole-library pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The old node compressed ordinary construction, derived right evaluation, scalar mates and normalized tensor localization into one sentence. The listed generic module-adjunction and projection-mate results alone do not supply the actual horizontal transitions, identity-on-section ordinary evaluations, singleton argument for right evaluation, or compatibility with the specified system tensor models. The reduction exposes these separate steps rather than assuming that derived evaluation preserves K-injectives.

The existing `SystemGeometricOrdinaryComparison` and `SystemSingletonGeometricPullback` interfaces use `StrictRingSystem`, `SystemScalarAssignment` and their chosen derived lifts. The present statement instead fixes `SemilinearSections.Data`, its actual `evaluation` functors, coefficient maps and canonical derived adjunctions. Their conclusions cannot be applied directly to these fields; the canonical ringed-topoi tensor API likewise identifies the site and coefficient universes, whereas this statement keeps them separate; the new leaves record the required construction and normalization in this interface. This is an interface gap, not an objection to using dependencies that still have holes.

A transitive DAG audit also finds an existing dangling reference from `lem-sfb-ringed-derived-identity-comparison` to `def-weil-pbc-localization-universal-property`. No new node directly cites the missing id, and this delivery does not alter that existing lower node.

The blueprint-ancestor command on the assigned node returns no ancestor because its `created.item` is a module name. Following the existing mathematical provenance through the geometric-operations, operations-existence, derived-sections and finite-diagram nodes leads to blueprint node `prop-coef-integral-exceptional-adjoint`. The new nodes record that ancestor and the intervening nodes. The original node's immutable provenance is retained.

## New nodes

`lem-coef-geometric-coefficient-tower` is proved in `GeometricCoefficientTower`. It constructs the transported coefficient ring objects and algebraic inverse images and proves compatibility of all adjacent transition maps. Its implementation reuses the concrete, proved private ring/module transport and graph-bundling helpers of `CochainCompositeAlgebraic`; it does not assume that module's composite-existence theorem. The new node exposes precisely this coefficient-tower result, rather than treating a helper from a broader node as that node's statement.

`lem-coef-semilinear-ordinary-geometric-realization` states the ordinary module and system construction for a supplied compatible inverse-image coefficient tower. It excludes all derived data, and its equality conditions fix that supplied tower and algebraic inverse images. Its source is Zheng Construction 4.1 and the paragraph before Lemma 4.10; the module-adjunction and transport arguments supply the ordinary step.

`lem-coef-semilinear-geometric-derived-evaluation` fixes an ordinary realization and source/target calculi, and supplies only right-evaluation, unit/counit and coefficient-transpose comparisons. Its proof uses the finite left singleton extension and conjugate adjunctions, together with normalized scalar extension. It does not construct ordinary operations or tensor comparisons.

`lem-coef-semilinear-geometric-tensor-localization` fixes the ordinary realization and both tensor models, and supplies only tensor comparisons and their ordinary/derived evaluation normalization. The proof is the balanced pure-tensor map, its signed total-complex extension, and K-flat localization uniqueness. It does not construct direct image, adjunctions, or scalar comparisons.

All four nodes retain the assigned chapter and unit. The mixed-universe module adjunction, coefficient scalar comparison, singleton/evaluation and K-flat descent nodes of other units are used as general categorical tools, not as alternative routes to a unit theorem. Their needed normalized system interface is not stated in this unit. Maintainer tool approvals are left to the maintainer; no `tool_uses` entries were added. Mathlib searches and the whole-blueprint search were performed; the search results supply general adjunction or tensor infrastructure, not these normalized strict-system statements. No change record is needed because no existing statement or definition was changed.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
