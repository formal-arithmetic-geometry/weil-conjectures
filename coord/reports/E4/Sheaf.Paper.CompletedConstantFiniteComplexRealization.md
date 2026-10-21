## What changed

Replaced the assigned theorem's `sorry` with a complete Lean combination of the module-completion model, a finite-free tensor calculation, and the already proved finite-ring profinite inverse-image theorem. The theorem signature is unchanged.

Proved the algebraic resolution step using the Noetherian pseudo-coherence criterion and projectivity, rather than rebuilding the downward free resolution. Proved preservation of quasi-isomorphisms by lifting complexes to the abelian category of finite modules and using the exact finite realization. Constructed the scalar map from its evaluation cone. Constructed the actual quotient-module tower and proved its linearity, naturality, identity and composition laws from the limit projections. Constructed the relative coefficient isomorphism and proved its required finite projections. The natural comparison is the inverse localized resolution, followed by the K-flat counit and the finite-free tensor isomorphism. Proved the universal derived tensor tower independently: tensor descends to homotopy, the cone criterion and a K-flat resolution prove invariance under K-flat quasi-isomorphisms, and resolving-class essential constancy plus the pointwise Kan bridge give the universal counit. Precomposition by the homotopy quotient transfers it to complexes without imposing a triangulation on the diagram category.

Moved all existing definitions and structures, with exactly the same data and signatures, into `Sheaf.Paper.CompletedConstantRealizationData`; the assigned module publicly re-exports them. The two independent source calculations can therefore be stated without an import cycle. The change record contains a body-by-body equality check and the 239 active transitive importers and two quarantined consumers; no consumer adaptation is required.

Validation: `lcompile.py --all` compiled all five delivered Lean modules with no errors or warnings. The derived-tower module took 23.4 seconds and the assigned module 18.7 seconds, within the normal per-file limit. The assigned theorem signature was also compared verbatim with the repository source.

## Proved and sorry left

Closed the original syntactic hole in `AlgebraicGeometry.Scheme.completed_constant_finite_complex_realization`. Its proof compiles from the following two remaining holes; this is a decomposition, not an axiom-free proof of the full theorem. Original holes removed: 1. New holes added: 2. Net syntactic change: one additional hole before pruning.

- `AlgebraicGeometry.Scheme.completed_constant_module_model` — `lem-weil-pbc-completed-constant-module-model`: the sectionwise finite-module tensor/limit comparison, exactness and local lisse model.
- `AlgebraicGeometry.Scheme.completed_constant_resolution_tensor_calculation` — `lem-weil-pbc-completed-constant-resolution-tensor-calculation`: the finite-free K-flatness and chain-level tensor comparison for the supplied actual quotient tower. The universal derived tensor tower is completely proved separately.

Both are distinct source arguments, strictly below the original statement. Each has its own module, node, source and complete natural-language proof; each proof is exactly `by sorry`. The assigned module, data module and derived-tower construction have zero holes. There are no new axioms and no holes in definitions. Private helpers fully prove the quotient tower, evaluation compatibility, finite-free resolution existence, preservation of quasi-isomorphisms, assembly through the K-flat counit, the scalar map, and the finite-ring pullback comparison. The additional public theorem `AlgebraicGeometry.Scheme.completed_constant_derived_tensor_tower` is fully proved from the library and supplies the universal derived tower for every module diagram.

Edge cases checked mathematically: the zero scheme, zero ring, I = 0, I = top, and the zero module or complex. The module statement does not require finite underlying quotient sets; Noetherianity suffices there. The relative argument uses the finite quotient-set hypothesis only to apply the existing profinite coefficient theorem. Coefficient restriction in the tensor calculation is along an isomorphism, so it preserves exactness, tensors and K-flatness. Neither statement discards Tor in a nonregular quotient.

## No longer needed

The following old proof imports are absent from the delivered modules (the public API imports moved to the data module are retained, not counted as pruning):

- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `WeilConjectures.Algebra.Homology.BoundedFlatKFlat`
- `Mathlib.Algebra.Module.FinitePresentation`
- `Mathlib.RingTheory.AdicCompletion.LocalRing`
- `Mathlib.RingTheory.AdicCompletion.Completeness`
- `Mathlib.RingTheory.AdicCompletion.Algebra`
- `Mathlib.RingTheory.Noetherian.Defs`
- `Sheaf.Paper.ConstantModuleSectionProperties`
- `WeilConjectures.RingTheory.FiniteFreeResolution`
- `WeilConjectures.RingTheory.FiniteModuleComplete`
- `Mathlib.RingTheory.AdicCompletion.Basic`
- `Mathlib.RingTheory.Finiteness.Defs`
- `WeilConjectures.RingTheory.LimitFlatModules`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.Paper.ConstantCompletionEquivalence`

The following original proof dependencies are no longer directly needed on this branch (definitions such as inverse image and K-flatness remain in the statement/data dependencies):

- `lem-pc-module-bounded-flat-kflat`
- `lem-weil-pbc-constant-completion-equivalence`
- `lem-weil-pbc-finite-free-resolution-noetherian`
- `lem-weil-pbc-noetherian-submodule-finite`
- `lem-weil-pbc-ringed-topoi-derived-pullback`
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`
- `lem-weil-pbc-ringed-topos-flat-module-pullback`

The source statement `ConstantRealizationDerivedScalarExtension` was also inspected: it supplies constant scalar comparisons but leaves their chain-level tensor formulas and cross-coefficient restriction identifications as separate assertions. It does not directly construct the required completed-ring quotient tower.

The direct relative flat-pullback and balancing detour is replaced by the already proved profinite coefficient isomorphism. The direct finite-free resolution and Noetherian-submodule construction is replaced by the proved pseudo-coherence criterion. The constant-completion derived equivalence is not used. These are branch-level pruning claims only; no declaration or source-library module is deleted, and modules still used elsewhere remain in the library. Constant-section, flat-limit, completion and K-flat dependencies still needed by the two source calculations remain in their nodes.

## Where the brief, the DAG or earlier work was wrong

The node's Lean note says `isMonoidal_W_independentCoefficients` is retired, but the current declaration exists and is proved; the original module compiles with it. No API replacement was necessary. The original eight-step proof remains a valid mathematical plan, but the existing pseudo-coherence and profinite coefficient theorems give shorter routes through its resolution and relative-coefficient steps. The unit and its amplification proof (c) are retained unchanged. There is no disputed statement. Preflight identified two additional quarantined consumers of the derived-category abbreviation; both are now listed in the change record, with their attachments and dependencies preserved.

## New nodes

`def-weil-pbc-completed-constant-realization-data` attaches the unchanged realization interfaces to their independent data module. No mathematical definition changes.

`lem-weil-pbc-completed-constant-module-model` is the finite-module completion comparison of Tags 0912, 093J--093M and 09BT. It has no derived-complex conclusion.

`lem-weil-pbc-completed-constant-resolution-tensor-calculation` is the finite-free chain-level quotient calculation of Tags 06YN, 06YT and 06YU. The upper theorem separately proves the resolution exists, preserves its quasi-isomorphism, and combines the natural isomorphisms.

`lem-weil-pbc-completed-constant-derived-tensor-tower` proves the generic derived tensor tower, including its universal cochain counit and computation on every K-flat complex, using Tags 06XN, 06YT and 06YU. It has no holes.

Change record: `coord/changes/Y2-completed-constant-realization-data.md`.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
