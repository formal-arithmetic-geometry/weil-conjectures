## What changed

Proved `AlgebraicGeometry.Scheme.noetherian_proper_directImage_bounded_coherent`
from the existing proper-support theorem `directImage_isBounded_coherent`.
Properness makes the source locally Noetherian. Coherent source cohomology is
quasi-coherent of finite type; its scheme-theoretic support is a closed subscheme,
proper over the base by composition. This supplies the existing theorem's support
hypothesis. Its conclusion is exactly the original conclusion, for the independent
derived localizations already supplied in the statement.

Reused `finite_sections_higherDirectImage` for the public affine finiteness corollary.
Removed three unused private helpers and updated the target's proof plan and docstring.
Both public theorem signatures and all public imports remain identical. The module
compiles without warnings using `lcompile.py`. Both unchanged direct importers,
`Sheaf.AlgebraicGeometry.DescentFirstProperFlatCechModel` and
`Sheaf.AlgebraicGeometry.ProperFlatSingleOpenPseudoCoherent`, also compile against
the changed module in the scratch sandbox. Each compile was within the 60-second limit.

## Proved and sorry left

The original module had two direct holes:

- Proved `AlgebraicGeometry.Scheme.noetherian_proper_directImage_bounded_coherent`
  (node `lem-pc-noetherian-proper-bounded-coherent-image`).
- Pruned `AlgebraicGeometry.Scheme.finitePresentation_of_coherent`, an unused private
  helper, instead of proving it.

One original hole is proved and one is pruned; no holes are added or split off.
Actual remaining hole count: zero. The retained
`AlgebraicGeometry.Scheme.Modules.finite_sections_proper_on_affine` remains proved,
now from the source library's proper finiteness theorem. `#print axioms` for both public theorems reports exactly `propext`,
`Classical.choice`, and `Quot.sound`; neither theorem transitively uses `sorryAx`.

## No longer needed

Removed private declarations:

- `AlgebraicGeometry.Scheme.finitePresentation_of_coherent` (the unused hole).
- `AlgebraicGeometry.Scheme.Modules.finite_sections_proper` (duplicate devissage).
- `AlgebraicGeometry.Scheme.Modules.finitePresentation_higherDirectImage_proper`
  (unused affine-local reconstruction).

Removed imports:

- `Mathlib.Data.Int.Interval`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum`
- `Sheaf.AlgebraicGeometry.CohomologyFiniteExtension`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh`
- `Sheaf.AlgebraicGeometry.FinitePresentationIntegralFiltration`
- `Sheaf.AlgebraicGeometry.IntegralIdealProperCohomology`
- `Sheaf.CategoryTheory.HalfPlaneWeakConvergence`
- `Sheaf.CategoryTheory.TruncationHypercohomology`
- `WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum`
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`
- `WeilConjectures.CategoryTheory.HalfPlaneWeakConvergence`
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`

Removed direct proof dependencies from this node:
`def-pc-derived-direct-image`, `lem-pc-cohomology-sections-affine-base`,
`lem-pc-derived-direct-image-bounded-below-qcoh`,
`lem-pc-e2-cohomology-finite-extension`,
`lem-pc-e2-finite-presentation-integral-filtration`,
`lem-pc-e2-integral-ideal-proper-cohomology`,
`lem-pc-higher-direct-image-local-vanishing`,
`lem-pc-sections-higher-direct-image-quasi-coherent`,
`lem-sp-half-plane-weak-convergence`,
`lem-weil-pbc-coherent-modules-kernel-cokernel-sum`, and
`thm-sp-truncation-e2`. Some remain transitively needed by the imported proper-support
result or the public statements. This delivery does not assert that they are globally
unreachable. `pqf-lem-coherent-ft-locnoeth` remains a direct dependency.

## Where the brief, the DAG or earlier work was wrong

The old docstring said the proper-support theorem's module could not be imported
because it reached the arbitrary-base pseudo-coherence item. The current source
import graph no longer has that cycle: `import_direction.py may` accepts the import,
and the single-file compiler accepts it. Reusing that theorem preserves the existing
unit's proper-coherence argument, while removing its duplicate implementation here.
The current unit record's `realized` statement and step lists are empty; no prescribed
realized node is bypassed.

The source library now already proves proper affine finite cohomology in
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex` using
`hasFiniteH_of_isProper`; its old name does not imply a dependency on arbitrary-base
finite-free models. The public corollary needs no added finite-presentation assumption
on the proper morphism.

Lean Finder and Mathlib grep found no matching bounded coherent proper-image theorem.
Loogle did not resolve the unqualified geometric name. The decisive shorter route
was the existing project theorem found by `rg`, whose type and proof were read.

Delivery files touched: the item module, its existing node, and this report.
Scratch verification files: `scratchpad/ProofAxioms.lean` and the three module copies
under `scratchpad/consumers/lean/`; these are excluded from the delivery.
No new modules,
definitions, statements, nodes, change records, or forced adaptations are introduced.

## Second reading by B4

1. **Interface — pass.** Compared the delivered module with the repository version.
The signatures of `finite_sections_proper_on_affine` and
`noetherian_proper_directImage_bounded_coherent` are unchanged byte for byte; only
proofs, proof-only imports, private helpers, and docstrings differ. No definition or
target statement was changed. The existing public-import change record is unrelated to
the theorem interfaces and its retained import path is intact.

2. **Proof — pass.** Compiled the module with `lcompile.py` both alone and with the
sandbox import order. The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`,
or `implemented_by`. A scratch `#print axioms` check gives exactly `propext`,
`Classical.choice`, and `Quot.sound` for both public declarations. The proof uses the
proper-support theorem with a support supplied by the coherent finite-type
characterization; the local Noetherian hypothesis is registered for that theorem.

3. **Split statements — pass.** No statement was split off and no new node was added.
The support argument is a direct specialization of the existing proper-support result,
and the affine finiteness corollary is a direct application of the existing
`finite_sections_higherDirectImage` theorem. No hollow definition or arbitrary witness
was introduced.

4. **Shortest route and pruning — pass after repair.** The existing
`directImage_isBounded_coherent` theorem is strictly more general and closes the target
after constructing proper supports, so the former local spectral-sequence and integral
ideal devissage are unnecessary. The old duplicate private helpers and their imports
are removed. I also removed the stale affine-finiteness step and `lem-pc-coherent-hi`
from the target node's `proof` and `proof_deps`, because that corollary is proved in the
same module but is not used by the target theorem. The unit record has empty
`realized` lists, so no required unit step is bypassed.

5. **DAG — pass.** The revised node's proof steps now match the target proof exactly:
coherence gives quasi-coherent finite-type cohomology and proper scheme-theoretic
support, then `directImage_isBounded_coherent` gives the conclusion. Its dependency set
is exactly the union of the step uses. Existing search records document the failed
Mathlib/Loogle matches and the repository theorem that supplies the shorter route.

I changed the DAG proof/dependency metadata to remove that stale unused step and made no
Lean proof changes.
