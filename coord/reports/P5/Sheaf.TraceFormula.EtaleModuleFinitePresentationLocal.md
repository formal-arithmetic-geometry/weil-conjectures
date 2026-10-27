## What changed

Proved AlgebraicGeometry.Scheme.Modules.etale_module_finite_presentation_local with
its original signature. Private proved helpers identify finite presentation on the opens/over
site and on the corresponding open subscheme. Adjunction uniqueness identifies tensor
pullback with ordinary pullback. The forward direction uses existing pullback preservation;
the reverse direction descends along the surjective étale map from the given open to its
open image. Mathlib's fppfTopology_le_fpqcTopology supplies the fpqc covering condition.
The DAG proof now records this implementation. No new modules or statements with holes.

Removed unused public imports and recorded their consumer check in
coord/changes/p5-etale-module-finite-presentation-local-imports.md.

## Proved and sorry left

Closed 1 hole: AlgebraicGeometry.Scheme.Modules.etale_module_finite_presentation_local
(lem-trf-etale-module-finite-presentation-local).
Added 0 holes. There are 0 sorry declarations left in the delivered module. The three
private helper theorems are fully proved. No split-off results.

Validation: server single-file compilation passed in 32.3 seconds with no errors or
warnings. The source-only import-pruning check passed. Delivery runs the independent
preflight, including compilation with axiom probes.

## No longer needed

Removed imports:
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators: redundant through Quasicoherent.
- Sheaf.AlgebraicGeometry.CoherentFiniteType: the theorem assumes quasi-coherence only.
- Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction: only the concrete upstream
  tensorPullback and existence of its adjunction are needed. Publicly import
  WeilConjectures.AlgebraicGeometry.TensorPullback instead.
- WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation: ordinary pullback
  preservation is already proved and available through the descent module.

Declared proof dependencies no longer needed by this proof:
- lem-pc-tensor-pullback-finite-presentation and its wrapper module above: reuse the
  ordinary-pullback preservation instance directly, with the same adjunction comparison.
- lem-weil-pbc-etale-covering-affine-refinement: Mathlib's existing fppf-to-fpqc inclusion
  packages the refinement argument for the singleton surjective étale map.
- pqf-def-coherent: no finite-type condition is used; quasi-coherence is already supplied
  by the existing sheaf module API.

No module is withdrawn, and no upstream declaration is changed or removed. The parent
and the unit route remain unchanged. These dependencies may still be needed elsewhere.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error. The DAG's explicit affine-refinement step is unnecessary
in Lean because Mathlib already proves fppfPrecoverage_le_fpqcPrecoverage and the topology
inclusion. The residue-field isomorphism is unused in both implications, as the original
DAG already observes; the hypothesis is preserved.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
