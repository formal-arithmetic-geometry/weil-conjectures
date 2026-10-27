## What changed

Replaced the sole proof hole of
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedAffineFree_presheaf_localDual`
with a complete Lean proof from strict substeps. Its statement, including the repaired
nonzero sheafification-image hypothesis, is unchanged. The existing swap-kernel proof is
preserved. No other existing Lean module or existing node is changed.

The proof extends a natural scalar test through the free-module universal property and
through the locally bijective sheafification unit on the slice. It writes the given section
as its finite Finsupp expansion, derives vanishing of each residue-field equality-class
coefficient sum from the assumption that all duals vanish, and applies the geometric
pattern cover. A proved finite-partition identity cancels the generators on that cover.
Naturality and sheaf separatedness then contradict the nonzero-image hypothesis.

The coefficient proof uses the already proved
`Scheme.discreteContinuousCoefficientIso` auxiliary interface, rather than the finite
extension completion theorem in the same existing module.

Three new modules isolate continuous-function coordinates, finite scalar interpolation,
and closed-pattern covers. These are independent parts of the parent argument, rather
than restatements of local dual detection. The interpolation conclusion only specifies
values of a natural scalar test on finitely many generators at one point. The pattern-cover
conclusion only supplies equalities of arrows and zero sums of scalar coefficients on a
cover; the proof assembling them into sheafified-module detection is in the assigned module.

Validation: `lcompile.py --all` compiled all four modules successfully, with no diagnostics:
coefficient model 8.5 seconds, interpolation 4.0 seconds, pattern cover 4.6 seconds,
and the assigned module 13.1 seconds. Every file is below the 60-second limit.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedAffineFree_presheaf_localDual`:
1 of 1 original holes. This is a decomposition, not a claim that its geometric dependencies
are axiom-free. The private lemmas `scalar_test_extends` and
`sum_smul_eq_zero_of_class_sums` are fully proved; the older `free_presheaf_swap_kernel`
remains proved.

Also proved
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedAffineCoefficientModel_exists`
from the existing discrete continuous-coefficient comparison, sectionwise limits, and a
proved compatible-residue lifting argument. The auxiliary `positiveLift_exists` proves
continuity of the p-adic lift using the compact residue-product embedding.

Remaining new holes (2 added; net original-minus-added hole count is -1):

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedAffine_fiber_interpolation`,
  node `lem-sfb-completed-affine-fiber-interpolation`.
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedAffine_pattern_cover`,
  node `lem-sfb-completed-affine-pattern-cover`.

Each new hole has its source, complete proof in words, and matching DAG node.
The finite-family and empty-scheme edge cases are addressed in the proof descriptions;
classes may merge on the boundary of a pattern stratum, and the cover lemma deliberately
requires only within-class equality, not an unchanged exact pattern.

## No longer needed

No original public import is removed: they are needed by the unchanged statement and
preserved swap-kernel proof. No existing module or declaration is withdrawn. The geometric
nodes `sk-def-pe-morphisms`, `lem-pe-spectral-components-profinite`, and
`lem-pe-clopen-restriction-canonical-localization` remain needed through the new substeps.
They are no longer direct steps of the assigned node: its updated proof dependencies are
the three substeps and module sheafification. No UNIT statement or realized proof step
is bypassed. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The repaired nonzero-image hypothesis is essential and is preserved. A free presheaf
section itself can be nonzero while its sheafification image vanishes; the earlier
swap-kernel counterexample remains valid. Also, class sums must be evaluated on
residue-field maps, rather than merely on underlying topological points of U.

The inherited blueprint coefficient paragraph does not itself contain this geometric
argument, as the W3 proof-origin record already notes. The new nodes explicitly take
their source from the finite-support, stage-test, and closed-stratum proof in the docstring
of `completedAffineFree_localDual_detect`. Their proof descriptions make the empty cases,
closure argument, and permissible merging of classes explicit.

## New nodes

`lem-sfb-completed-affine-coefficient-model`: natural sectionwise ring coordinates by
continuous p-adic functions. Its existence theorem is proved, including compatibility
with restrictions and removal of coefficient universe lifts. It contains no assertion
about a free module or its dual.

`lem-sfb-completed-affine-fiber-interpolation`: characteristic functions from finitely
many affine etale stages isolate one residue-field fiber class at a fixed point. This
is only a natural scalar test on the slice and does not claim sheafified-module detection.

`lem-sfb-completed-affine-pattern-cover`: zero pointwise class sums yield a covering
family on which within-class arrows agree and coefficient class sums vanish. It is the
closed-pattern descent step, independent of free modules and duals.

No change record is needed: existing definitions, statements, and interfaces are unchanged.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
