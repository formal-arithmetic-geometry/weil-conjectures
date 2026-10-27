## What changed

Kept the statement of `diagonalOrdinaryOrientationNormalization` unchanged. Wrote
its global assembly from one affine-restriction calculation: invert the prescribed
realization equation, transport it around the open/site-comparison square, descend
through the bounded-below comparison Hom bijection, and detect equality by
cohomology in degree `-2d` and jointly faithful sheaf restrictions.

The private Tate normal-form and sheaf-cover equality arguments reuse the proved
arguments of `BundleSectionOrientationMapExt`, specialized without its bundle target.
They construct the shifted-single normal form using flat Tate sheaves and prove
equality detection for the actual ordinary derived maps.

Added `DiagonalAffineCounitRestriction`. Its four data constructions are explicit
canonical functor comparisons, the coefficient-unit conversion, and the existing
coordinate counit followed by inverse source-etale locality. The square comparisons
and coordinate composite are irreducible to avoid
expanding large adjunction and site-comparison terms during kernel checking;
`unitChange` remains transparent so the given realization equation matches directly.
There is no witness chosen from mere existence and no hole in a definition.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurityFiniteSetting.diagonalOrdinaryOrientationNormalization`
(node `lem-pur-diagonal-ordinary-orientation-normalization`) by a complete assembly
from the strictly local geometric step below. Original holes: 1; closed: 1.

Added one hole:
`WeilConjectures.PurityFiniteSetting.diagonalAffineCounitRestriction`
(node `lem-pur-diagonal-affine-counit-restriction`). Its proof is exactly `by sorry`.
It states the DNC/vector-integration calculation on one affine target restriction,
with no global orientation and no global realization hypothesis. Its docstring and
node give the coordinate-difference/Rees calculation, integration normalization,
and counit-mate pasting argument. This is a decomposition, not a complete proof of
the geometric compatibility; the net hole count is zero.

No holes remain in the assigned module; one remains in the added module. The
normal-form, open-cover equality detection, pullback comparisons, and assembly
introduce no additional holes. Empty schemes and empty covers use jointly
surjective inverse-image conservativity. Rank zero uses the zero Tate tensor,
identity shift, and identity affine counit. The local lemma imposes no positive-rank,
nonempty-open, absolute-separatedness, or coefficient-flatness assumptions.

## No longer needed

The normal-form induction also no longer needs the signed twist-pullback node
`lem-asd-etale-finite-twist-pullback`: the nonnegative successor comparison is the
actual tensor-power equation (with a left unitor at zero). This node remains needed
elsewhere in the geometric argument.

Removed the proof import `Sheaf.Paper.DegreeZeroDerivedMapGluing` and the assigned
node's direct proof dependency `lem-pur-degree-zero-derived-map-gluing`. The proof
needs equality detection only, which follows from the existing cohomology Hom
bijection and jointly faithful restrictions on module sheaves. It constructs no
new global map and requires no general derived-map gluing theorem.

The assigned assembly does not directly use `Dnc.existsUnique_dncInvariance`,
`vectorBundlePurity`, `vectorBundleIntegration`, `tensorMateEtalePrecomp`, or the
Cartesian-coefficient theorem. These geometric dependencies belong to the new
affine calculation, where they remain recorded. No such node or module is claimed
globally unnecessary, and no source-library declaration is withdrawn.

`DiagonalOrientationRefinement` remains a public import for its `Chart`, `theta`,
`pull` and `tate` data, without invoking its existence theorem. The unit's diagonal,
DNC and vector-integration route is preserved. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies provide the DNC and vector integration normalizations
separately but no independent theorem identifies their composite with the
coordinate counit on one affine target restriction. Existing chart-factor results
cannot fill this role: import-direction checks report that both
`ChartDncVectorFactors` and `ChartDncNaturality` already reach the assigned module.
Importing them would close a cycle. The new local statement isolates precisely
this missing calculation; the global descent argument is implemented separately.

The initial assembly exceeded the compile limit. Profiling a restricted prefix
showed that elaboration was small and most time went to kernel checking and the
private-module linter waiting for those declarations to finish. The new explicit
comparison definitions were made irreducible. Mapped-inverse cancellation is
proved for arbitrary functors in the same file. The coefficient-unit
wrapper stays transparent to match the realization hypothesis. The nonnegative
Tate successor product uses the actual tensor-power equation rather than an
unneeded signed multiplication comparison.
Typed generic wrappers express the shift and flat-single comparisons directly
in the right-tensor API; this avoids repeated concrete bifunctor conversion.
The final assigned file compiled cleanly in 58.9 seconds, with no warnings.
The limit and transparency options were not relaxed.

## New nodes

`lem-pur-diagonal-affine-counit-restriction`, in
`dag/nodes/sec-smooth-purity/lem-pur-diagonal-affine-counit-restriction.json`, realizes
the coordinate calculation in Steps 1--2 and the canonicity paragraph of
`thm-pur-diagonal-dualizing-object.proof.md`. It records the complete local equation,
its explicit comparison data, three logged Mathlib searches, source and proof.
It is strictly smaller than the assigned theorem: it has one affine target open,
no global orientation, no realization premise, and no global equality descent.
There are no definition/statement repairs to existing declarations and no change
records or forced adaptations.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
