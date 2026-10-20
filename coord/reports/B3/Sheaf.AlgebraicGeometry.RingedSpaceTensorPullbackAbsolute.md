## What changed

Restored the quarantined Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute
as a public compatibility import of the adopted WeilConjectures module. This
repairs the reproduced unknown changeOfRings, changeOfRingsHom and
IsAcyclicTensorKFlat failures while using the existing proved theorem once.
The quarantine archive and every source-library declaration remain untouched.

Updated lem-pc-ringed-space-tensor-pullback-absolute's Lean attachment to the
canonical source declaration and verbatim type. Its proof now records the actual
assembly from q3-ringed-space-tensor-pullback-left-derived and
q3-ringed-space-tensor-pullback-absolute-postcomposition. Their existing proofs
retain the K-flat resolution route; no unit statement or proof step is bypassed.

Validation: lcompile.py reproduces the archived failure, then compiles the repaired
wrapper and a full-signature compatibility probe together in import order. The
probe reconstructs the archived K-flat predicate and applies the canonical theorem
directly to the entire old type. The theorem's axioms are exactly propext,
Classical.choice and Quot.sound. A standalone probe initially used the published
old wrapper; the successful paired compile explicitly uses the repaired sandbox
wrapper. No consumer is edited: the four quarantined consumers and two further DAG
parents are recorded in the change record.

Change record: coord/changes/B3-tensor-pullback-absolute-upstream.md.

## Proved and sorry left

Assigned zero-hole sync repair. Archived item: zero sorry. Restored item: zero
sorry. Holes closed: zero; holes added: zero; split off: zero. There are no sorry
declarations in this delivery.

The re-exported AlgebraicGeometry.RingedSpace.exists_absolute_leftDerived_tensorModulePullback
(lem-pc-ringed-space-tensor-pullback-absolute) is fully proved, with no sorryAx in
its axioms. This delivery repairs visibility and duplicate ownership, not a new
mathematical proof or decomposition.

## No longer needed

The duplicate local theorem body and these archived direct imports are replaced
by the canonical public import:

- Sheaf.Paper.DerivedHomMayerVietoris
- Sheaf.Algebra.Homology.KFlatPullback
- Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
- Sheaf.Algebra.Homology.DerivedChangeOfRings
- Sheaf.Algebra.Homology.KFlatResolution
- WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
- Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux

The former direct node dependencies lem-pc-kflat-resolution,
lem-pc-kflat-pullback-preservation, lem-pur-derived-change-of-rings and
lem-pur-left-derived-from-kflat-class are represented below the two auxiliary
results rather than repeated as the parent proof's direct dependencies. They
remain needed by that route. No module or DAG node is withdrawn or claimed as
globally pruned; the unit route stays intact.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a proof obligation, but the assigned rework is a
zero-hole import repair after adoption upstream. Adding visibility imports alone
would preserve a duplicate public theorem; the source already contains the
complete statement and proof. The stale attachment used IsAcyclicTensorKFlat,
whose body is identical to the source IsKFlatTensor. Re-exporting and updating the
attachment preserves the mathematical statement with no added hypothesis or
weakened conclusion. The archived consumers remain needed and are preserved.

Mathlib searches were run through msearch.py: LeanFinder and LeanSearch returned
underived pullback constructions, Loogle did not recognize the derived-functor
identifier, and grep found no exact Mathlib theorem. The exact proved match was
found directly in lean/WeilConjectures, so no new node is required.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
