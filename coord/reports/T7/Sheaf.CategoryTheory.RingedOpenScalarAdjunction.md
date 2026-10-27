## What changed

Proved scalarExact, sliceExact, adjunctionGenerators and tupleAction in
Sheaf.CategoryTheory.RingedOpenScalarAdjunction without changing their signatures.
Added a private generic restriction-of-scalars exactness lemma and a proof-only import of
WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful. Exactness follows by
reflecting finite limits and colimits through the faithful forgetful functor to abelian
sheaves. The fixed slice unit is the prescribed summand injection; its counit formula
follows by evaluating the right triangle identity. The tuple action is definitional.

## Proved and sorry left

Closed four of the original five holes:
SheafOfModules.RingedOpenScalar.scalarExact,
SheafOfModules.RingedOpenScalar.sliceExact,
SheafOfModules.RingedOpenScalar.adjunctionGenerators,
SheafOfModules.RingedOpenScalar.tupleAction.

One original hole remains:
SheafOfModules.RingedOpenScalar.comparison
(lem-cbc-ringed-open-scalar-adjunction).
No holes were added or split off.

## No longer needed

No original imports, nodes or modules were removed. The original comparison route
and all its dependencies remain needed by the unproved comparison theorem.

## Where the brief, the DAG or earlier work was wrong

The concrete adjunction generator formulas do not require reconstructing the direct-sum
Hom bijection: localizedSystemAdjunction_existsUnique already specifies the unit, and the
right triangle identity gives the counit. Scalar exactness can use the existing proved
moduleSheaves_colimits_forgetful theorem instead of reconstructing kernels and cokernels.
The identity action on tuples is definitional, including the empty direct sum.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
