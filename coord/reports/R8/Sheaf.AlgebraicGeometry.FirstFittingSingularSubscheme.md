## What changed

Proved `AlgebraicGeometry.Scheme.existsUnique_firstFittingIdealSheaf` in
`Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme`, with its existing signature.
The witness is the existing general `Scheme.Modules.fittingIdealSheaf` at index one.
Its affine characterization is the first conjunct of the existing
`Scheme.Modules.fitting_ideal_generate_locally`; uniqueness is proved by
`IdealSheafData.ext`, comparing the witnessing surjection on each affine open.

Added the proved private helper `relativeDifferentials_finiteType`: choose affine-pair
charts, apply Mathlib's `KaehlerDifferential.finite`, transport through the existing
affine differential and section equivalences, and apply the covering clause of
`quasicoherent_finite_type_affine`. This uses only locally finite type, including on
non-noetherian schemes, and introduces no finite-presentation assumption.

Added proof imports of `Sheaf.AlgebraicGeometry.FittingIdealGenerateLocally`,
`WeilConjectures.AlgebraicGeometry.TangentBundle`,
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`, and
`Mathlib.RingTheory.Finiteness.Cardinality`. Each supplies a declaration used in the proof.
The TangentBundle import supplies the existing quasi-coherence instance and affine-pair
neighbourhood lemma. Updated the item's DAG proof, dependencies and origin to match.
No definition, public signature, public import or existing consumer changed.

Validation: `lcompile.py` compiled the proof cleanly in 9.5 seconds. Both new import
routes checked by `tools/import_direction.py` are acyclic. DAG dependency traversal also
confirmed the general Fitting criterion and affine finite-type criterion do not reach
this item. Read Stacks Divisors section-fitting-ideals and Morphisms
lemma-finite-type-differentials, and the current blueprint unit. Search via leanfinder,
loogle, the launcher's grep and local rg found the existing general Fitting criterion
and Mathlib `Module.Finite.exists_fin'`, rather than a need for a new statement.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.Scheme.existsUnique_firstFittingIdealSheaf`
(node `def-trf-first-fitting-singular-subscheme`).
Added 0 holes; split off 0 statements. The item's module now contains 0 `sorry`s.
The new private helper `relativeDifferentials_finiteType` is fully proved.
The proof uses the existing, still unfinished
`AlgebraicGeometry.Scheme.Modules.fitting_ideal_generate_locally`
(node `lem-trf-fitting-ideal-generate-locally`); this delivery does not claim to close
that dependency or eliminate all transitive `sorryAx` dependencies.

## No longer needed

No existing imports removed and no modules withdrawn or globally pruned.
The item does not need a separate construction of affine Fitting ideals or a new gluing
lemma: it reuses the existing general Fitting sheaf and its affine characterization.
`lem-trf-fitting-ideal-independence-base-change` is no longer a direct proof step;
it remains a statement dependency of the existing predicate and an indirect dependency
of the general Fitting criterion, so its node and module are still needed.
The general criterion's bounded-generator, stalk, and arbitrary-pullback clauses are not
used here; only its affine characterization is used.

## Where the brief, the DAG or earlier work was wrong

The old theorem docstring asked for a finite presentation of relative differentials
under a locally finite type hypothesis. Only a finite generating surjection is needed,
and its kernel need not be finitely generated. Replaced that proof description with
the actual affine finite-generation argument and reuse of the general Fitting sheaf.
The statement and all definitions remain unchanged. The item's DAG had no proof steps;
it now records the implemented proof.

The generic affine finite-type criterion
`lem-weil-pbc-quasi-coherent-finite-type-affine` is used as a tool from another unit.
It supplies the precise local-to-global finite-generation comparison; the trace-formula
unit does not supply such a commutative-algebra/sheaf comparison. No unit route is bypassed.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
