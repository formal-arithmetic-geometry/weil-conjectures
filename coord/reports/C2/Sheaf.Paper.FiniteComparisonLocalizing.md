## What changed

Proved `AlgebraicGeometry.ProEtale.finiteComparisonGenerators_identification` with
its existing statement. Apply `finiteTorComparisonNoetherian` to the lifted finite
ring, choose coefficient-model representatives through the presentation equalities,
and compose the model comparison square, the restricted equivalence's ambient
isomorphism and its counit. This realizes both directions of the prescribed
finite-Tor comparison route without changing the unit route.

Added `FiniteComparisonModelRealization`: the specified constant-scalar restriction
is proved to be an equivalence; evaluation through the AsSmall site equivalences
gives actual etale/pro-etale model functors. The coefficient ring-map unit equation
proves a sectionwise direct-image square. Conjugating adjunctions proves the
pullback square, and the localization universal property proves the derived square
for every D with the required localization factorization. All these proofs compile.

Moved the coefficient construction block verbatim, except blueprint links, to
`FiniteComparisonCoefficients` and publicly reexported it from the original module.
This avoids a cycle when the independent presentation bridge uses those definitions.
Added `FiniteComparisonPresentation` for the two generator-predicate replete-image
equalities separately on the two sites. It contains the one remaining named hole.

Repair of return e6b6ce7b2: added the missing unchanged consumer
`Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin` to the change record’s `## Users`.
A fresh downstream and symbol-use scan finds exactly that module and
`Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization` as external users of the moved
declarations. Both are checked unchanged against the delivery. The delivery tool
rebases the retained packet onto freshly fetched `sheaf-dag`, preserving current
node metadata outside the worker-owned fields.

The complete sandbox and both unchanged existing downstream consumers compile
with `lcompile.py --all`.
Every Lean line has at most 100 characters. A direct text comparison confirms the
moved coefficient block is unchanged except its blueprint links.

Change record: `coord/changes/finite-comparison-coefficient-presentation.md`.

## Proved and sorry left

The current item started with one hole:
`AlgebraicGeometry.ProEtale.finiteComparisonGenerators_identification`. Its proof
is now complete, using the existing finite-Tor comparison and the new coefficient
presentation lemma. The item itself now contains zero `sorry` occurrences.

One hole is added, in the independent theorem
`AlgebraicGeometry.ProEtale.finiteComparisonPresentation`, module
`Sheaf.Paper.FiniteComparisonPresentation`, node
`lem-ctf-finite-comparison-presentation`. It identifies constructibility and Tor
amplitude under the specified coefficient realizations. It does not assert any
etale/pro-etale comparison or equivalence of localizing closures. This is a
decomposition: one upper hole closed, one lower hole added, net zero local holes.

No holes are added by the model realization module. In particular,
`CategoryTheory.coefficientModelFixedScalars_isEquivalence`,
`AlgebraicGeometry.ProEtale.finiteComparisonModelPullbackSquare` and
`AlgebraicGeometry.ProEtale.finiteComparisonModelDerivedSquare` are proved.
All four equivalence/additivity instances are proved. The moved exactness theorem
was already proved and is not counted as a newly closed hole.

## No longer needed

Removed the original module's private proof imports
`Sheaf.Paper.ConstantInternalModuleSheafEquivalence` and
`Sheaf.Paper.InternalModuleAbEquivalence`: only the extracted coefficient exactness
proof uses them, so their imports now belong to `FiniteComparisonCoefficients`.
Removed its direct proof imports of `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
and `Mathlib.CategoryTheory.Monad.Limits`, which it no longer needs directly.
The model realization module still imports the former for its own definitions.
The original public imports are retained to preserve the existing public interface.
The new coefficient module imports the bounded-constructible definitions directly,
without importing unrelated operation or algebraic-closure interfaces.

No DAG node or library module is withdrawn. The Noetherian finite-Tor comparison,
ordinary full faithfulness, localizing closure argument and operation comparison
nodes remain needed. In particular neither the finite-Tor comparison unit nor the
unbounded comparison route is bypassed. The comparison square does not need any
constructibility hypothesis, so it is proved independently of the remaining
predicate bridge.

## Where the brief, the DAG or earlier work was wrong

The prior change record incorrectly described `FiniteDiscreteCtfRealization` as
the only existing external consumer. The current `FiniteDiscreteCtfOrigin` also
uses the moved realization and exactness theorem; its missing Users entry caused
the landing failure. This repair records both users without adapting either.

The live module had already been restored by C3 and had only the generator hole;
the archived module's older two-hole count is not this session's baseline.
The current generator node cited `lem-ctf-finite-comparison-presentation`, but the
repository had no such node or declaration. This delivery materializes that
separate coefficient-presentation step. The derived comparison square previously
included in that plan is proved here, rather than left inside its statement.

The coefficient-presentation proof needs genuine compatibility of finite local
models, affine-local/global stratification conventions and relative tensor tests;
exact categorical equivalence alone does not identify those predicates. Its
remaining obligation is stated explicitly, with source and a full proof in words.
The new statements retain empty schemes, zero rings and zero complexes. All model
realization and square constructions work without qcqs or finiteness hypotheses;
the predicate bridge uses precisely qcqs and the finite ring.

## New nodes

`lem-ctf-finite-comparison-coefficients` attaches the unchanged extracted coefficient
constructions and exactness theorem to their new module. No new hole.

`lem-ctf-finite-comparison-model-realization` records the constructed model functors,
the proved constant-scalar equivalence and the proved pullback/derived squares.
No new hole. Its source is the coefficient transport required before the opening
paragraph's finite-Tor comparison.

`lem-ctf-finite-comparison-presentation` records the two replete-image equalities
for bounded finite-Tor predicates. It is the sole remaining hole and a proper part
of the generator argument. The generator proof applies the independent finite-Tor
comparison and combines its outputs with these equalities and the proved square.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
