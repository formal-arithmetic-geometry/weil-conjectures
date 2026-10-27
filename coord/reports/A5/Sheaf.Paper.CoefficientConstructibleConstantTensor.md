## What changed

In `Sheaf.Paper.CoefficientConstructibleConstantTensor`, prove
`AlgebraicGeometry.Scheme.coefficientConstructible_constantTensor` from one local tensor
calculation and the existing coefficient-site geometry. The theorem signature, the two
constant-tensor definitions, and every original public import are unchanged.

The complete private proof `commonStratification` inducts over the finite interval of
input cohomology degrees. It uses the Noetherian global/affine-local equivalence, actual
fibre-product intersections of stratifications, and the two projection pullbacks of the
same finite local models. The empty family uses the trivial stratification. A second
complete private proof converts finite and finitely presented local values over the
Noetherian ring. The final theorem proves every nonzero input degree belongs to this
interval, applies the local calculation on each stratum, and converts the resulting
global stratification back to the exact affine-local predicate.

Add `Sheaf.Paper.CoefficientConstantTensorLocalModels`, with the strictly local step
`AlgebraicGeometry.Scheme.coefficientConstantTensor_restricted_finite`. Its hypotheses
are local finite-type systems after one arbitrary scheme restriction and an upper
cohomological bound; its conclusion is a local finite-type system on that whole source
site. It has no constructibility predicate, finite stratification, scheme Noetherianity
or lower bound. Thus the proved finite geometric refinement and global assembly are
removed from the outstanding obligation. The tensor is explicitly the original K-flat
tensor and exact constant module realization, without introducing a new construction.

Validation: `lcompile.py --all` compiles both delivered modules with exit code 0:
9.2 seconds for the local-model statement and 42.9 seconds for the item. Import-direction
checks permit the existing geometry imports. No existing interface is changed, so there
are no forced consumer adaptations.

This is a decomposition. The local tensor/cohomology comparison is not claimed proved.
The original finite-ring/stalk theorem cannot be applied: A need not be finite as a set,
and the coefficient universe is independent of the scheme universe. Mathlib searches
found no matching sheaf constructibility theorem. The existing Tag 094H theorem on
K-flat representatives and canonical tensor-pullback theorem are recorded as dependencies
of the remaining local step.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.coefficientConstructible_constantTensor`
(node `lem-sfb-coefficient-constructible-constant-tensor`). Its proof and both new private
helpers contain no `sorry`.

Added one hole:
`AlgebraicGeometry.Scheme.coefficientConstantTensor_restricted_finite`
(node `lem-sfb-coefficient-constant-tensor-local-models`), in its own new module, with its
source and complete proof in words in the docstring. No other holes are added or changed.

Counts: original item 1 to 0; new module 1; net 0. This is a decomposition, not an
axiom-free proof of the tensor calculation. No data definition contains a hole or uses
an arbitrary witness from an unproved existence assertion.

## No longer needed

No original public import is removed, and no module is withdrawn.

The item no longer uses `lem-sfb-adic-finite-stratification-pullback`
(`Sheaf.AlgebraicGeometry.AdicFiniteStratificationPullback`): its recorded theorem uses
a coefficient ring in `Type (u + 1)`, while the present item has independent coefficient
size. The proved finite induction uses instead the existing coefficient-sized
`coefficientProEtale_finite_comp`, `Stratification.inter`, and the Noetherian global
constructibility equivalence. No arbitrary factorization by image containment is used.
This does not claim the old module is unused by other parents.

The original node's direct planned dependencies
`def-weil-pbc-proetale-operations`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`def-sfb-site-derived-constant-module-functor`, and
`lem-weil-pbc-locally-constant-tensor` remain needed by the new local calculation; they
are not globally pruned. The constant functor also remains an original public import.
The finite-presentation node remains directly used. No unit statement or realized unit
proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement survives the zero module, zero ring, empty scheme, and empty
finite-family edge cases. No statement dispute or repair is needed.

The planned common-stratification declaration does not directly accept the independent
coefficient universe. Existing coefficient-sized pullback and global-constructibility
APIs suffice for a complete geometric proof, so no shared statement or definition is
changed. Finite generation implies finite presentation here by
`Module.finitePresentation_of_finite`; this is a theorem, deliberately not a global
instance in Mathlib, so the proof applies it explicitly.

## New nodes

`lem-sfb-coefficient-constant-tensor-local-models`, attached to
`Sheaf.Paper.CoefficientConstantTensorLocalModels` and
`AlgebraicGeometry.Scheme.coefficientConstantTensor_restricted_finite`: the local
bounded-above tensor calculation after an arbitrary scheme restriction, from Stacks
Tag 094H and the restriction/tensor comparisons in Tag 09BQ. It strictly removes the
finite-family stratification and global constructibility arguments, which are proved
in this delivery. No change record is needed: existing public interfaces and definitions
are unchanged, and no other existing module is modified.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
