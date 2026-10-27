## What changed

Completed `AlgebraicGeometry.ProEtale.RationalStratum.presentationModels`, the one
remaining hole in the item. The proof preserves its entire original signature:
the specified presentation, quotient maps, ordinary-vector lifts, row and column
operations with their inverse coordinate formulas, tail quotient equations, and
isomorphisms on every specified slice.

Added four proved helper modules, each with its own node:

- `Sheaf.LinearAlgebra.ScalarPresentationCokernel` proves ordinary scalar extension
  of a specified presentation, normalized on every original vector.
- `Sheaf.LinearAlgebra.RankNormalCokernel` computes the exact kernel and surjectivity
  of tail extraction for the rectangular rank matrix and transports the quotient
  through the supplied invertible row and column operations.
- `Sheaf.CategoryTheory.ConstantScalarCokernel` proves that the existing constant
  module realization preserves cokernels, without a flatness assumption.
- `Sheaf.CategoryTheory.ConstantMatrixCokernelModels` transports the normalized
  cokernel, quotient generators, inverse matrix coordinates and coordinate selector
  equation through the existing finite-power beta isomorphisms.

The item composes these constructions with its already proved `scalarModels`.
A proved private lemma identifies the rational coefficient unit with the actual
constant continuous section. Applying `overFunctor` to the completed global
isomorphism supplies the slice clause. Added only proof imports to the item;
all existing public declarations, definitions and public imports are preserved.
No other existing Lean module is changed. The completed unsplit file took 68 seconds,
so its existing private `GenericScalar` proof block is extracted unchanged to
`Sheaf.CategoryTheory.ConstantScalarTowerComparison` and privately imported back.
That module has a fifth new node recording its already proved final private theorem.
The change record is `coord/changes/f8-rational-stratum-compile-split.md`.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.ProEtale.RationalStratum.presentationModels`
(`lem-per-rational-stratum-finite-free-model`): 1 of 1 original holes.

Added zero holes. The four new public theorems are proved:
`ModuleCat.scalarPresentationCokernel`, `Matrix.rankNormalCokernel`,
`CategoryTheory.ConstantFiniteFreePresentationExtension.constantScalarCokernel`,
and
`CategoryTheory.ConstantFiniteFreePresentationExtension.constantMatrixCokernelModels`.
Every private helper is proved. No `sorry` remains in any delivered Lean module.

All six modules passed `lcompile.py --all` in import order. The required
`deliver3.py` validation additionally checks the declaration axiom probes. These proofs use the existing library's constant,
scalar and finite-power machinery; a zero textual hole count here does not assert
that all imported declarations are independent of every remaining project hole.

## No longer needed

None. No existing import, declaration or module is removed. The new proof implements
the remaining ordinary and sheaf presentation steps of the current DAG plan.
Continuous matrix elimination remains unnecessary, as already established by the
previous delivery: the input supplies P and Q, and the local-freeness theorem uses
a finite basis. No additional module withdrawal is claimed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was required. The existing finite-presentation helper's
short-exact clause assumes injectivity and flatness, so that clause cannot be
applied to this arbitrary right-exact presentation. Its already proved beta and
matrix-coordinate helpers are sufficient after proving cokernel preservation
separately by the constant-module and scalar adjunctions.

The rank calculation needs neither a field nor existence of a normal form: it works
over any commutative ring once invertible P and Q and the rank equation are supplied.
The proof explicitly handles m=0, n=0, rho=0 and rho=n, without cancellation of an
unavailable coordinate or an assumption of a nonempty tail.

The unit `sk-p-dl-a1-perverse` retains its own statement and two realized steps
(`thm-a1-curve-perverse-heart`, `thm-a1-fourier-t-exact`). These generic algebra and
sheaf helpers implement steps below the assigned node and bypass no unit step.

## New nodes

`lem-per-scalar-presentation-cokernel` records the normalized ordinary scalar
presentation and its categorical quotient equation. Its proof uses the ordinary
extension/restriction adjunction, tensor finite powers and cokernel transport.

`lem-per-rank-normal-cokernel` records the ordinary tail quotient for a supplied
rank normal form. Its proof gives zero-padding witnesses for exactness and
surjectivity and then transports the categorical cokernel.

`lem-per-constant-scalar-cokernel` records right exactness of the existing constant
module realization, with the normalized cokernel comparison. It is proved using
finite-colimit reflection on additive sheaves and the scalar adjunction.

`lem-per-constant-matrix-cokernel-models` records realization of an ordinary
normalized cokernel and a prescribed coordinate quotient. It combines the existing
beta formulas, generator naturality and the preceding cokernel preservation result.
The parent node's proof and dependencies now record these proved helpers.

`lem-per-constant-scalar-tower-comparison` records the already proved normalized
scalar comparison extracted from the parent's private `GenericScalar` namespace.
It retains the same concrete constructions and proofs; this is a compilation split,
with no added hole or change to any public statement.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
