## What changed

Proved `AlgebraicGeometry.ProEtale.rationalDerivedScalar_invertible` in
`Sheaf.AlgebraicGeometry.RationalDerivedScalarInvertible`, with its signature unchanged.
The continuous-function multiplier is constructed explicitly. A proved private helper
`moduleScalarInverse` uses only additivity, the module unit axiom, and conservativity of
the forgetful functor to identify the inverse on an internal module. Componentwise
invertibility supplies the inverse complex map, and additive derived localization plus
conjugation supplies both required inverse equations on K.

Updated the existing node's proof and proof_origin to record this shorter module-action
argument. All six declared proof dependencies are retained; the blueprint unit route stays.
No definitions or public theorem signatures change, and no source-library module is edited.
The public-import interface change is recorded in
`coord/changes/rational-derived-scalar-imports.md`; no current Lean consumers require adaptation.

Validation: the complete module compiles through lcompile.py without warnings. `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. The argument
handles n=0, zero modules/complexes, empty schemes, and arbitrary unbounded representatives;
its only division is by the nonzero field element (ell:E)^n.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.ProEtale.rationalDerivedScalar_invertible`
(node `lem-sfb-rational-derived-scalar-invertible`).
Added 0 holes; split off 0 holes. No sorry remains in any delivered Lean declaration.
`moduleScalarInverse` is a fully proved private helper.

## No longer needed

Removed `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` (public import):
the proof uses the ordinary Mathlib derived localization, already available through
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`, and needs no
right derived functor. There are no current Lean importers of the item module.

Removed the proof import `Mathlib.Algebra.Homology.DerivedCategory.Basic`: it is already
publicly provided by the retained HasDerivedCategory dependency.

Removed the proof import `Sheaf.AlgebraicGeometry.ProEtalePointPullback`: the existing
point and scheme pullback adjunctions in the retained upstream ModuleObject.Basic
module directly give additivity. The node `sk-def-sfb-pullback-from-point` itself is
still needed for that construction. All original DAG dependencies remain needed;
no module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's central-scalar multiplication and commutativity
calculations in step 2 are unnecessary: m times b=id already makes b the inverse of
m times id on the underlying object. Reflection of isomorphisms then gives a module
inverse automatically, with the same explicit formula. The revised DAG records this
argument. No new mathematical assumptions or unfinished intermediate results are used.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
