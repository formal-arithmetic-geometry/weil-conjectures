## What changed

Replaced the body of
`AlgebraicGeometry.ProEtale.coefficientComparison_affineSections_vanishing`
by the module Čech criterion on the coefficient-sized pro-etale model itself.
Its public signature and existing public imports are unchanged.

The proof establishes cover-density of the transported affine ind-etale basis,
finite refinements inside any covering sieve, and membership of every chosen
Čech intersection in the basis. The intersection argument uses the universal
properties of `SiteCechComplex`, so it works for any permitted choices.
The finite-refinement argument generalizes the proof of
`affineProEt_finite_refinement`: the ambient affineness hypothesis there is
unnecessary, since only the covered basis object must be affine. This is why
that affine-ambient public theorem cannot be directly applied here.

The module Čech criterion computes the cohomology of an intrinsic-module
injective resolution; `InjectiveResolution.isoRightDerivedObj` identifies it
with exactly the displayed derived evaluation. There is no appeal to
injectivity after forgetting the scalar action.

Added `Sheaf.AlgebraicGeometry.CoefficientComparisonAffineCech` for the remaining
finite-cover calculation of Tag 099U. It concerns an explicit ordinary Čech
complex, has no derived functor or enough-injectives assumption, and is the
geometric step before the Čech-to-derived criterion. The original node now
records the actual proof route.

Validation: `lcompile.py --all` compiled the complete packet without errors or
warnings on 2026-10-26. The finite Čech module took 9.6 seconds and the item
module 12.0 seconds. The existing theorem signature and public imports were
compared with the repository and are unchanged. The new node's recorded Lean
signature agrees verbatim with its declaration; all Lean lines are at most
100 characters. A dependency traversal found no cycle.

## Proved and sorry left

Closed the original body's hole in
`AlgebraicGeometry.ProEtale.coefficientComparison_affineSections_vanishing`
(node `lem-pe-coefficient-comparison-affine-sections`) by a complete proof from
the finite-cover calculation and the already proved module Čech criterion.
All five private helpers are completely proved.

Added one hole:
`AlgebraicGeometry.ProEtale.coefficientComparison_affineCech_vanishing`
(node `lem-pe-coefficient-comparison-affine-cech`). Its docstring and node give
the two-limit proof, including compatibility with the face maps, module
injectivity, and the empty-family case.

This is a decomposition: one original hole closed, one strictly smaller
finite-cover Čech obligation added, net zero holes. The item module itself
contains zero remaining `sorry`s. No definition contains a hole.

## No longer needed

No original public import was removed. The exploratory proof import
`Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishing` was replaced by
`WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`, whose proved
geometric basis declarations are all this part of the proof needs.
The separate `Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape` proof import
is redundant with those public geometric imports and was removed.

The original node no longer directly uses:

- `lem-weil-pbc-etale-restriction-injectives`: no localization to W is performed.
- `lem-weil-pbc-proetale-restriction-injectives`: the original site's evaluation
  is computed directly.
- `lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison`: the module
  injective resolution already computes the specified composed functor.
- `lem-weil-pbc-comparison-injective-acyclicity`: the original-site theorem fixes
  the coefficient morphism universe to u+1, and cannot be applied verbatim to
  arbitrary coefficients in max(v,u+1).
- `sk-thm-pe-indetale-refinement`: the finite-cover calculation uses ind-etale
  presentations of basis objects, not a new weakly-etale covering refinement.
- `lem-pe-coefficient-comparison-data` as a separate proof step: its definitions
  remain statement dependencies and their public import remains.

These are dependency-edge removals, not withdrawals of those modules. The
finite-cover node still needs its recorded geometry, continuity, and exactness
inputs. No upstream declaration or module is removed. The unit's own route is
preserved: Tag 099U's finite Čech calculation followed by its acyclicity criterion.

## Where the brief, the DAG or earlier work was wrong

The original plan's localization and separate module/abelian derived comparison
are unnecessary for this statement. The module criterion already returns the
cohomology of evaluation of the underlying abelian presheaf on an injective
resolution in the intrinsic module category.

The proved older comparison-acyclicity package works with coefficient morphisms
in universe u+1. The current theorem has independent coefficient size
max(v,u+1); direct application would silently specialize away the required
universe generality. The finite-cover lemma explicitly retains both universes.
No target, existing definition, or existing theorem statement was changed.

## New nodes

`lem-pe-coefficient-comparison-affine-cech` records positive Čech vanishing for
finite covers of affine ind-etale objects. It is the ordinary-complex calculation
in the original plan, with the subsequent derived-functor argument removed.
The empty cover has zero cochain groups, repeated indices are retained, and
arbitrary choices of nerve products are allowed. Its proof is the two-limit
argument from Stacks Tag 099U using module-injective Čech vanishing and exact
filtered colimits in the coefficient universe. No change record is required:
there are no existing interface or definition changes.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
