## What changed

Proved `WeilConjectures.PurityFiniteSetting.finiteReductionOfUnitSmoothTrace` in
`Sheaf.Paper.FiniteReductionOfPurity`, retaining its exact statement and all specified
comparison maps. Specialize the already proved coefficient-valued trace reduction to
the coefficient unit, identify the explicit unit presentation with that specialization,
and use trace naturality for the actual scalar-unit arrow.

The private supporting proofs establish intrinsic finite-Tor invariance under an
isomorphism, finite-Tor constructibility of the unit using the existing finite Hom
site-descent theorem, equality of the two trace presentations, naturality of the
intrinsic exceptional counit, and naturality of the coefficient-valued trace.
New proof imports are `Sheaf.Paper.CoefFiniteHomSiteDescent`,
`Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`,
`WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual`, and
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`.
The parent node records the additional dependencies and the actual unit-trace proof.
The site-descent theorem is used only as a generic tool for preservation of the
finite-Tor domain; it does not replace any step of the purity-transport unit route.
The intrinsic triangulation theorem supplies only closure under isomorphisms.
The unit helper locally disables the redundant `finiteHomEtaleCategory` instance: its
positive-level pattern otherwise makes typeclass search unfold the entire quotient
ring at an arbitrary level. Standard derived-category instances supply the same
category structure; the attribute change is scoped to that private proof.

## Proved and sorry left

Closed one of the three original holes:
`WeilConjectures.PurityFiniteSetting.finiteReductionOfUnitSmoothTrace`
(node `thm-pur-finite-reduction-of-purity`). No holes added or split off.

Validation: the complete module compiled through `lcompile.py` in 30.7 seconds.
All eight public theorem signatures are unchanged; the source has exactly two
remaining `sorry` tokens and no lines over 100 characters.

Two original holes remain, both on `thm-pur-finite-reduction-of-purity`:

- `WeilConjectures.PurityFiniteSetting.finiteReductionOfCompositionSource`.
- `WeilConjectures.PurityFiniteSetting.finiteReductionOfCompositionExceptional`.

The other five public theorems retain their existing proofs. Every new private
helper is proved completely. The delivery relies on existing named dependency
theorems, including the finite Hom site-descent theorem; it does not claim the
entire dependency closure is free of sorry.

## No longer needed

No modules or nodes withdrawn. No original imports removed. The existing planned
tensor and adjunction dependencies still describe the two remaining composition
holes, so they remain in the DAG. The unit-trace argument needs no new reduction
lemma and no additional source-square compatibility assumption.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement change. The DAG's trace step and proof-origin text
previously described the unit-trace clause as still open; they now record its proof.
The existing finite-Tor constructibility and trace definitions use different
presentations of the coefficient unit. Their canonical comparison must be applied
explicitly; simply specializing the coefficient-valued trace theorem does not by
itself identify the unit trace.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
