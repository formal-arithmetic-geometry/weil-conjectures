## What changed

Proved `WeilConjectures.finiteFieldDatumPrimeUnit` and
`WeilConjectures.directImages_constructible`.  The proof establishes the finite
ordinary clause by fixed etale origin, finite-type direct-image constructibility,
and the comparison isomorphisms; the compact-support clause uses the existing
finite theorem.  The integral clauses use the integral direct-image theorem and
the stored compact-support constructibility proof.  Rational and common-stage
clauses are obtained by localization and pairing with `E₀`.

The two common-stage `HEq` conclusions were repaired from `M.obj.obj` to
`M.obj.obj.obj`.  The former compares an integral constructible object with a
derived object at different structure levels and is not type-correct for the
intended construction; the latter is the underlying derived object and is
proved by reflexivity.  All other binders and conclusions are unchanged.

The existing consumer `Sheaf.Paper.OrdinaryCompactCohomology` was compiled
against this module; it uses only the unchanged first two clauses.

## Proved and sorry left

Closed both holes: `WeilConjectures.finiteFieldDatumPrimeUnit` and
`WeilConjectures.directImages_constructible`.  No `sorry` remains in the
delivered module, and no new theorem was split off.

## No longer needed

The following direct proof imports were removed after compilation showed that
the proof does not use them:

* `WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients`
* `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`
* `Sheaf.Paper.FiniteCoefficientPoint`
* `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
* `Sheaf.Paper.QcqsCompactSupportRealization`
* `Sheaf.Paper.SfCommonStageDirectImage`
* `Sheaf.Paper.SfIntegralCompactSupportConstructible`
* `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`

The corresponding proof-plan inputs `def-weil-pbc-constructible-complexes`,
`def-weil-pbc-proetale-operations`, `def-weil-finite-torsion-constructibility`,
`def-compact-support-direct-image-detailed`,
`lem-sf-compact-support-restriction-of-scalars`,
`lem-sf-integral-compact-support-constructible`, and
`def-weil-finite-coefficient-point` are not used as independent proof steps;
the specialized declarations used by the proof already package the required
facts.  No statement or definition below the module was changed.

## Where the brief, the DAG or earlier work was wrong

The Lean statement in the inherited node had two common-stage conclusions
written as `HEq M.obj.obj ...`.  In the declared structure,
`M.obj.obj` is the integral constructible object, while the displayed right
side is the derived object.  The intended common-stage object is reached at
`M.obj.obj.obj`; the repaired statement matches the natural-language DAG
statement and makes the intended reflexive construction type-correct.  The
node copy records this repaired elaborated statement.

## New nodes

None. The change record is
`coord/changes/DirectImagesConstructible-statement-and-proof.md`.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
