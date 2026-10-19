## What changed

Proved `AlgebraicGeometry.finiteCoefficient_comparison_preserves_torAmplitude` without changing its signature. The proof combines preserved bounded constructibility with transport of a flat model in the same interval. Four new helper modules prove the constant-scalar restriction comparison, bounded constructibility, intrinsic realization flatness, and Tor-amplitude preservation. All four helpers are proved. Existing definitions and signatures are unchanged.

Intrinsic realization flatness is proved by the local equational criterion: lift the finitely many scalar coefficients to constants on a common covering, apply local triviality of relations in the original flat fixed-coefficient sheaf, and map the factorization matrix back through the scalar unit. No section ring is identified with the coefficient ring. The fixed-coefficient local-relation theorem already exists and is proved in the source library; a node attaches that declaration without duplicating it.

The retained five-module set compiled against the current library. The new flatness proof compiled in 3.7 seconds; its sole unused-tactic warning was removed. The delivery tool performs the final clean compilations and axiom probes. The requested initial dry run refused the earlier attempt's new hole before 60 percent of the budget; that hole has now been proved.

## Proved and sorry left

Closed one of the two original holes: `AlgebraicGeometry.finiteCoefficient_comparison_preserves_torAmplitude` (`lem-sf-comparison-tor-amplitude`). Added zero holes. This is a proof from the existing library declarations, not a decomposition leaving new obligations.

Proved all four new helpers: `AlgebraicGeometry.ProEtale.intrinsicRealization_restriction` (`lem-sf-intrinsic-realization-origin-comparison`), `AlgebraicGeometry.intrinsicComparison_boundedConstructible` (`lem-sf-intrinsic-comparison-constructibility`), `AlgebraicGeometry.ProEtale.intrinsicRealization_flat` (`lem-sf-intrinsic-realization-flat`), and `AlgebraicGeometry.intrinsicComparison_torAmplitude` (`lem-sf-intrinsic-comparison-tor-amplitude`). All private helpers are proved, and no definition contains sorry.

The sole remaining hole is the unchanged `AlgebraicGeometry.finiteCoefficient_comparison_reflects_torAmplitude` (`lem-sf-comparison-tor-amplitude`). It needs the compatibility of the intrinsic constant-scalar realization with the existing fixed-coefficient derived tensor and K-flat representatives. The recorded general ringed-topos tensor theorem requires explicit inverse-image and representative comparison data; these have not been constructed for this intrinsic realization. The existing fully faithful comparison and exact homology comparison then give the sheaf-level vanishing reflection. No new theorem restating that obligation has been added.

## No longer needed

For clause (i), the converse of the pro-etale flat-model equivalence removes a separate bounded-above K-flat proof: `lem-pc-bounded-above-flat-kflat-site` / `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`. Constructibility uses constant-module restriction instead of `lem-sf-proetale-constructible-origin` / `Sheaf.Paper.ProEtaleConstructibleOrigin`. The canonical intrinsic comparison already fixes the scalar construction, so `lem-weil-pbc-adjunction-lifts-group-ring-objects`, `lem-weil-pbc-sheaf-algebraic-structures-objects`, `def-weil-pbc-constant-sheaf`, `def-weil-pbc-sheafification`, and the separate derived-functor identification are unnecessary as direct proof dependencies for this clause.

Removed direct proof imports from the item module:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `WeilConjectures.SixFunctors.ProEtale.Comparison.Flat` (still used by the Tor helper)
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`

The last three imports are in the current source but were absent from the retained sandbox. They are not used by the completed preservation proof. Reflection remains open, with its tensor-comparison and sheaf-level reflection plan retained in the DAG. The unit-route import `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel` is retained for reflection. No entire library module is withdrawn. No maintainer tool approvals are edited.

## Where the brief, the DAG or earlier work was wrong

The constructible-origin statement uses a different continuous-function coefficient encoding and cannot directly prove intrinsic constructibility. Fixed-module restriction supplies the bridge. The recorded bounded-above K-flat theorem has a restricted site-universe interface; the existing pro-etale flat-model equivalence avoids that mismatch.

The retained attempt left intrinsic realization flatness as a new hole. The independent-universe local equational criterion and the source library's fixed-coefficient local-relation theorem suffice to prove it. Thus no tensor-equivalence construction is needed for preservation. The proof includes empty relations, the zero ring and empty schemes. Finiteness of the coefficient ring supplies the Noetherian hypothesis of the fixed-coefficient relation theorem.

The resumed dry run passed compilation and preflight. Inspection then corrected a nonexistent `def-weil-proetale-modules` reference in the new nodes to the existing intrinsic constant-sheaf definition `def-weil-proetale-locally-constant-sheaf`, and restored the finite-level site-comparison unit-route import.

No unit statement, target signature, or existing definition changes. There are no consumer adaptations and no change record is needed.

## New nodes

`lem-sf-intrinsic-realization-origin-comparison`: proved recovery by the sheafification unit, in `Sheaf.Paper.IntrinsicRealizationOriginComparison`.

`lem-sf-intrinsic-comparison-constructibility`: proved constructibility and finite homology support, in `Sheaf.Paper.IntrinsicComparisonConstructibility`.

`lem-sf-intrinsic-comparison-tor-amplitude`: proved interval preservation using the existing flat-model declarations and proved realization flatness, in `Sheaf.Paper.IntrinsicComparisonTorAmplitude`.

`lem-sf-intrinsic-realization-flat`: proved site flatness by locally lifting finite scalar coefficients and using the two local relation criteria, in `Sheaf.Paper.IntrinsicRealizationFlat`.

`lem-sf-fixed-coefficient-flat-local-relations`: attaches the already proved `CategoryTheory.Sheaf.hasLocallyTrivialRelations_of_flat` in `WeilConjectures.CategoryTheory.Sites.FlatLocalRelations` (line 299). This adds only a DAG record, no duplicate Lean statement or module, and no hole.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
