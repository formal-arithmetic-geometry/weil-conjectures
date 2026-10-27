## What changed

Proved `AlgebraicGeometry.ProEtale.diagonal_evaluation_unit_exists` in
`Sheaf.Paper.DiagonalEvaluationUnit` using the universal right Kan extension of
simultaneous reduction. Evaluation followed by forgetting has an exact left
adjoint: scalar extension followed by the finite-coproduct evaluation left adjoint.
Its derived functor is therefore a right adjoint and preserves the pointwise right
Kan extension. Lift the ordinary quotient transformation through that extension;
the factorization gives the complexes equation. Naturality of the exact-functor
comparison and a degreewise calculation give the single equation.

The scalar-extension exactness and additivity proofs are reused through a private
`import all Sheaf.Paper.DiagonalDerivedReductionExists`. The other proof imports
provide localization of exact adjunctions, Kan-extension preservation, and ordinary
evaluation adjunctions. All public signatures, definitions, instances, attributes,
and public imports are unchanged. Only the item's module and its own node change.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.diagonal_evaluation_unit_exists`
(node `lem-sfb-diagonal-evaluation-unit`). No holes are added or split off;
zero `sorry` remain in the delivered module. Both new private helper theorems
are proved. The existing finite-forgetting isomorphism and transport theorem
are preserved. Server compilation succeeded in 16.6 seconds. A temporary
`#print axioms AlgebraicGeometry.ProEtale.diagonal_evaluation_unit_exists`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`; the diagnostic
command has been removed. The final delivery checks compile the cleaned file.

## No longer needed

The proof no longer directly needs `lem-pc-kflat-resolution`
(`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`),
`lem-pur-constant-two-term-resolution` (`Sheaf.Paper.ConstantTwoTermResolution`),
or `lem-weil-pbc-site-module-sheaf-constant-ring-equivalence`
(`Sheaf.CategoryTheory.SiteModuleSheafConstantRingEquivalence`). These three
planned proof dependencies are removed from the node and are not imported.
No existing import or library module is withdrawn. This reports local dependency
pruning, not a claim that these modules have no other consumers. The replacement
proof dependency is `lem-sfb-diagonal-derived-reduction-exists`, whose module
already proves exactness of the scalar extension. The diagonal-system interface
and the unit's prescribed route are retained.

## Where the brief, the DAG or earlier work was wrong

The earlier proof plan unnecessarily reconstructed K-flat models to produce the
unit. The supplied universal and pointwise derived-functor fields already permit
its construction after postcomposition with the derived right adjoint. This is
a shorter proof of the original statement and both original normalization fields;
no hypothesis or conclusion changes. The degree-zero equation is proved from the
complexes equation, without a new normalization assumption.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalEvaluationUnit": "88dc9808d8c8dc8eccdb50b8de371fd90e334f91"}, "results": {"Sheaf.Paper.StrictKummerUnitNormalization": {"hash": "6eeac958be8736c4f04d6cfd9654491ce698cce5", "status": "OK"}}, "seconds": 77, "time": "2026-10-28T03:39:44+0800", "transitive": 0, "version": 1}
```

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
