## What changed

Proved `WeilConjectures.TwistFrobeniusScalar.twist_frobenius_scalar_field_extensions`
from the existing rational/common-stage scalar theorem. The prescribed comparison maps
are composites of isomorphisms. Two proved private helpers show that the signed scalar
commutes with field homomorphisms and that an invertible linear comparison intertwines
operators acting by the corresponding scalars. Two further private lemmas certify
invertibility of the prescribed comparisons. Local irreducibility keeps the large
comparison and Frobenius map definitions closed during the final proofs, where
respectTransparency is enabled; public definitions and attributes are unchanged. The intertwining proof checks the actual
maps on generating tensors. All existing signatures and definitions are unchanged.
Updated the field-extension node to record this shorter argument.

## Proved and sorry left

Closed 1 of the original 6 holes:
`WeilConjectures.TwistFrobeniusScalar.twist_frobenius_scalar_field_extensions`
(`lem-pur-twist-frobenius-scalar-field-extensions`). Added 0 holes; split off 0 statements.
The proof still depends on the admitted rational/common-stage scalar theorem.

The 5 remaining holes are:

- `WeilConjectures.TwistFrobeniusScalar.signedQuotients_existsUnique`
  (`lem-pur-twist-frobenius-scalar`).
- `WeilConjectures.TwistFrobeniusScalar.reductionSheafLine_existsUnique`
  (`lem-pur-twist-frobenius-scalar`).
- `WeilConjectures.TwistFrobeniusScalar.twist_frobenius_scalar_finite_integral`
  (`lem-pur-twist-frobenius-scalar-finite-integral`).
- `WeilConjectures.TwistFrobeniusScalar.twist_frobenius_scalar_rational_qbar`
  (`lem-pur-twist-frobenius-scalar-rational-qbar`).
- `WeilConjectures.TwistFrobeniusScalar.twist_frobenius_scalar_reduction_localization`
  (`lem-pur-twist-frobenius-scalar-reduction-localization`).

## No longer needed

Removed unused proof imports:

- `Sheaf.NumberTheory.FrobeniusRootsOfUnityPower`
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`
- `Sheaf.Paper.PointProEtaleSectionsExact`
- `Sheaf.Paper.IsomorphismDerivedPullback`
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`
- `Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso`

The field-extension proof no longer directly needs
`lem-pur-point-proetale-sections-exact`,
`def-weil-frobenius-coefficient-twists`,
`lem-pur-point-frobenius-transport-normalization`, or
`lem-pur-point-tate-fiber-coefficient-comparisons` as proof dependencies: it uses
`lem-pur-twist-frobenius-scalar-rational-qbar` instead. The coefficient-twist
construction remains a statement dependency. These older nodes may still be needed
by the other component proofs; no module is withdrawn or claimed globally pruned.
The unit has no realized statement or proof steps, and its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The field-extension component can be assembled without a new generator computation:
the comparison maps are already constructed as isomorphisms, and the scalar theorem
supplies equivariance for any linear comparison.

The suggested signed-reduction route requires care: `signedTwistReduction_comparison`
requires invertibility of l on the scheme, whereas the two reduction helper signatures
here do not retain the surrounding `hl : l ≠ D.p`. Thus applying that theorem with
`sfWeilPrimeInvertible D l hl` alone does not cover their full signatures. This delivery
leaves those statements and holes unchanged; it does not assert that they are false.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
