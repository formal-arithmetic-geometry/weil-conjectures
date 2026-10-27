## What changed

Replaced the hole in `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.associator_commShift`
with the ordinary-derived, integral-inclusion, and raw-localization argument. All helper lemmas
are private and proved. The statement, independent universes, actual coefficient transports and
repeated-index cases are preserved. Only the assigned Lean module and its node are changed.

The ordinary compositor uses the proved shift instances from
`WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`. The existing
`integralScalarCommShift_existsUnique`, `sfIntegralScalarComp_existsUnique`, and
`transitionCommShift_existsUnique` specifications supply the prescribed shift and integral
normalization. The stated `intrinsicRationalScalarAssociator_image` supplies the rational
associator normalization. Rationalization is checked at shift one and extended to all integers by
addition and inverse-shift coherence. The localization square is proved for arbitrary
coefficient-linear categories and transported along the defining functor equalities, keeping large
concrete coefficient constructions out of conversions.

## Proved and sorry left

Closed: `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.associator_commShift` (node
`lem-pur-intrinsic-associator-shift-square`), one of one original holes. No holes added or split
off; no sorry remains in the delivered module.

## No longer needed

The ordinary exactness, integral compositor image, and integral shift formulas of
`Sheaf.Paper.IntrinsicScalarNormalizationFormulas` are unneeded here: the adopted source library
already proves ordinary derived compatibility, and the defining modules expose proved integral
normalization specifications. Its rational associator image remains a needed stated dependency;
the module is retained. The standalone localization universal-property dependency
`lem-weil-pbc-localization-universal-property` is unnecessary: the ordinary derived compositor's
shift compatibility is already proved in the adopted source library. Removed the five redundant
private imports: `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
`Mathlib.CategoryTheory.Localization.Predicate`, `Mathlib.CategoryTheory.Shift.CommShift`,
`Sheaf.CategoryTheory.ScalarLocalization`, and
`Sheaf.CategoryTheory.ScalarLocalizationTriangulated`. The used APIs are already provided by the
retained imports. No existing source declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The ordinary and integral parts of the planned normalization interface, and arbitrary-degree
rational conjugation, are unnecessary. The degree-one specifications, actual rational scalar
object and pure-tensor map formulas, and coherent integer induction suffice. The mathematical
statement is unchanged. The unit has no realized proof steps that this route would bypass.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
