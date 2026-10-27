## What changed

Proved `CategoryTheory.finiteFreeExceptionalMate_isIso` with its existing statement,
public definitions, and public imports unchanged. No other library module is modified.
Added proof imports for `WeilConjectures.CategoryTheory.Sites.FlatExtendScalars`,
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Descent`,
`WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`,
`WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation`, and
`Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived`. These supply the
proved ordinary basis calculation, exactness, biproduct transport, localized
adjunction, and left-derived universal-property APIs.

Constructed the scalar presentations using exact sheafified ordinary extension of
scalars. The ordinary module basis theorem gives the unit columns on sections;
evaluation gives the same result for complexes. Generic private exact-functor lemmas isolate the
localization calculation from the large sheaf types. The localized exact adjunction's
unit formula transports the columns to derived objects. The comparison isomorphism
also supplies the left-derived universal property. Restriction reflects
isomorphisms by objectwise reflection on sheaves and then derived homology.

Characterized theta using right-adjoint uniqueness, proved the mate's counit
identity and uniqueness, and traced the scalar unit through the Hom equivalences.
Coefficient multiplication and naturality identify every basis column. The
additive functor's biproduct isomorphism gives the explicit inverse; conservativity
then proves the mate invertible. This includes the empty basis.

Updated the item's DAG proof to match this direct construction and remove its
unused planned proof dependencies. All helper results are proved private lemmas
in the assigned module, and no intermediate statement is split off.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.finiteFreeExceptionalMate_isIso`.
Added zero holes. No `sorry` remains in the delivered module.
The complete module compiled in 46.4 seconds. `#print axioms` for the main theorem
reported exactly `propext`, `Classical.choice`, and `Quot.sound`; the temporary
print command was then removed.

## No longer needed

The proof does not use these planned dependencies:

- `lem-sfb-derived-finite-free-scalar-coordinates`, module
  `Sheaf.CategoryTheory.DerivedFiniteFreeScalarCoordinates`: construct the exact
  extension and its coordinates directly from the proved ordinary basis theorem.
- `lem-pur-sheaf-ring-derived-coefficient-adjunction`, module
  `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`: localize the exact
  module-valued-sheaf adjunction and check its unit directly.
- `lem-sfb-dc-hom-scalar-adjunction`, module
  `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`: prove conservativity directly
  through homology and ordinary restriction of scalars.
- `lem-galois-yoneda-fully-faithful`: use the existing `rightAdjointUniq` API and its
  counit characterization instead of a separate Yoneda representation argument.

The three Sheaf proof imports above and the redundant `Mathlib.CategoryTheory.Yoneda`
proof import were removed. These are pruning recommendations for this item's
route; no source-library declaration or module is withdrawn. The source proof
helpers used instead remain intact in their original modules.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The planned constant-ring transport and general
ringed-sheaf derived scalar machinery are unnecessary for the fixed-ring
ModuleCat-valued sheaf statement already written here. Exact ordinary scalar
extension and its localization suffice.

As already observed in the DAG, the supplied restriction comparison `rho` and
its normalization are unnecessary for the scalar-unit calculation. Their binders
and the entire public statement are retained verbatim. Preservation of coefficient
multiplication by `GB` is used essentially in the column computation.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
