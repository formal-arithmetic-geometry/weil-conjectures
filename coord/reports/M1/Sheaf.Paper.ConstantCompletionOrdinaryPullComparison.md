## What changed

Proved `CategoryTheory.ConstantCompletion.ordinaryPullComparison_existsUnique` without
changing its statement. The coefficient square commutes by the finite limit projections
and naturality of `F.constants`. Private helpers transport scalar restriction through
`F.algebra` using the specified generalized-section addition and scalar-action laws.
These adapt the already proved restriction transport in
`Sheaf.Paper.RingedCoefficientPullbackComparison` to `InverseImageData`, which does not
carry the additional pushforward data of that module's `Geometry` structure.
The comparison is constructed by the sheafified scalar-extension adjunction. Its
adjunct is inverse-image restriction transport followed by scalar insertion and the
restriction compositor for the coefficient square. Adjunction naturality gives
naturality in the module; the unit gives the required insertion equation, and
injectivity of the adjunction Hom equivalence proves uniqueness.

All added helpers are private and fully proved. No data are chosen from an unproved
existence statement. The public inverse-image import already re-exports every former
public dependency, so removing the redundant imports preserves its public closure.
See `coord/changes/M1-ordinary-pull-comparison-proof.md`.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.ConstantCompletion.ordinaryPullComparison_existsUnique`
(blueprint `lem-weil-pbc-constant-completion-equivalence`).
Holes closed: 1. Holes added: 0. Sorries remaining in the item: 0.
No decomposition and no new nodes.

The full proof compiled in 21.4 seconds before final import/style cleanup.
`#print axioms` reported exactly `propext`, `Classical.choice`, and `Quot.sound`.
Final delivery checks are run on the cleaned module.

## No longer needed

This ordinary comparison needs no Noetherian, flatness, quotient-isomorphism,
K-flat-resolution, derived-functor or strict-tower argument. Those branches remain
necessary for the other declarations of the collective completion node; no DAG
node or library module is withdrawn. The unit route is unchanged.

Removed these direct imports (former public imports are still re-exported by
`Sheaf.Paper.ConstantCompletionInverseImage`):

- `public import Mathlib.CategoryTheory.Sites.LeftExact`
- `public import Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `public import Mathlib.CategoryTheory.Sites.Limits`
- `public import Mathlib.Algebra.Category.Ring.Limits`
- `public import Mathlib.Algebra.Category.Ring.Colimits`
- `public import Mathlib.Algebra.Category.Ring.FilteredColimits`
- `public import Mathlib.RingTheory.Ideal.Quotient.PowTransition`
- `public import Mathlib.RingTheory.Noetherian.Defs`
- `public import Mathlib.RingTheory.Ideal.Quotient.Operations`
- `public import Sheaf.Paper.FlatRingedIdealCompleteEquivalence`
- `public import Sheaf.CategoryTheory.RingedKoszulSystem`
- `public import Sheaf.CategoryTheory.AlgebraicInverseImage`
- `public import Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `public import Sheaf.Paper.RingedSiteIdeal`
- `public import Mathlib.Algebra.Category.Grp.FilteredColimits`
- `public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`
- `public import Mathlib.CategoryTheory.Sites.Over`
- `public import Sheaf.CategoryTheory.RingedSiteModules`
- `public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete`
- `public import WeilConjectures.Algebra.Homology.DerivedInternalHom`
- `public import Sheaf.Algebra.Homology.KFlat`
- `public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`
- `public import Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `public import Mathlib.Algebra.Homology.BifunctorShift`
- `public import Mathlib.CategoryTheory.Limits.HasLimits`
- `public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived`
- `public import Mathlib.CategoryTheory.Functor.Derived.RightDerived`
- `public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `import WeilConjectures.CategoryTheory.NatTransFromResolvingClass`
- `import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated`
- `import Sheaf.Paper.KFlatRingedToposPullback`
- `import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients`
- `import Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat`
- `import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`
- `import Mathlib.RingTheory.Ideal.Span`
- `import Mathlib.RingTheory.Finiteness.Defs`
- `import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison`
- `import all Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
- `import Mathlib.CategoryTheory.Adjunction.Whiskering`
- `import Mathlib.CategoryTheory.Adjunction.Additive`
- `import Sheaf.Paper.RingedTopoiDerivedPullback`
- `import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`
- `import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory`
- `import Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`

The proof uses private helpers from `ConstantCompletionCore`,
`RingedCoefficientPullbackComparison`, and `GeometricModuleTransport`, and the public
scalar adjunction from `RingedTopoiTensorSections`.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction. The large inherited import list and section context
came from splitting `ConstantCompletionEquivalence`; the ordinary comparison itself
uses only the scalar-insertion part of step 4. The node remains collective and its
other steps still describe the other split modules. No change to its statement,
unit route or dependency records is needed.

Edge cases: the construction never cancels a coefficient element or uses a nonzero,
proper or finitely generated ideal. It therefore covers `I = 0`, `I = ⊤`, the zero
coefficient ring, and arbitrary modules, exactly as the original statement requires.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionOrdinaryPullComparison": "6e9dfc25b0bd3430c0ce116aa11ee5495aaaaf76"}, "results": {"Sheaf.Paper.ConstantCompletionDerivedPull": {"hash": "23cf0a5c4c01107e6c3844ab247f347795677e0b", "status": "OK"}}, "seconds": 501, "time": "2026-10-27T23:27:32+0800", "transitive": 0, "version": 1}
```

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
