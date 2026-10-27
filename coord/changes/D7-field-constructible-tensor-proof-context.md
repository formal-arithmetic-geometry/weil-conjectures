# AlgebraicGeometry.Scheme.FieldConstructibleTensor proof context

## Reason

Fill the tensor-closure proof with private helpers on the coefficient-sized site. The
interface scanner requires a change record for the additional opens and instance attributes.
All new instances are private and local to `section TensorProof`; imported instance erasures
are also confined to that section. These select the existing small-site sheafification and
abelian structures without imposing a successor-universe constraint. No public declaration,
public import, existing signature or definition body changes. No other module is edited.

## Old

The existing opens were:

```lean
open CategoryTheory CategoryTheory.Limits
```

There were no proof-local instance helpers or registrations. The sole theorem was `by sorry`
with the following signature (unchanged):

```lean
theorem field_bounded_constructible_tensor (X : Scheme.{u})
    [CompactSpace X] [IsLocallyNoetherian X]
    (κ : Type (max v (u + 1))) [Field κ] :
    (∀ F G : Modules.{u, v} X κ,
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ F →
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ G →
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ
        (((ordinary.{u, v} X κ).obj F).obj G) ∧
      ∀ (S : Stratification X) (i : Fin S.n)
        (T : Scheme.{u}) (f : T ⟶ S.domain i) [WeaklyEtale f] (r s : ℕ),
        Nonempty ((coefficientProEtaleFixedModulePullback.{u, v} (f ≫ S.immersion i) κ).obj
            ((coefficientModelFixedScalars _ κ).obj F) ≅
          (constantSheaf (coefficientProEtaleModelTopology.{u, v} T) (ModuleCat κ)).obj
            (ModuleCat.of κ (Fin r → κ))) →
        Nonempty ((coefficientProEtaleFixedModulePullback.{u, v} (f ≫ S.immersion i) κ).obj
            ((coefficientModelFixedScalars _ κ).obj G) ≅
          (constantSheaf (coefficientProEtaleModelTopology.{u, v} T) (ModuleCat κ)).obj
            (ModuleCat.of κ (Fin s → κ))) →
        Nonempty ((coefficientProEtaleFixedModulePullback.{u, v} (f ≫ S.immersion i) κ).obj
            ((coefficientModelFixedScalars _ κ).obj (((ordinary.{u, v} X κ).obj F).obj G)) ≅
          (constantSheaf (coefficientProEtaleModelTopology.{u, v} T) (ModuleCat κ)).obj
            (ModuleCat.of κ (Fin (r * s) → κ)))) ∧
    (∀ A B : D.{u, v} X κ,
      ProEtale.coefficientBoundedConstructibleProEtale.{u, v} X κ A →
      ProEtale.coefficientBoundedConstructibleProEtale.{u, v} X κ B →
      ProEtale.coefficientBoundedConstructibleProEtale.{u, v} X κ
        (((tensor (ring.{u, v} X κ)).obj A).obj B) ∧
      ∀ a b c d : ℤ,
        (∀ n : ℤ, n < a ∨ b < n →
          IsZero ((coefficientModelCohomology (ring.{u, v} X κ) n).obj A)) →
        (∀ n : ℤ, n < c ∨ d < n →
          IsZero ((coefficientModelCohomology (ring.{u, v} X κ) n).obj B)) →
        ∀ n : ℤ, n < a + c ∨ b + d < n →
          IsZero ((coefficientModelCohomology (ring.{u, v} X κ) n).obj
            (((tensor (ring.{u, v} X κ)).obj A).obj B)))
```

## New

The signature above, all existing definition bodies, and all existing public imports stay
verbatim. The theorem now has a complete proof. The namespace opens additionally include
`MonoidalCategory` and scoped `ZeroObject`. The following proof-local context is introduced:

```lean
section TensorProof

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
attribute [local instance] Functor.CommShift₂.commShiftObj
  Functor.CommShift₂.commShiftFlipObj Functor.CommShift₂.commShift_map

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  ConstantScalarRestriction.fixedSheafify ConstantScalarRestriction.fixedAbelian
  ConstantScalarRestriction.ringAbelian ConstantScalarRestriction.ringPreadditive
  ConstantScalarRestriction.fixedPreadditive ConstantScalarRestriction.ringZeroMorphisms
  ConstantScalarRestriction.fixedZeroMorphisms
```

Thirteen private local instances cache additive/module sheafification, the two abelian
categories, additive and monoidal fixed-scalar restriction, exact and additive pullback,
the homology-window properties, and the standard derived-category instance. They are
proved from existing library instances and theorems; they export no global registration.
Every other new declaration is a proved private helper. `end TensorProof` restores the
surrounding instance environment before the existing public theorem is elaborated.

## Users

`python3 tools/downstream.py Sheaf.Paper.FieldBoundedConstructibleTensor --uses
field_bounded_constructible_tensor ring Modules D ordinary tensor single singleComparison`
reports zero downstream modules and only occurrences in this item. The unfinished parent
DAG route is retained; zero current importers is not treated as withdrawal authorization.
No consumer requires adaptation because all public data and signatures are preserved.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FieldBoundedConstructibleTensor | D7 (dispatched item) | Complete proof and private local elaboration context; public declarations preserved. |

## Status

landed 20261024T014500-L-2204944 2026-10-24 (merge of deliver/D7/Sheaf.Paper.FieldBoundedConstructibleTensor)
