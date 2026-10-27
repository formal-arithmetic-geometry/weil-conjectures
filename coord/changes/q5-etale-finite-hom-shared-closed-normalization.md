# finiteHomEtaleClosed_existsUnique and its shared normalization data

## Reason

Prove the existing normalized closed-record existence and uniqueness theorem.
Its direct specialization repeatedly exceeded the compile limit because Lean
compared expanded derived monoidal and closed structures. Share the exact same
internal Hom, right-tensor adjunction and normalization before specializing the
coefficient category. The factored definitions are definitionally equal to the
old ones; no mathematical normalization condition changes.

The total-tensor inclusion only uses a preadditive category, not an abelian
structure. Replace its unnecessary abelian hypothesis with preadditivity. This
avoids comparing the inherited abelian addition with the already selected sheaf
addition. Its body remains the published signed-total summand inclusion.
An isolated kernel profile reduced the generator check from 19.7 to 9.76 seconds.

No source-library declaration, public import or target statement changes.
Definitions in the targets' dependency closure are factored; their meanings stay
identical. The independent review should recheck the affected target meanings as
required by stages/2-statements.md, using the old and new definition bodies below. The attempted combined
reflexivity audit was too expensive; it is not claimed as a passing check.

## Old

```lean
def finiteHomEtaleRightAdjunctionGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) (P : DerivedCategory (Sheaf W.smallEtaleTopology A)) :=
  letI := finiteHomDerivedBraiding (Sheaf W.smallEtaleTopology A)
  finiteHomRightAdjunction P
```

```lean
def finiteHomEtaleInternalHomGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :=
  Functor.uncurry.obj (Etale.derivedHom A W)
```

```lean
def FiniteHomEtaleClosedNormalization
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u})
    (S : CoefficientClosedStructure (finiteHomEtaleInternalHomGeneral A W)) : Prop :=
  S.monoidal = (inferInstance : MonoidalCategory (DerivedCategory
    (Sheaf W.smallEtaleTopology A))) ∧
  ∀ P : DerivedCategory (Sheaf W.smallEtaleTopology A),
    HEq (S.adjunction P) (finiteHomEtaleRightAdjunctionGeneral A W P)
```

```lean
def finiteHomTensorInclusionGeneral
    {C : Type a} [Category.{b} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C] (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    (p q k : ℤ) (h : p + q = k) :
    P.X p ⊗ Q.X q ⟶ (HomologicalComplex.tensorObj P Q).X k :=
  HomologicalComplex.ιTensorObj P Q p q k h
```

## New

```lean
def finiteHomEtaleRightAdjunctionGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) (P : DerivedCategory (Sheaf W.smallEtaleTopology A)) :=
  finiteHomDerivedRightAdjunctionGeneral (Sheaf W.smallEtaleTopology A) P
```

```lean
def finiteHomEtaleInternalHomGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :=
  finiteHomDerivedInternalHomGeneral (Sheaf W.smallEtaleTopology A)
```

```lean
def FiniteHomEtaleClosedNormalization
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u})
    (S : CoefficientClosedStructure (finiteHomEtaleInternalHomGeneral A W)) : Prop :=
  FiniteHomDerivedClosedNormalization (Sheaf W.smallEtaleTopology A) S
```

```lean
def finiteHomTensorInclusionGeneral
    {C : Type a} [Category.{b} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    (p q k : ℤ) (h : p + q = k) :
    P.X p ⊗ Q.X q ⟶ (HomologicalComplex.tensorObj P Q).X k :=
  HomologicalComplex.ιTensorObj P Q p q k h
```

Three public definitions share the same real constructions at a generic
category before the etale specialization:

```lean
def finiteHomDerivedRightAdjunctionGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (P : DerivedCategory C) :=
  letI := finiteHomDerivedBraiding C
  finiteHomRightAdjunction P
```

```lean
def finiteHomDerivedInternalHomGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] :=
  Functor.uncurry.obj (MonoidalClosed.internalHom (C := DerivedCategory C))
```

```lean
def FiniteHomDerivedClosedNormalization
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (S : CoefficientClosedStructure (finiteHomDerivedInternalHomGeneral C)) : Prop :=
  S.monoidal = (inferInstance : MonoidalCategory (DerivedCategory C)) ∧
  ∀ P : DerivedCategory C, HEq (S.adjunction P) (finiteHomDerivedRightAdjunctionGeneral C P)
```

## Users

`tools/downstream.py --uses` reports only the item itself as a textual user of
each changed declaration. Its transitive import closure has 823 modules, whose
statements retain the same meaning by the definitional equalities above.
The K-flat presentation consumer also checks the unchanged chosen model API.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | Q5 | Same closed data and normalization; tensor inclusion uses its minimal structural hypothesis. |
| Sheaf.Paper.EtaleKFlatTensorPresentation | unclaimed | Consumer validation only; no source adaptation. |

## Status

landed 20261025T211050-L-3781601 2026-10-25 (merge of deliver/Q5/Sheaf.Paper.EtaleFiniteCoefficientHomArrow)
