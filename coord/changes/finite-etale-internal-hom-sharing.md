# finiteHomEtaleInternalHom

## Reason

The existing normalization compares closed records whose internal Hom functor was elaborated twice at concrete coefficient rings. Applying its heterogeneous equality made the kernel expand the maps of the derived internal Hom and time out. The source library already documents this specialization issue in `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`. Share the internal Hom before specialization, using the same published `Etale.derivedHom` and uncurrying construction. All old definitions and normalization conditions remain definitionally equal. No mathematical statement is weakened or strengthened. The module is unclaimed (both its module and DAG node claim records were absent when inspected).

## Old

```lean
def FiniteHomEtaleClosedNormalization
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u})
    (S : CoefficientClosedStructure (Functor.uncurry.obj (Etale.derivedHom A W))) : Prop :=
  S.monoidal = (inferInstance : MonoidalCategory (DerivedCategory
    (Sheaf W.smallEtaleTopology A))) ∧
  ∀ P : DerivedCategory (Sheaf W.smallEtaleTopology A),
    HEq (S.adjunction P) (finiteHomEtaleRightAdjunctionGeneral A W P)

abbrev finiteHomEtaleInternalHom (n : ℕ) :=
  Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X)
```

## New

```lean
def finiteHomEtaleInternalHomGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :=
  Functor.uncurry.obj (Etale.derivedHom A W)

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

abbrev finiteHomEtaleInternalHom (n : ℕ) :=
  finiteHomEtaleInternalHomGeneral (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X
```

## Users

The source-import closure and whole-name searches give the following consumers.
Every unchanged consumer retains its statement because the changed types and
constructors unfold to the original ones. Rows also retain adapted and new modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | Definitionally equal shared internal Hom; existing declarations retained. |
| Sheaf.Paper.EtaleKFlatTensorPresentation | new, Y7 | Identifies the chosen closed tensor using the shared normalization. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Uses the same internal Hom and closed transposes; no mathematical change. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | Y7 | Uses the shared normalization to prove the representative comparison. |

## Status

landed 20261022T114256-L-598666 2026-10-22 (merge of deliver/Y7/Sheaf.Paper.FiniteCoefficientSiteHomArrow)
