# FiniteHomEtaleRepresentativeNormalization

## Reason

The old record repeated specialized tensor carriers and localization tensorators when
elaborating its fields and projections. Share the native tensor and its localization
map in one real construction before coefficient specialization. Name the same canonical
pure-tensor generator with its existing carrier. The heterogeneous equalities impose
the same conditions. Definition-meaning review is reopened for every target using
these definitions. No target signature changes.

## Old

```lean
structure FiniteHomEtaleRepresentativeNormalization
    (S : FiniteHomEtaleRepresentativeData l E X) : Prop where
  generator : ∀ i : FiniteHomEtaleTensorSectionInput l E X,
    HEq (S.generator i)
      (((finiteHomTensorInclusionGeneral i.P i.Q i.p i.q i.k i.h).hom.app (op i.U))
        (finiteHomEtaleTensorSection l E X i.n (i.P.X i.p) (i.Q.X i.q) i.U i.x i.y))
  model : ∀ (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ),
    HEq (S.model n P Q) (Functor.LaxMonoidal.μ (finiteHomEtaleQ l E X n) P Q)
```

## New

```lean
structure FiniteHomEtaleRepresentativeNormalization
    (S : FiniteHomEtaleRepresentativeData l E X) : Prop where
  generator : FiniteHomGeneratorNormalizationAux S.generator
    (finiteHomEtaleCanonicalTensorSection l E X)
  model : ∀ n, FiniteHomEtaleModelNormalizationGeneral
    (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1)))) X (S.model n)
```

The following helpers construct the published tensor, localization tensorator and
local generators. The bundle stores explicit native constructions; it chooses no
object from an existence theorem. Its model field is precisely the native lax
tensorator. The wrappers keep the original small derived universe. The explicit
module-map projection used by the generator is its ordinary coercion to a linear map.

```lean
structure FiniteHomNativeTensorData
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] where
  tensor : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C
  model (P Q : CochainComplex C ℤ) :
    tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ⟶
      DerivedCategory.Q.obj (HomologicalComplex.tensorObj P Q)
```

```lean
def finiteHomNativeTensorDataGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] : FiniteHomNativeTensorData C where
  tensor := tensor (DerivedCategory C)
  model P Q := Functor.LaxMonoidal.μ DerivedCategory.Q P Q
```

```lean
def finiteHomLocalizationTensorModelGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] (P Q : CochainComplex C ℤ) :
    (finiteHomNativeTensorDataGeneral C).tensor.obj
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ⟶
      DerivedCategory.Q.obj (HomologicalComplex.tensorObj P Q) :=
  (finiteHomNativeTensorDataGeneral C).model P Q
```

```lean
def finiteHomDerivedTensorGeneral
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [HasColimitsOfSize.{0, 0} C] [hD : HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] :=
  (finiteHomNativeTensorDataGeneral C).tensor
```

```lean
def finiteHomEtaleDerivedTensorGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :=
  finiteHomDerivedTensorGeneral (Sheaf W.smallEtaleTopology A)
    (hD := inferInstanceAs
      (HasDerivedCategory.{u + 1} (Sheaf W.smallEtaleTopology A)))
```

```lean
def finiteHomEtaleLocalizationTensorModelGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) (P Q : CochainComplex (Sheaf W.smallEtaleTopology A) ℤ) :=
  finiteHomLocalizationTensorModelGeneral (Sheaf W.smallEtaleTopology A)
    (hD := inferInstanceAs
      (HasDerivedCategory.{u + 1} (Sheaf W.smallEtaleTopology A))) P Q
```

```lean
def finiteHomEtaleCanonicalTensorSectionGeneral
    (B : Type (u + 1)) [CommRing B] (W : Scheme.{u})
    (P Q : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : W.Etale)
    (x : (P.X p).obj.obj (op U)) (y : (Q.X q).obj.obj (op U)) :
    ((HomologicalComplex.tensorObj P Q).X k).obj.obj (op U) :=
  ((finiteHomTensorInclusionGeneral P Q p q k h).hom.app (op U)).hom'
    (((Functor.LaxMonoidal.μ (sheafToPresheaf W.smallEtaleTopology
      (ModuleCat.{u + 1} B)) (P.X p) (Q.X q)).app (op U)).hom' (x ⊗ₜ y))
```

```lean
def finiteHomEtaleCanonicalTensorSection (i : FiniteHomEtaleTensorSectionInput l E X) :
    finiteHomEtaleTensorSectionCarrier l E X i :=
  finiteHomEtaleCanonicalTensorSectionGeneral _ X i.P i.Q i.p i.q i.k i.h i.U i.x i.y
```

```lean
def FiniteHomGeneratorNormalizationAux
    {I : Type a} {V : I → Type b} (v w : ∀ i, V i) : Prop :=
  ∀ i, HEq (v i) (w i)
```

```lean
def FiniteHomEtaleModelNormalizationGeneral
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u})
    {V : CochainComplex (Sheaf W.smallEtaleTopology A) ℤ →
      CochainComplex (Sheaf W.smallEtaleTopology A) ℤ → Type (u + 1)}
    (v : ∀ P Q, V P Q) : Prop :=
  ∀ P Q, HEq (v P Q) (finiteHomEtaleLocalizationTensorModelGeneral A W P Q)
```

The generic source-presentation proof unfolds the bundle before any sheaf or finite
coefficient specialization. It identifies its tensor functor and map with the native
ones there. Its specialized consumers therefore use the shared construction through
its named interface, without repeating the native monoidal derivation.

## Users

The source-import closure and whole-name searches give the following consumers.
Every unchanged consumer retains its statement because the changed types and
constructors unfold to the original ones. Rows also retain adapted and new modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | unclaimed | Names the same localization tensorator and generator in the normalization. |
| Sheaf.Paper.EtaleKFlatTensorPresentation | new, Y7 | Uses the native bundle on K-flat representatives. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | Y7 | Unchanged; the shared type or constructor is definitionally identical where used. |
| Sheaf.Paper.FiniteCoefficientSiteTensorPresentation | new, Y7 | Combines the source presentation with resolving and chain comparisons. |

## Status

landed 20261022T114256-L-598666 2026-10-22 (merge of deliver/Y7/Sheaf.Paper.FiniteCoefficientSiteHomArrow)
