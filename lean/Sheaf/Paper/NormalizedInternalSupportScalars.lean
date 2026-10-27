/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.CoefficientHeartFiltration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Sheaf.Paper.CondensedOpenClosedRecollement
public import Sheaf.Paper.ClosedSupportedScalarComparison
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Canonical normalized internal support and scalar data

Source: blueprint main-20261015, scalar-six pullback proof (1)--(3)
(blueprint: def-sfb-normalized-internal-support-scalars).

## Main definitions

* `scalar`, `adj`, `tower`: the existing K-flat scalar functors and canonical tower.
* `support`, `supportSingle`: exact closure support and its degree-zero realization.
* `SupportComparison`: the actual unbounded support comparison normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

universe u u₁ u₂ v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.SupportedCommonField

/-- The existing internal-module category, abbreviated to display the comparison diagram.
Source: scalar-six pullback proof (1)
(blueprint: def-sfb-normalized-internal-support-scalars). -/
abbrev Modules (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- The ordinary unbounded derived category of the specified internal modules.
Source: scalar-six pullback proof (1)
(blueprint: def-sfb-normalized-internal-support-scalars). -/
abbrev D (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) := DerivedCategory (Modules Λ X)

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']

/-- K-flat scalar extension, using the recorded universal derived functor unchanged.
Source: scalar-six pullback proof (1)
(blueprint: def-sfb-normalized-internal-support-scalars). -/
def scalar (c : Λ ⟶ Λ') [IsMonHom c] (X : Scheme.{u}) : D Λ X ⥤ D Λ' X :=
  (fun {F : D Λ X ⥤ D Λ' X} {G : D Λ' X ⥤ D Λ X} (_ : F ⊣ G) ↦ F)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap c X))

/-- Exact restriction of scalars in the same ordinary derived categories.
Source: scalar-six pullback proof (1)
(blueprint: def-sfb-normalized-internal-support-scalars). -/
def restrict (c : Λ ⟶ Λ') [IsMonHom c] (X : Scheme.{u}) : D Λ' X ⥤ D Λ X :=
  (Mod.comap (coefficientMap c X)).mapDerivedCategory

/-- The actual scalar adjunction; its unit is insertion of the scalar 1.
Source: scalar-six pullback proof (1)
(blueprint: def-sfb-normalized-internal-support-scalars). -/
def adj (c : Λ ⟶ Λ') [IsMonHom c] (X : Scheme.{u}) :
    scalar c X ⊣ restrict c X :=
  Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap c X)

/-- The proof-irrelevant exactness of closed direct image, from the recorded recollement.
Only a property is selected, never an object or a functor.
Source: scalar-six pullback proof (2), closed factor
(blueprint: def-sfb-normalized-internal-support-scalars). -/
instance closedExact
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {Z X : Scheme.{u}}
    [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteColimits (CondensedRing.lowerStar A i) :=
  (CondensedRing.condensed_open_closed_recollement A i
    (Scheme.openComplementOfIsClosedImmersion i).ι (Scheme.Opens.range_ι _)).choose

/-- Exact closed direct image, localized termwise, on the full unbounded category.
Source: scalar-six pullback proof (2)
(blueprint: def-sfb-normalized-internal-support-scalars). -/
def closed (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {Z X : Scheme.{u}}
    [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] : D A Z ⥤ D A X :=
  (CondensedRing.lowerStar A i).mapDerivedCategory

/-- Exact adjunction localized on complexes using the canonical factorization squares.
This is termwise localization, so its unit and counit are the ordinary unit and counit.
Source: scalar-six pullback proof (2), exact unbounded route
(blueprint: def-sfb-normalized-internal-support-scalars). -/
def exactAdjunction {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory :=
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors.symm⟩
  (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso B (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory

/-- The actual closed restriction/direct-image adjunction localized termwise.
Source: scalar-six pullback proof (2)
(blueprint: def-sfb-normalized-internal-support-scalars). -/
def closedAdj (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {Z X : Scheme.{u}}
    [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] :
    (CondensedRing.upperStar A i).mapDerivedCategory ⊣ closed A i :=
  exactAdjunction (CondensedRing.upperStar A i) (CondensedRing.lowerStar A i)
    (CondensedRing.upperStarLowerStarAdjunction A i)

/-- The specified exact locally closed extension, through the scheme-theoretic closure.
Source: direct-image stability proof (3), definition of h_!
(blueprint: def-sfb-normalized-internal-support-scalars). -/
def support (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {S X : Scheme.{u}} [IsNoetherian X]
    [TopologicalSpace.NoetherianSpace S] (a : S ⟶ X) [IsImmersion a] : D A S ⥤ D A X :=
  (CondensedRing.openImmersionLowerShriek A a.toImage).mapDerivedCategory ⋙
    closed A a.imageι

/-- Restriction along a coefficient tower, using exact localization of action restriction.
Source: scalar-six pullback proof (3)
(blueprint: def-sfb-normalized-internal-support-scalars). -/
def restrictComp (c : Λ ⟶ Λ') [IsMonHom c] (d : Λ' ⟶ Λ'') [IsMonHom d]
    (X : Scheme.{u}) : restrict d X ⋙ restrict c X ≅ restrict (c ≫ d) X :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Mod.comapComp (coefficientMap c X)
      (coefficientMap d X)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Mod.comapCongr (coefficientMap_comp c d X).symm)

/-- The canonical scalar reassociation fixed by the actual two scalar adjunctions.
Adjoint uniqueness uses the identity comparison on the restricted actions. Its balanced
formula is b tensor (c tensor v) mapped to b d(c) tensor v.
Source: scalar-six pullback proof (3)
(blueprint: def-sfb-normalized-internal-support-scalars). -/
def tower (c : Λ ⟶ Λ') [IsMonHom c] (d : Λ' ⟶ Λ'') [IsMonHom d]
    (X : Scheme.{u}) : scalar c X ⋙ scalar d X ≅ scalar (c ≫ d) X :=
  (((adj c X).comp (adj d X)).ofNatIsoRight (restrictComp c d X)).leftAdjointUniq
    (adj (c ≫ d) X)

/-- The derived A-linear map induced by the coefficient inclusion c. It is defined
independently of the c-adjunction unit: its transpose under A-to-C scalar extension is
the direct A-to-B unit. Thus on balanced representatives it sends z tensor v to c(z)
tensor v, including for unbounded inputs and without flatness.
Source: direct-image stability proof (3), displayed m_V
(blueprint: def-sfb-normalized-internal-support-scalars). -/
def inducedMap (e : Λ ⟶ Λ') [IsMonHom e] (c : Λ' ⟶ Λ'') [IsMonHom c]
    (X : Scheme.{u}) (V : D Λ X) :
    (restrict e X).obj ((scalar e X).obj V) ⟶
      (restrict (e ≫ c) X).obj ((scalar (e ≫ c) X).obj V) :=
  (restrict e X).map (((adj e X).homEquiv V
    ((restrict c X).obj ((scalar (e ≫ c) X).obj V))).symm
      ((adj (e ≫ c) X).unit.app V ≫
        (restrictComp e c X).inv.app ((scalar (e ≫ c) X).obj V))) ≫
    (restrictComp e c X).hom.app ((scalar (e ≫ c) X).obj V)

/-- The actual degree-zero comparison to ordinary scalar extension, defined by
transposing the ordinary scalar unit through the specified derived scalar adjunction.
The exact restriction/single comparison identifies its codomain. Its invertibility
for lisse modules is a conclusion, never an assumption of the main theorem.
Source: scalar-six pullback proof (1)
(blueprint: def-sfb-normalized-internal-support-scalars). -/
def singleComparison (c : Λ ⟶ Λ') [IsMonHom c] (X : Scheme.{u}) (M : Modules Λ X) :
    (scalar c X).obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (coefficientMap c X)).obj M) :=
  ((adj c X).homEquiv _ _).symm
    ((DerivedCategory.singleFunctor (Modules Λ X) 0).map
        ((Mod.extendRestrictAdjunction (coefficientMap c X)).unit.app M) ≫
      ((Mod.comap (coefficientMap c X)).mapDerivedCategorySingleFunctor 0).inv.app
        ((Mod.extendScalars (coefficientMap c X)).obj M))

/-- Exact coefficient pullback, using the already recorded internal-module functor.
Source: scalar-six pullback proof (1)
(blueprint: def-sfb-normalized-internal-support-scalars). -/
abbrev pull (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {S X : Scheme.{u}} (a : S ⟶ X) :=
  (CondensedRing.upperStar A a).mapDerivedCategory

/-- The specified K-flat comparison is the inverse scalar-adjunction mate of the
identity on restricted actions, as in the recorded normalization lemma.
Source: scalar-six pullback proof (1)
(blueprint: def-sfb-normalized-internal-support-scalars). -/
structure PullComparison (c : Λ ⟶ Λ') [IsMonHom c] {S X : Scheme.{u}} (a : S ⟶ X) where
  iso : pull Λ a ⋙ scalar c S ≅ scalar c X ⋙ pull Λ' a
  normalized : iso.hom = SheafOfModules.ScalarPullback.mate (adj c X) (adj c S)
    (CondensedRing.derivedComapUpperStarIso c a).inv

/-- The factorized comparison obtained from the closed counit-normalized comparison
and the published open scalar conjugate. This is real composition data.
Source: scalar-six pullback proof (2)
(blueprint: def-sfb-normalized-internal-support-scalars). -/
def supportComparison (c : Λ ⟶ Λ') [IsMonHom c]
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a]
    (δ : closed Λ a.imageι ⋙ scalar c X ≅ scalar c a.image ⋙ closed Λ' a.imageι) :
    support Λ a ⋙ scalar c X ≅ scalar c S ⋙ support Λ' a :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (CondensedRing.openImmersionLowerShriek Λ a.toImage
      ).mapDerivedCategory δ ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (CondensedRing.derivedOpenImmersionShriekIso c a.toImage)
      (closed Λ' a.imageι) ≪≫ Functor.associator _ _ _

/-- The required equations for the actual unbounded support comparisons. Keeping the
normalizations in a predicate avoids expanding their concrete localization data in each
structure projection.
Source: scalar-six pullback proof (1)--(2), normalized closed-unit expansion
(blueprint: def-sfb-normalized-internal-support-scalars). -/
def SupportNormalized (c : Λ ⟶ Λ') [IsMonHom c]
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a]
    (openPull : PullComparison c a.toImage) (closedPull : PullComparison c a.imageι)
    (δ : closed Λ a.imageι ⋙ scalar c X ≅ scalar c a.image ⋙ closed Λ' a.imageι) : Prop :=
  (δ.hom = SheafOfModules.ScalarPullback.closedScalarMap
    (closedAdj Λ a.imageι) (closedAdj Λ' a.imageι) (scalar c X) (scalar c a.image)
      closedPull.iso) ∧
  (∀ M : D Λ S,
    (scalar c S).map
        ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
          Λ a.toImage).unit.app M) ≫
      openPull.iso.hom.app
        ((CondensedRing.openImmersionLowerShriek Λ a.toImage).mapDerivedCategory.obj M) ≫
      (pull Λ' a.toImage).map
        ((CondensedRing.derivedOpenImmersionShriekIso c a.toImage).hom.app M) =
      (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
        Λ' a.toImage).unit.app ((scalar c S).obj M)) ∧
  ∀ M : D Λ a.image,
    IsZero ((pull Λ' (Scheme.openComplementOfIsClosedImmersion a.imageι).ι).obj
      ((scalar c X).obj ((closed Λ a.imageι).obj M))) ∧
    IsZero ((pull Λ' (Scheme.openComplementOfIsClosedImmersion a.imageι).ι).obj
      ((closed Λ' a.imageι).obj ((scalar c a.image).obj M))) ∧
    (pull Λ' (Scheme.openComplementOfIsClosedImmersion a.imageι).ι).map
      (δ.hom.app M) = 0

/-- Natural support comparison data with their prescribed full unbounded normalizations.
The isomorphisms are linear over their destination coefficient ring by their types.
Source: scalar-six pullback proof (1)--(2)
(blueprint: def-sfb-normalized-internal-support-scalars). -/
structure SupportComparison (c : Λ ⟶ Λ') [IsMonHom c]
    {S X : Scheme.{u}} [IsNoetherian X] [TopologicalSpace.NoetherianSpace S]
    (a : S ⟶ X) [IsImmersion a] where
  openPull : PullComparison c a.toImage
  closedPull : PullComparison c a.imageι
  closedIso : closed Λ a.imageι ⋙ scalar c X ≅ scalar c a.image ⋙ closed Λ' a.imageι
  normalized : SupportNormalized c a openPull closedPull closedIso

/-- Exact support extension commutes with the single-complex realization, using the
published exact-functor factorization, with no chosen object identification.
Source: direct-image stability proof (3), K=(a_!L_0)[0]
(blueprint: def-sfb-normalized-internal-support-scalars). -/
def supportSingle (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {S X : Scheme.{u}} [IsNoetherian X]
    [TopologicalSpace.NoetherianSpace S] (a : S ⟶ X) [IsImmersion a] (M : Modules A S) :
    (support A a).obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((coefficientHeartLocallyClosedExtension A a inferInstance).obj M) :=
  (closed A a.imageι).mapIso
      (((CondensedRing.openImmersionLowerShriek A a.toImage
        ).mapDerivedCategorySingleFunctor 0).app M) ≪≫
    ((CondensedRing.lowerStar A a.imageι).mapDerivedCategorySingleFunctor 0).app
      ((CondensedRing.openImmersionLowerShriek A a.toImage).obj M)

end AlgebraicGeometry.ProEtale.SupportedCommonField
