/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModel
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
/-! # Internal Hom and arbitrary changes of ring-sheaf coefficients

This is the auxiliary scalar-adjunction comparison for arbitrary changes of coefficient ring
sheaves. Every comparison is normalized on actual K-flat tensors. In particular these
are ordinary unbounded module derived categories, with no flatness or
perfectness assumption on a coefficient map or a derived input.

## References

* Bhatt--Scholze, Remark 6.8.15 (ambient derived operations)
* Stacks Project, Cohomology on Sites, Tags 07A6, 07A4, 08J9, 08JA and 0D6D
* Stacks Project, Derived Categories, Tag 05RT
* Stacks Project, Tags 03DA, 06YY, 0FND and 09T5
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open SheafOfModules
attribute [local irreducible] monoidalCategory derivedInternalHomOfUniverses
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- The recorded module category, with its ring-sheaf commutativity forgotten. -/
abbrev scalarModules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J
    (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

variable {J} {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)

/-- Actual ordinary restriction along the given map of commutative ring sheaves. -/
noncomputable abbrev scalarRestriction : scalarModules J S ⥤ scalarModules J R :=
  restrictScalars ((sheafCompose J
    (forget₂ CommRingCat.{r} RingCat.{r})).map a)

variable [HasDerivedCategory.{w} (scalarModules J R)]
  [HasDerivedCategory.{w} (scalarModules J S)]

/-- Exact scalar restriction preserves finite limits, by the recorded adjunction theorem. -/
noncomputable instance scalarRestriction_limits :
    PreservesFiniteLimits (scalarRestriction a) :=
  (sheafRingDerivedCoefficientAdjunction a).choose

/-- Exact scalar restriction preserves finite colimits, by the recorded adjunction theorem. -/
noncomputable instance scalarRestriction_colimits :
    PreservesFiniteColimits (scalarRestriction a) :=
  (sheafRingDerivedCoefficientAdjunction a).choose_spec.choose

/-- Actual termwise application of an additive functor. -/
noncomputable def scalarComplex (E : scalarModules J R ⥤ scalarModules J S)
    (hE : E.Additive) :
    CochainComplex (scalarModules J R) ℤ ⥤ CochainComplex (scalarModules J S) ℤ :=
  letI := hE
  E.mapHomologicalComplex (.up ℤ)

/-- Actual homotopy application of an additive functor. -/
noncomputable def scalarHomotopy (E : scalarModules J R ⥤ scalarModules J S)
    (hE : E.Additive) :
    HomotopyCategory (scalarModules J R) (.up ℤ) ⥤
      HomotopyCategory (scalarModules J S) (.up ℤ) :=
  letI := hE
  E.mapHomotopyCategory (.up ℤ)

/-- Derived restriction is localization of the exact termwise restriction functor. -/
noncomputable def scalarDerivedRestriction :
    DerivedCategory (scalarModules J S) ⥤ DerivedCategory (scalarModules J R) :=
  (scalarRestriction a).mapHomologicalComplexUpToQuasiIso (.up ℤ)

/-- The canonical termwise restriction comparison. -/
noncomputable def scalarRestrictionComparison :
    DerivedCategory.Q ⋙ scalarDerivedRestriction a ≅
      (scalarRestriction a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  (scalarRestriction a).mapHomologicalComplexUpToQuasiIsoFactors (.up ℤ)

/-- The representative comparison determined by a left-derived pair. -/
noncomputable def scalarPairComplexComparison
    (E : scalarModules J R ⥤ scalarModules J S) (hE : E.Additive)
    (F : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Qh ⋙ F ⟶ scalarHomotopy E hE ⋙ DerivedCategory.Qh)
    (P : CochainComplex (scalarModules J R) ℤ) :
    F.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj ((scalarComplex E hE).obj P) :=
  F.map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app _

/-- The actual chain transpose induced by an ordinary scalar adjunction. -/
noncomputable def scalarChainTranspose
    (E : scalarModules J R ⥤ scalarModules J S) (hE : E.Additive)
    (am : E ⊣ scalarRestriction a)
    (P : CochainComplex (scalarModules J R) ℤ)
    (H : CochainComplex (scalarModules J S) ℤ)
    (g : P ⟶ ((scalarRestriction a).mapHomologicalComplex (.up ℤ)).obj H) :
    (scalarComplex E hE).obj P ⟶ H :=
  letI := hE
  ((am.mapHomologicalComplex (.up ℤ)).homEquiv P H).symm g

/-- A presentation of the canonical scalar adjunction, retaining every normalization.
The functors are fixed by their object/map formulas and left-derived universal property;
the adjunction is fixed by the sheafified scalar-unit equation and chain-transpose equation.
-/
structure ScalarDerivedPair where
  /-- The ordinary scalar tensor functor. -/
  extension : scalarModules J R ⥤ scalarModules J S
  /-- Its objects are the recorded sheafified scalar tensor objects. -/
  extension_obj : ∀ M, extension.obj M = changeOfRings a M
  /-- Its maps are the recorded sheafified scalar tensor maps. -/
  extension_map : ∀ {M N : scalarModules J R} (f : M ⟶ N),
    extension.map f = eqToHom (extension_obj M) ≫ changeOfRingsHom a M f ≫
      eqToHom (extension_obj N).symm
  /-- Scalar extension is additive. -/
  extension_additive : extension.Additive
  /-- The everywhere defined left derived extension. -/
  derived : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S)
  /-- Its defining universal comparison. -/
  counit : DerivedCategory.Qh ⋙ derived ⟶
    scalarHomotopy extension extension_additive ⋙ DerivedCategory.Qh
  /-- The recorded left-derived universal property. -/
  isLeftDerived : derived.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (scalarModules J R) (.up ℤ))
  /-- Every K-flat complex computes this universal derived pair. -/
  computes : ∀ (P : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      IsIso (scalarPairComplexComparison extension extension_additive derived counit P)
  /-- The ordinary scalar adjunction. -/
  ordinaryAdjunction : extension ⊣ scalarRestriction a
  /-- Its unit is sheafification of 1 tensor x, so no twisted adjunction is allowed. -/
  ordinaryUnit : ∀ (M : scalarModules J R) (V : Cᵒᵖ) (x : M.val.obj V),
    ((eqToHom (extension_obj M)).val.app V)
        ((ordinaryAdjunction.unit.app M).val.app V x) =
      (toSheafify J (changeOfRingsPresheaf a M).presheaf).app V
        ((ModuleCat.extendRestrictScalarsAdj (a.hom.app V).hom).unit.app
          (M.val.obj V) x)
  /-- The unbounded derived extension/restriction adjunction. -/
  adjunction : derived ⊣ scalarDerivedRestriction a
  /-- The precise normalized derived transpose on K-flat representatives. -/
  normalization : ∀ (P : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n)) →
    ∀ (H : CochainComplex (scalarModules J S) ℤ)
      (g : P ⟶ ((scalarRestriction a).mapHomologicalComplex (.up ℤ)).obj H),
      (adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj H)).symm
          (DerivedCategory.Q.map g ≫ (scalarRestrictionComparison a).inv.app H) =
        scalarPairComplexComparison extension extension_additive derived counit P ≫
          DerivedCategory.Q.map (scalarChainTranspose a extension extension_additive
            ordinaryAdjunction P H g)

end SheafOfModules

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

/-- A simultaneous presentation of the existing derived tensors and scalar adjunctions.
Each closed structure has the recorded representative evaluation normalization;
each scalar pair has actual sheafified tensor objects/maps and the universal
left-derived comparison, with its ordinary and derived unit normalizations.
-/
structure ScalarHomModels where
  /-- The already recorded closed tensor-Hom structure for each coefficient sheaf. -/
  closed : ∀ R : Sheaf J CommRingCat.{max c v r},
    CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R)
  /-- Its fixed actual K-flat and Hom-complex representative normalization. -/
  model : ∀ R : Sheaf J CommRingCat.{max c v r},
    CoefficientTensorModels.{r, c, v, w} J R (closed R)
  /-- The normalized scalar adjunction for every actual ring-sheaf map. -/
  scalar : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S), ScalarDerivedPair a

variable {J} (M : ScalarHomModels.{c, v, r, w} J)
  {R S T : Sheaf J CommRingCat.{max c v r}}

attribute [local irreducible] scalarPairComplexComparison
  coefficientTotalTensor CoefficientTensorModels.iso

end CategoryTheory
