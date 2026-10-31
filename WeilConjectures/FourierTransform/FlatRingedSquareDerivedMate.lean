/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsMixedUniverses

/-!
# Normalized derived comparison for a flat ringed square

Source: Stacks Project, Tag 0736, `lemma-base-change-map-flat-case`, and its injective-lift
proof in `sites-cohomology.tex` (blueprint: lem-fd-flat-ringed-square-derived-mate).

The formulas in `FlatRingedSquare` expose the canonical underived mate, the normalization
of the composition identification, and the class of every injective-resolution lift.
The theorem specializes these formulas to the four actual ringed-site module categories.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w₁ w₂ w₃ w₄

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.FlatRingedSquare

/-- Modules over a commutative ring sheaf, using the recorded module category without change.
Source: Stacks 0736 (blueprint: lem-fd-flat-ringed-square-derived-mate). -/
abbrev Modules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)

section Formulas

variable {X : Type u₁} {Y : Type u₂} {X' : Type u₃} {Y' : Type u₄}
  [Category.{v₁} X] [Category.{v₂} Y] [Category.{v₃} X'] [Category.{v₄} Y']
  {F : X ⥤ Y} {F' : X' ⥤ Y'} {L : Y ⥤ Y'} {R : Y' ⥤ Y}
  {L' : X ⥤ X'} {R' : X' ⥤ X}

/-- The tensor-adjunction mate of the specified direct-image square.
Source: Stacks 0736, applying the module adjunction to `f_*b`
(blueprint: lem-fd-flat-ringed-square-derived-mate). -/
def underivedMate (a : L ⊣ R) (a' : L' ⊣ R') (s : F' ⋙ R ≅ R' ⋙ F) :
    F ⋙ L ⟶ L' ⋙ F' :=
  ((mateEquiv a' a).symm s.inv).natTrans

variable [Abelian X] [Abelian Y] [Abelian X'] [Abelian Y']
  [HasDerivedCategory.{w₁} X] [HasDerivedCategory.{w₂} Y]
  [HasDerivedCategory.{w₃} X'] [HasDerivedCategory.{w₄} Y']
  [EnoughInjectives X] [EnoughInjectives X'] [EnoughInjectives Y']
  [F.Additive] [F'.Additive] [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']

/-- The actual right-derived exchange of the underived tensor-adjunction mate.
Source: Stacks 0736 (blueprint: lem-fd-flat-ringed-square-derived-mate). -/
noncomputable def exchange (a : L ⊣ R) (a' : L' ⊣ R') (s : F' ⋙ R ≅ R' ⋙ F) :
    F.rightDerivedFunctorPlus ⋙ L.mapDerivedCategoryPlus ⟶
      L'.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (underivedMate a a' s)

/-- Compatibility with the two composite right-derived comparison maps pins the canonical
composition identification; it excludes arbitrary automorphisms of the derived functors.
Source: Stacks 0736 and the normalization of derived direct-image composition
(blueprint: lem-fd-flat-ringed-square-derived-mate). -/
def CompositionNormalization (s : F' ⋙ R ≅ R' ⋙ F)
    (κ : F'.rightDerivedFunctorPlus ⋙ R.rightDerivedFunctorPlus ≅
      R'.rightDerivedFunctorPlus ⋙ F.rightDerivedFunctorPlus) : Prop :=
  ∀ M : HomotopyCategory.Plus X',
    (Functor.rightDerivedFunctorPlusCompUnit F' R).app M ≫
        κ.hom.app (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus s.hom).app M) ≫
        (Functor.rightDerivedFunctorPlusCompUnit R' F).app M

/-- The displayed derived-adjunction unit formula, with the canonical composition
identification inserted on the left.
Source: Stacks 0736, adjoint description (blueprint: lem-fd-flat-ringed-square-derived-mate). -/
def UnitNormalization (a : L ⊣ R) (a' : L' ⊣ R')
    (κ : F'.rightDerivedFunctorPlus ⋙ R.rightDerivedFunctorPlus ≅
      R'.rightDerivedFunctorPlus ⋙ F.rightDerivedFunctorPlus)
    (β : F.rightDerivedFunctorPlus ⋙ L.mapDerivedCategoryPlus ⟶
      L'.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus) : Prop :=
  ∀ M : DerivedCategory.Plus X,
    a.derivedPlus.unit.app (F.rightDerivedFunctorPlus.obj M) ≫
        R.rightDerivedFunctorPlus.map (β.app M) ≫
        κ.hom.app (L'.mapDerivedCategoryPlus.obj M) =
      F.rightDerivedFunctorPlus.map (a'.derivedPlus.unit.app M)

/-- Every pair of bounded-below injective resolutions admits the unit lift; the class of
its transported adjoint is the specified derived exchange, for every possible lift.
The equation includes all localization, exact-functor and right-derived comparison maps,
so it asserts independence of resolutions and of the homotopy class representative.
Source: Stacks 0736, injective-lift proof
(blueprint: lem-fd-flat-ringed-square-derived-mate). -/
def LiftNormalization (a : L ⊣ R) (a' : L' ⊣ R') (s : F' ⋙ R ≅ R' ⋙ F)
    (β : F.rightDerivedFunctorPlus ⋙ L.mapDerivedCategoryPlus ⟶
      L'.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus) : Prop :=
  ∀ (M I : HomotopyCategory.Plus X) (N : HomotopyCategory.Plus X')
    (i : M ⟶ I) (j : L'.mapHomotopyCategoryPlus.obj M ⟶ N),
    HomotopyCategory.Plus.quasiIso X i → HomotopyCategory.Plus.quasiIso X' j →
    (∀ n : ℤ, Injective (I.obj.as.X n)) → (∀ n : ℤ, Injective (N.obj.as.X n)) →
    (∃ b : I ⟶ R'.mapHomotopyCategoryPlus.obj N,
      i ≫ b = a'.mapHomotopyCategoryPlus.unit.app M ≫ R'.mapHomotopyCategoryPlus.map j) ∧
    ∀ b : I ⟶ R'.mapHomotopyCategoryPlus.obj N,
      i ≫ b = a'.mapHomotopyCategoryPlus.unit.app M ≫ R'.mapHomotopyCategoryPlus.map j →
      L.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnit.app M) ≫
          β.app (DerivedCategory.Plus.Qh.obj M) ≫
          F'.rightDerivedFunctorPlus.map (L'.mapDerivedCategoryPlusFactorsh.hom.app M) ≫
          F'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map j) =
        L.mapDerivedCategoryPlus.map
            (DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map i)) ≫
          L.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj I) ≫
          DerivedCategory.Plus.Qh.map
            ((a.mapHomotopyCategoryPlus.homEquiv (F.mapHomotopyCategoryPlus.obj I)
              (F'.mapHomotopyCategoryPlus.obj N)).symm
                (F.mapHomotopyCategoryPlus.map b ≫
                  (NatTrans.mapHomotopyCategoryPlus s.inv).app N)) ≫
          F'.rightDerivedFunctorPlusUnit.app N

end Formulas
end CategoryTheory.FlatRingedSquare

namespace CategoryTheory

-- Elaborating the four concrete sheaf-module categories and their forgetful comparisons
-- requires more typeclass and definitional-equality work than the generic formulas above.
set_option maxHeartbeats 2000000 in
-- The concrete square equation needs this bound while its module forgetful functors elaborate.
set_option synthInstance.maxHeartbeats 400000 in
/-- A flat ringed square has its canonical bounded-below right-derived exchange, normalized
by injective lifts and by the derived units.
Source: Stacks Project, Tag 0736, `lemma-base-change-map-flat-case` and its proof
(blueprint: lem-fd-flat-ringed-square-derived-mate).

Proof: Choose bounded-below termwise injective resolutions using the injective representative
of D⁺ and the K-injective Hom bijection. Since `g'^*` is exact, its right adjoint preserves
injectives. Thus `g'_*N` is a bounded-below injective complex. Lift the composite of the
ordinary unit with `g'_*j` along `i`; the K-injective Hom bijection gives existence and
uniqueness up to homotopy. Apply `f_*`, transport by the specified square and transpose under
the termwise adjunction. The injective right-derived comparison maps identify its class
with the canonical derived exchange of the underived mate. Uniqueness of lifts gives
independence and naturality. The bounded-below derived-adjunction unit formula transposes
this construction to `Rf_*(eta_g')`. The two composite comparison maps in
`CompositionNormalization` identify it with `Rg_*(beta) eta_g`. This proves both clauses.
No Cartesianity or exactness of the horizontal module pullbacks is used. The pullbacks here
are left adjoints to the specified induced module direct images, hence are the tensor
pullbacks up to their unique adjunction-preserving identifications.
-/
theorem flatRingedSquareDerivedMate
    {C D C' D' : Type u}
    [SmallCategory C] [SmallCategory D] [SmallCategory C'] [SmallCategory D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {J' : GrothendieckTopology C'} {K' : GrothendieckTopology D'}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (A' : Sheaf J' CommRingCat.{u}) (B' : Sheaf K' CommRingCat.{u})
    (f : RingedToposMorphism ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (f' : RingedToposMorphism ((sheafCompose J' (forget₂ CommRingCat RingCat)).obj A')
      ((sheafCompose K' (forget₂ CommRingCat RingCat)).obj B'))
    (g' : RingedToposMorphism ((sheafCompose J' (forget₂ CommRingCat RingCat)).obj A')
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (g : RingedToposMorphism ((sheafCompose K' (forget₂ CommRingCat RingCat)).obj B')
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (square : f'.modules ⋙ g.modules ≅ g'.modules ⋙ f.modules)
    (squareSets : f'.direct ⋙ g.direct ≅ g'.direct ⋙ f.direct)
    (square_underlying : ∀ M : FlatRingedSquare.Modules A',
      (SheafOfModules.toSheaf _ ⋙ sheafCompose K (forget AddCommGrpCat)).map
            (square.hom.app M) ≫
          f.underlying.hom.app (g'.modules.obj M) ≫
          f.direct.map (g'.underlying.hom.app M) =
        g.underlying.hom.app (f'.modules.obj M) ≫
          g.direct.map (f'.underlying.hom.app M) ≫
          squareSets.hom.app
            ((SheafOfModules.toSheaf _ ⋙ sheafCompose J' (forget AddCommGrpCat)).obj M))
    {gStar : FlatRingedSquare.Modules B ⥤ FlatRingedSquare.Modules B'}
    {gStar' : FlatRingedSquare.Modules A ⥤ FlatRingedSquare.Modules A'}
    (adjG : gStar ⊣ g.modules) (adjG' : gStar' ⊣ g'.modules)
    [gStar.Additive] [gStar'.Additive]
    [PreservesFiniteLimits gStar] [PreservesFiniteColimits gStar]
    [PreservesFiniteLimits gStar'] [PreservesFiniteColimits gStar']
    [HasDerivedCategory.{w₁} (FlatRingedSquare.Modules A)]
    [HasDerivedCategory.{w₂} (FlatRingedSquare.Modules B)]
    [HasDerivedCategory.{w₃} (FlatRingedSquare.Modules A')]
    [HasDerivedCategory.{w₄} (FlatRingedSquare.Modules B')]
    [EnoughInjectives (FlatRingedSquare.Modules A)]
    [EnoughInjectives (FlatRingedSquare.Modules A')]
    [EnoughInjectives (FlatRingedSquare.Modules B')]
    (κ : f'.modules.rightDerivedFunctorPlus ⋙ g.modules.rightDerivedFunctorPlus ≅
      g'.modules.rightDerivedFunctorPlus ⋙ f.modules.rightDerivedFunctorPlus)
    (hκ : FlatRingedSquare.CompositionNormalization square κ) :
    ∃ β : f.modules.rightDerivedFunctorPlus ⋙ gStar.mapDerivedCategoryPlus ⟶
        gStar'.mapDerivedCategoryPlus ⋙ f'.modules.rightDerivedFunctorPlus,
      β = FlatRingedSquare.exchange adjG adjG' square ∧
      FlatRingedSquare.LiftNormalization adjG adjG' square β ∧
      FlatRingedSquare.UnitNormalization adjG adjG' κ β := by
  sorry

end CategoryTheory
