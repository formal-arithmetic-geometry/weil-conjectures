/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CoefficientSystemDerivedImage.CoefficientSystemImageData
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison
import WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.Retract
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-! # Unbounded evaluation comparison for strict coefficient systems

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Project, Tags 09T5 and 0D6E.
-/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option linter.unusedSectionVars false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v u' v' w d
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules

attribute [local instance] CoefficientEvaluationExtensionData.extensionAdditive

section Abstract
universe a av b bv
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
  (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] (a : F ⊣ G)

section Square
universe c cv e ev
variable {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{d} C]
  {D : Type e} [Category.{ev} D] [Abelian D] [HasDerivedCategory.{d} D]
  (eA : A ⥤ C) (eB : B ⥤ D) (Fl : C ⥤ D)
  [eA.Additive] [eB.Additive] [Fl.Additive]
  (FD : DerivedCategory A ⥤ DerivedCategory B)
  (EA : DerivedCategory A ⥤ DerivedCategory C)
  (EB : DerivedCategory B ⥤ DerivedCategory D)
  (FlD : DerivedCategory C ⥤ DerivedCategory D)
  (φF : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φA : DerivedCategory.Q ⋙ EA ≅ eA.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φB : DerivedCategory.Q ⋙ EB ≅ eB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φl : DerivedCategory.Q ⋙ FlD ≅ Fl.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (α : F ⋙ eB ≅ eA ⋙ Fl)

end Square

section Mate
universe c cv e ev
variable {C : Type c} [Category.{cv} C] {D : Type e} [Category.{ev} D]
  {Fs : A ⥤ B} {Gs : B ⥤ A} (asys : Fs ⊣ Gs)
  {Fl : C ⥤ D} {Gl : D ⥤ C} (alevel : Fl ⊣ Gl)
  {EA : A ⥤ C} {EB : B ⥤ D} (α : Fs ⋙ EB ≅ EA ⋙ Fl)

end Mate

section MateNaturality
universe c cv e ev
variable {C : Type c} [Category.{cv} C] {D : Type e} [Category.{ev} D]
  {Fs : A ⥤ B} {Gs : B ⥤ A} (asys : Fs ⊣ Gs)
  {Fl : C ⥤ D} {Gl : D ⥤ C} (alevel : Fl ⊣ Gl)
  {EA EA' : A ⥤ C} {EB EB' : B ⥤ D}

section Grid
universe c' cv' e' ev'
variable {C' : Type c'} [Category.{cv'} C'] {D' : Type e'} [Category.{ev'} D']
  {Fn : C' ⥤ D'} {Gn : D' ⥤ C'} (an : Fn ⊣ Gn)
  (RA : C' ⥤ C) (RB : D' ⥤ D)
  (EA₀ : A ⥤ C) (EA₁ : A ⥤ C') (EB₀ : B ⥤ D) (EB₁ : B ⥤ D')
  (α₀ : Fs ⋙ EB₀ ≅ EA₀ ⋙ Fl) (α₁ : Fs ⋙ EB₁ ≅ EA₁ ⋙ Fn)
  (δ : RA ⋙ Fl ≅ Fn ⋙ RB)
  (tA : EA₀ ⟶ EA₁ ⋙ RA) (tB : EB₀ ⟶ EB₁ ⋙ RB)

end Grid

end MateNaturality

section TensorSquare

universe c cv e ev
variable {C : Type c} [Category.{cv} C] {D : Type e} [Category.{ev} D]
  (TA : A ⥤ C) (RA : C ⥤ A) (TB : B ⥤ D) (RB : D ⥤ B)
  (Fn : C ⥤ D) (Gn : D ⥤ C)
  (aTA : TA ⊣ RA) (aTB : TB ⊣ RB) (an : Fn ⊣ Gn)
  (β : RA ⋙ F ≅ Fn ⋙ RB)

end TensorSquare

section DerivedLeftSquare

universe c cv e ev
variable {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{d} C]
  {D : Type e} [Category.{ev} D] [Abelian D] [HasDerivedCategory.{d} D]
  (TA : A ⥤ C) (RA : C ⥤ A) (TB : B ⥤ D) (RB : D ⥤ B)
  [TA.Additive] [RA.Additive] [TB.Additive] [RB.Additive]
  (aTA : TA ⊣ RA) (aTB : TB ⊣ RB)
  (pA : CochainComplex A ℤ → Prop) (pB : CochainComplex B ℤ → Prop)
  (DA : DerivedCoefficientScalarExtension TA RA aTA pA)
  (DB : DerivedCoefficientScalarExtension TB RB aTB pB)
  (Fn : C ⥤ D) [Fn.Additive]
  (FD : DerivedCategory A ⥤ DerivedCategory B)
  (FnD : DerivedCategory C ⥤ DerivedCategory D)
  (φF : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φn : DerivedCategory.Q ⋙ FnD ≅ Fn.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (β : RA ⋙ F ≅ Fn ⋙ RB)
  (βD : DA.restriction ⋙ FD ≅ FnD ⋙ DB.restriction)
  (hβD : ∀ K,
    βD.hom.app (DerivedCategory.Q.obj K) ≫
      DB.restriction.map (φn.hom.app K) ≫
      DB.restrictionFactors.hom.app ((Fn.mapHomologicalComplex (.up ℤ)).obj K) =
    FD.map (DA.restrictionFactors.hom.app K) ≫
      φF.hom.app ((RA.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex β (.up ℤ)).hom.app K))
  (ι : F ⋙ TB ≅ TA ⋙ Fn)
  (hι : ∀ P, aTB.homEquiv _ _ (ι.hom.app P) =
    F.map (aTA.unit.app P) ≫ β.hom.app (TA.obj P))

end DerivedLeftSquare

end Abstract

section TransitionLocalization

universe a av b bv cn cnv cm cmv dn dnv dm dmv
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
  {Cn : Type cn} [Category.{cnv} Cn] [Abelian Cn] [HasDerivedCategory.{d} Cn]
  {Cm : Type cm} [Category.{cmv} Cm] [Abelian Cm] [HasDerivedCategory.{d} Cm]
  {Dn : Type dn} [Category.{dnv} Dn] [Abelian Dn] [HasDerivedCategory.{d} Dn]
  {Dm : Type dm} [Category.{dmv} Dm] [Abelian Dm] [HasDerivedCategory.{d} Dm]
  (F : A ⥤ B) (eAn : A ⥤ Cn) (eAm : A ⥤ Cm)
  (eBn : B ⥤ Dn) (eBm : B ⥤ Dm) (Fn : Cn ⥤ Dn) (Fm : Cm ⥤ Dm)
  (RA : Cn ⥤ Cm) (RB : Dn ⥤ Dm)
  [F.Additive] [eAn.Additive] [eAm.Additive] [eBn.Additive] [eBm.Additive]
  [Fn.Additive] [Fm.Additive] [RA.Additive] [RB.Additive]
  (FD : DerivedCategory A ⥤ DerivedCategory B)
  (AnD : DerivedCategory A ⥤ DerivedCategory Cn)
  (AmD : DerivedCategory A ⥤ DerivedCategory Cm)
  (BnD : DerivedCategory B ⥤ DerivedCategory Dn)
  (BmD : DerivedCategory B ⥤ DerivedCategory Dm)
  (FnD : DerivedCategory Cn ⥤ DerivedCategory Dn)
  (FmD : DerivedCategory Cm ⥤ DerivedCategory Dm)
  (RAD : DerivedCategory Cn ⥤ DerivedCategory Cm)
  (RBD : DerivedCategory Dn ⥤ DerivedCategory Dm)
  (φF : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φAn : DerivedCategory.Q ⋙ AnD ≅ eAn.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φAm : DerivedCategory.Q ⋙ AmD ≅ eAm.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φBn : DerivedCategory.Q ⋙ BnD ≅ eBn.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φBm : DerivedCategory.Q ⋙ BmD ≅ eBm.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φFn : DerivedCategory.Q ⋙ FnD ≅ Fn.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φFm : DerivedCategory.Q ⋙ FmD ≅ Fm.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φRA : DerivedCategory.Q ⋙ RAD ≅ RA.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φRB : DerivedCategory.Q ⋙ RBD ≅ RB.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (αn : F ⋙ eBn ≅ eAn ⋙ Fn) (αm : F ⋙ eBm ≅ eAm ⋙ Fm)
  (β : RA ⋙ Fm ≅ Fn ⋙ RB)
  (αnD : FD ⋙ BnD ≅ AnD ⋙ FnD) (αmD : FD ⋙ BmD ≅ AmD ⋙ FmD)
  (βD : RAD ⋙ FmD ≅ FnD ⋙ RBD)
  (tA : eAm ⟶ eAn ⋙ RA) (tB : eBm ⟶ eBn ⋙ RB)
  (tAD : AmD ⟶ AnD ⋙ RAD) (tBD : BmD ⟶ BnD ⋙ RBD)
  (hαn : ∀ P, αnD.hom.app (DerivedCategory.Q.obj P) ≫
    FnD.map (φAn.hom.app P) ≫ φFn.hom.app ((eAn.mapHomologicalComplex (.up ℤ)).obj P) =
    BnD.map (φF.hom.app P) ≫ φBn.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex αn (.up ℤ)).hom.app P))
  (hαm : ∀ P, αmD.hom.app (DerivedCategory.Q.obj P) ≫
    FmD.map (φAm.hom.app P) ≫ φFm.hom.app ((eAm.mapHomologicalComplex (.up ℤ)).obj P) =
    BmD.map (φF.hom.app P) ≫ φBm.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex αm (.up ℤ)).hom.app P))
  (hβD : ∀ P, βD.hom.app (DerivedCategory.Q.obj P) ≫
    RBD.map (φFn.hom.app P) ≫ φRB.hom.app ((Fn.mapHomologicalComplex (.up ℤ)).obj P) =
    FmD.map (φRA.hom.app P) ≫ φFm.hom.app ((RA.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex β (.up ℤ)).hom.app P))
  (htA : ∀ P, tAD.app (DerivedCategory.Q.obj P) ≫ RAD.map (φAn.hom.app P) ≫
    φRA.hom.app ((eAn.mapHomologicalComplex (.up ℤ)).obj P) =
    φAm.hom.app P ≫ DerivedCategory.Q.map ((tA.mapHomologicalComplex (.up ℤ)).app P))
  (htB : ∀ P, tBD.app (DerivedCategory.Q.obj P) ≫ RBD.map (φBn.hom.app P) ≫
    φRB.hom.app ((eBn.mapHomologicalComplex (.up ℤ)).obj P) =
    φBm.hom.app P ≫ DerivedCategory.Q.map ((tB.mapHomologicalComplex (.up ℤ)).app P))
  (ho : ∀ M, tB.app (F.obj M) ≫ RB.map (αn.hom.app M) =
    αm.hom.app M ≫ Fm.map (tA.app M) ≫ β.hom.app (eAn.obj M))

end TransitionLocalization

section OrdinaryRestriction

universe a₀v a₁v b₀v b₁v xv yv a₀u a₁u b₀u b₁u xu yu
variable {A₀ : Type a₀u} [Category.{a₀v} A₀] {A₁ : Type a₁u} [Category.{a₁v} A₁]
  {B₀ : Type b₀u} [Category.{b₀v} B₀] {B₁ : Type b₁u} [Category.{b₁v} B₁]
  {X : Type xu} [Category.{xv} X] {Y : Type yu} [Category.{yv} Y]
  (F₀ : A₀ ⥤ B₀) (G₀ : B₀ ⥤ A₀) (a₀ : F₀ ⊣ G₀)
  (F₁ : A₁ ⥤ B₁) (G₁ : B₁ ⥤ A₁) (a₁ : F₁ ⊣ G₁)
  (RA : A₀ ⥤ A₁) (RB : B₀ ⥤ B₁)
  (Ua : A₁ ⥤ X) (Un : A₀ ⥤ X) (Ub : B₁ ⥤ Y) (Uq : B₀ ⥤ Y)
  [Ua.ReflectsIsomorphisms]
  (L : X ⥤ Y) (V : Y ⥤ X) (adj : L ⊣ V)
  (ra : RA ⋙ Ua ≅ Un) (rb : RB ⋙ Ub ≅ Uq)
  (mu₀ : F₀ ⋙ Uq ≅ Un ⋙ L) (mu₁ : F₁ ⋙ Ub ≅ Ua ⋙ L)
  (γ₀ : G₀ ⋙ Un ≅ Uq ⋙ V) (γ₁ : G₁ ⋙ Ua ≅ Ub ⋙ V)
  (β : RA ⋙ F₁ ≅ F₀ ⋙ RB)
  (h₀ : ∀ M N (f : F₀.obj M ⟶ N),
    Un.map (a₀.homEquiv M N f) ≫ γ₀.hom.app N =
      adj.homEquiv _ _ (mu₀.inv.app M ≫ Uq.map f))
  (h₁ : ∀ M N (f : F₁.obj M ⟶ N),
    Ua.map (a₁.homEquiv M N f) ≫ γ₁.hom.app N =
      adj.homEquiv _ _ (mu₁.inv.app M ≫ Ub.map f))
  (hβ : ∀ M, Ub.map (β.hom.app M) ≫ rb.hom.app (F₀.obj M) ≫ mu₀.hom.app M =
    mu₁.hom.app (RA.obj M) ≫ L.map (ra.hom.app M))

end OrdinaryRestriction

section Assembly

universe a av b bv c cv e ev
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]
  {MA : ℕ → Type c} [∀ n, Category.{cv} (MA n)] [∀ n, Abelian (MA n)]
  [∀ n, HasDerivedCategory.{d} (MA n)]
  {MB : ℕ → Type e} [∀ n, Category.{ev} (MB n)] [∀ n, Abelian (MB n)]
  [∀ n, HasDerivedCategory.{d} (MB n)]
  {eA : ∀ n, A ⥤ MA n} [∀ n, (eA n).Additive]
  {eB : ∀ n, B ⥤ MB n} [∀ n, (eB n).Additive]
  {RA : ∀ {m n : ℕ}, n ≤ m → MA n ⥤ MA m} [∀ m n (h : n ≤ m), (RA h).Additive]
  {RB : ∀ {m n : ℕ}, n ≤ m → MB n ⥤ MB m} [∀ m n (h : n ≤ m), (RB h).Additive]
  {TA : ∀ {m n : ℕ}, n ≤ m → MA m ⥤ MA n} [∀ m n (h : n ≤ m), (TA h).Additive]
  {TB : ∀ {m n : ℕ}, n ≤ m → MB m ⥤ MB n} [∀ m n (h : n ≤ m), (TB h).Additive]
  {atA : ∀ {m n : ℕ} (h : n ≤ m), TA h ⊣ RA h}
  {atB : ∀ {m n : ℕ} (h : n ≤ m), TB h ⊣ RB h}
  {KFA : ∀ n, CochainComplex (MA n) ℤ → Prop} {FlatA : ∀ n, MA n → Prop}
  {KFB : ∀ n, CochainComplex (MB n) ℤ → Prop} {FlatB : ∀ n, MB n → Prop}
  {TN₁ : (∀ {m n : ℕ} (h : n ≤ m), eA m ⟶ eA n ⋙ RA h) → Prop}
  {TN₂ : (∀ {m n : ℕ} (h : n ≤ m), eB m ⟶ eB n ⋙ RB h) → Prop}
  {UN₁ : (∀ n, TA (Nat.le_refl n) ≅ 𝟭 (MA n)) → Prop}
  {UN₂ : (∀ n, TB (Nat.le_refl n) ≅ 𝟭 (MB n)) → Prop}
  {AN₁ : (∀ {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m),
    TA h₁ ⋙ TA h₂ ≅ TA (h₂.trans h₁)) → Prop}
  {AN₂ : (∀ {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m),
    TB h₁ ⋙ TB h₂ ≅ TB (h₂.trans h₁)) → Prop}

variable (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (a : F ⊣ G)
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (Fl : ∀ n, MA n ⥤ MB n) (Gl : ∀ n, MB n ⥤ MA n)
  [∀ n, (Fl n).Additive] [∀ n, (Gl n).Additive] (al : ∀ n, Fl n ⊣ Gl n)
  (PY : CoefficientEvaluationExtensionData eA RA TA atA KFA FlatA TN₁ UN₁ AN₁)
  (PX : CoefficientEvaluationExtensionData eB RB TB atB KFB FlatB TN₂ UN₂ AN₂)
  (α : ∀ n, F ⋙ eB n ≅ eA n ⋙ Fl n)
  (β : ∀ {m n : ℕ} (h : n ≤ m), RA h ⋙ Fl m ≅ Fl n ⋙ RB h)
  (ds : CoefficientDerivedImage F G a)
  (dl : ∀ n, CoefficientDerivedImage (Fl n) (Gl n) (al n))
  (hr : ∀ n (K : CochainComplex (MA n) ℤ),
    ∃ (P : CochainComplex (MA n) ℤ) (q : P ⟶ K), QuasiIso q ∧ KFA n P ∧
      (∀ i : ℤ, FlatA n (P.X i)) ∧ KFB n (((Fl n).mapHomologicalComplex (.up ℤ)).obj P) ∧
        ∀ i : ℤ, FlatB n ((Fl n).obj (P.X i)))
  (hRestr : ∀ {m n : ℕ} (h : n ≤ m),
    IsIso (mateEquiv (al n) (al m) (TwoSquare.mk _ _ _ _ (β h).hom)).natTrans)
  (hEval : ∀ n,
    IsIso (mateEquiv a (al n) (TwoSquare.mk _ _ _ _ (α n).inv)).natTrans)
  (hTrans : ∀ {m n : ℕ} (h : n ≤ m) M,
    (PX.strictTransition h).app (F.obj M) ≫ (RB h).map ((α n).hom.app M) =
    (α m).hom.app M ≫ (Fl m).map ((PY.strictTransition h).app M) ≫
      (β h).hom.app ((eA n).obj M))

end Assembly

section CommonResolution

open CategoryTheory.MonoidalCategory
open scoped ZeroObject

universe a av b bv
variable {A : Type a} [Category.{av} A] [Abelian A]
  [MonoidalCategory A] [MonoidalPreadditive A] [HasColimitsOfSize.{0, 0} A]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ M : A, PreservesColimitsOfShape ℤ ((curriedTensor A).obj M)]
  [∀ M : A, PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj M)]
  [HasExactColimitsOfShape ℤ A]
  {B : Type b} [Category.{bv} B] [Abelian B]
  [MonoidalCategory B] [MonoidalPreadditive B] [HasColimitsOfSize.{0, 0} B]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ B, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ B, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ M : B, PreservesColimitsOfShape ℤ ((curriedTensor B).obj M)]
  [∀ M : B, PreservesColimitsOfShape ℤ ((curriedTensor B).flip.obj M)]
  [HasExactColimitsOfShape ℤ B]
  (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] (ad : F ⊣ G)
  (T : A ⥤ A) (π : T ⟶ 𝟭 A) [∀ M, Epi (π.app M)]
  (hT : ∀ M, ObjectProperty.flat (T.obj M) ∧ ObjectProperty.flat (F.obj (T.obj M)))

end CommonResolution

section FreeModules

open CategoryTheory.SheafFreeModule CategoryTheory.MonoidalCategory

variable {C₀ : Type u} [Category.{v} C₀] [EssentiallySmall.{w} C₀]
  {J₀ : GrothendieckTopology C₀}
  [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J₀.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J₀ AddCommGrpCat.{w}]
  [HasWeakSheafify J₀ AddCommGrpCat.{w}]
  [HasWeakSheafify J₀ CommRingCat.{w}] [HasWeakSheafify J₀ (Type w)]
  [J₀.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J₀.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (R : Sheaf J₀ CommRingCat.{w})

section AdaptedResolution

open scoped ZeroObject

variable {D₀ : Type u'} [Category.{v'} D₀] [EssentiallySmall.{w} D₀]
  {K₀ : GrothendieckTopology D₀}
  [K₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K₀.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K₀ AddCommGrpCat.{w}]
  [HasWeakSheafify K₀ AddCommGrpCat.{w}]
  [HasWeakSheafify K₀ CommRingCat.{w}] [HasWeakSheafify K₀ (Type w)]
  [K₀.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K₀.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (R' : Sheaf K₀ CommRingCat.{w})
  (L₀ : Sheaf J₀ (Type w) ⥤ Sheaf K₀ (Type w))
  (V₀ : Sheaf K₀ (Type w) ⥤ Sheaf J₀ (Type w)) (adj₀ : L₀ ⊣ V₀)
  (F₀ : SheafOfModules.{w} (ring R) ⥤ SheafOfModules.{w} (ring R'))
  (G₀ : SheafOfModules.{w} (ring R') ⥤ SheafOfModules.{w} (ring R))
  [F₀.Additive] [PreservesFiniteLimits F₀] (a₀ : F₀ ⊣ G₀)
  (e₀ : G₀ ⋙ underlyingRaw R ≅ underlyingRaw R' ⋙ V₀)

end AdaptedResolution

end FreeModules

@[expose] public section

attribute [local irreducible] coefficientQuotientSheaf coefficientQuotientMap

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (O : Type w) [CommRing O] (ell : O)

variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)

variable [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := K) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := K) O ell)]

end

end SheafOfModules
