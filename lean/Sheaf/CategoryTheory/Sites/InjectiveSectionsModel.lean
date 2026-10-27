/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.Sites.PullbackInjectiveEvaluationAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

/-!
# Injective representatives and the two ordinary section models

Source: Stacks Project, Cohomology on Sites, Tag 0DD8, first proof sentence;
Tags 013K, 0D6X, 015E and 05TI
(blueprint: lem-trf-site-injective-sections-model).

The functor called `sheafPushforwardContinuous` by Mathlib is precomposition.
For the cocontinuous site functor in this statement it is the abelian inverse
image of the induced geometric morphism. The existentially bound continuity
and exactness instances below are proof data for that particular functor, not
choices of an inverse-image functor or additional hypotheses.

## Main definitions and statement

* `modelMap`: the specified ordinary right-derived comparison composite.
* `imageIso`: exact inverse image of a representative isomorphism.
* `injective_sections_model`: existence, acyclicity, invertibility and naturality.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w u₁ v₁ u₂ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SiteInjectiveSectionsModel

section Maps

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]

/-- The specified comparison map: the ordinary derived unit followed by the
image of the representative isomorphism. No inverse of a merely existential
comparison is chosen. Source: Stacks, Derived Categories, 05TI and 015E
(blueprint: lem-trf-site-injective-sections-model). -/
def modelMap (F : A ⥤ B) [F.Additive] [EnoughInjectives A]
    (I : CochainComplex.Plus A) (M : DerivedCategory.Plus A)
    (ρ : DerivedCategory.Plus.Q.obj I ≅ M) :
    DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj I) ⟶
      F.rightDerivedFunctorPlus.obj M :=
  F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj I) ≫
    F.rightDerivedFunctorPlus.map ρ.hom

/-- The image of a representative isomorphism under exact inverse image, with
its canonical localization factorization. Source: Stacks, Sites, 00YV and
Derived Categories, 05TI (blueprint: lem-trf-site-injective-sections-model). -/
def imageIso (L : A ⥤ B) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (I : CochainComplex.Plus A) (M : DerivedCategory.Plus A)
    (ρ : DerivedCategory.Plus.Q.obj I ≅ M) :
    DerivedCategory.Plus.Q.obj (L.mapCochainComplexPlus.obj I) ≅
      L.mapDerivedCategoryPlus.obj M :=
  L.mapDerivedCategoryPlusFactorsh.symm.app ((HomotopyCategory.Plus.quotient A).obj I) ≪≫
    L.mapDerivedCategoryPlus.mapIso ρ

end Maps

/-- The two ordinary section models, with their specified comparison units and
naturality in chain maps and coefficient maps.

Source: Stacks Project, Cohomology on Sites, 0DD8, first proof sentence
(blueprint: lem-trf-site-injective-sections-model).

Proof:
1. The site axioms and continuity on covering pullbacks make precomposition a
   sheaf functor (00WV/00WW). Its sectionwise operations are additive. The
   continuous-cocontinuous adjunction makes it left adjoint, while limits are
   sectionwise, hence it is exact (00XR/00YV); equivalently use
   lem-pe-constant-left-module-inverse-image at the integers.
2. Abelian sheaves have enough injectives. Apply
   lem-weil-pbc-dplus-injective-representative at the prescribed bound a to
   obtain I and ρ. Fix any such representative for the remaining assertions.
3. Exact additive inverse image preserves zero terms and maps ρ to an
   isomorphism. The canonical factorization through localization gives imageIso.
4. Apply lem-trf-site-pullback-injective-evaluation-acyclic to every injective
   term I^n, giving vanishing in all positive evaluation degrees.
5. Apply lem-weil-pbc-right-derived-plus-injective to evaluation at f(U) and I.
   Apply src-right-derived-functor-plus-acyclic-unit to evaluation at U and LI,
   using step 4. Thus both units are isomorphisms. Composing them with derived
   evaluation of ρ and imageIso gives exactly the two modelMap morphisms.
6. Naturality of each unit says RF(Qs) α = α QF(s). Apply RF to the given
   equation Qt ≫ ρ' = ρ ≫ c and use functoriality and associativity. This gives
   the first equation. Apply exact inverse image to that equation and use the
   naturality of its localization factorization; the same calculation for
   evaluation at U gives the second equation. -/
theorem injective_sections_model
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (f : C ⥤ D)
    (hcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map f ∈ K (f.obj X))
    (hpullback : ∀ (X Y Z : C) (S : Presieve X), S ∈ J X →
      ∀ (b : Y ⟶ X) (c : Z ⟶ X), S b → PreservesLimit (cospan b c) f)
    [f.IsCocontinuous J.toGrothendieck K.toGrothendieck]
    [HasDerivedCategory.{w} (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    [HasDerivedCategory.{w} (Sheaf K.toGrothendieck AddCommGrpCat.{u})]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    (U : C) (M : DerivedCategory.Plus (Sheaf K.toGrothendieck AddCommGrpCat.{u}))
    (a : ℤ) [M.IsGE a] :
    ∃ (_hc : f.IsContinuous J.toGrothendieck K.toGrothendieck),
    ∃ (_ha : (f.sheafPushforwardContinuous AddCommGrpCat.{u}
      J.toGrothendieck K.toGrothendieck).Additive),
    ∃ (_hl : PreservesFiniteLimits (f.sheafPushforwardContinuous AddCommGrpCat.{u}
      J.toGrothendieck K.toGrothendieck)),
    ∃ (_hr : PreservesFiniteColimits (f.sheafPushforwardContinuous AddCommGrpCat.{u}
      J.toGrothendieck K.toGrothendieck)),
      (∃ I : CochainComplex.Plus (Sheaf K.toGrothendieck AddCommGrpCat.{u}),
        I.obj.IsStrictlyGE a ∧ (∀ n : ℤ, Injective (I.obj.X n)) ∧
          Nonempty (DerivedCategory.Plus.Q.obj I ≅ M)) ∧
      ∀ (I : CochainComplex.Plus (Sheaf K.toGrothendieck AddCommGrpCat.{u}))
        (_hI : I.obj.IsStrictlyGE a) (_hinj : ∀ n : ℤ, Injective (I.obj.X n))
        (ρ : DerivedCategory.Plus.Q.obj I ≅ M),
        ((f.sheafPushforwardContinuous AddCommGrpCat.{u}
          J.toGrothendieck K.toGrothendieck).mapCochainComplexPlus.obj I).obj.IsStrictlyGE a ∧
        (∀ (n : ℤ) (p : ℕ), 0 < p →
          IsZero (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
            (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived p).obj
              ((f.sheafPushforwardContinuous AddCommGrpCat.{u}
                J.toGrothendieck K.toGrothendieck).obj (I.obj.X n)))) ∧
        IsIso (modelMap (sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (f.obj U))) I M ρ) ∧
        IsIso (modelMap (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))
          ((f.sheafPushforwardContinuous AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck).mapCochainComplexPlus.obj I)
          ((f.sheafPushforwardContinuous AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck).mapDerivedCategoryPlus.obj M)
          (imageIso (f.sheafPushforwardContinuous AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck) I M ρ)) ∧
        ∀ (M' : DerivedCategory.Plus (Sheaf K.toGrothendieck AddCommGrpCat.{u}))
          (I' : CochainComplex.Plus (Sheaf K.toGrothendieck AddCommGrpCat.{u}))
          (_hinj' : ∀ n : ℤ, Injective (I'.obj.X n))
          (ρ' : DerivedCategory.Plus.Q.obj I' ≅ M') (t : I ⟶ I') (c : M ⟶ M'),
          DerivedCategory.Plus.Q.map t ≫ ρ'.hom = ρ.hom ≫ c →
            (modelMap (sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
              (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (f.obj U))) I M ρ ≫
                (sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
                  (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj
                    (op (f.obj U))).rightDerivedFunctorPlus.map c =
              DerivedCategory.Plus.Q.map
                ((sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
                  (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj
                    (op (f.obj U))).mapCochainComplexPlus.map t) ≫
                modelMap (sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u} ⋙
                  (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op (f.obj U))) I' M' ρ') ∧
            (modelMap (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
              (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))
              ((f.sheafPushforwardContinuous AddCommGrpCat.{u}
                J.toGrothendieck K.toGrothendieck).mapCochainComplexPlus.obj I)
              ((f.sheafPushforwardContinuous AddCommGrpCat.{u}
                J.toGrothendieck K.toGrothendieck).mapDerivedCategoryPlus.obj M)
              (imageIso (f.sheafPushforwardContinuous AddCommGrpCat.{u}
                J.toGrothendieck K.toGrothendieck) I M ρ) ≫
                (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
                  (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerivedFunctorPlus.map
                  ((f.sheafPushforwardContinuous AddCommGrpCat.{u}
                    J.toGrothendieck K.toGrothendieck).mapDerivedCategoryPlus.map c) =
              DerivedCategory.Plus.Q.map
                ((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
                  (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapCochainComplexPlus.map
                  ((f.sheafPushforwardContinuous AddCommGrpCat.{u}
                    J.toGrothendieck K.toGrothendieck).mapCochainComplexPlus.map t)) ≫
                modelMap (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{u} ⋙
                  (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))
                  ((f.sheafPushforwardContinuous AddCommGrpCat.{u}
                    J.toGrothendieck K.toGrothendieck).mapCochainComplexPlus.obj I')
                  ((f.sheafPushforwardContinuous AddCommGrpCat.{u}
                    J.toGrothendieck K.toGrothendieck).mapDerivedCategoryPlus.obj M')
                  (imageIso (f.sheafPushforwardContinuous AddCommGrpCat.{u}
                    J.toGrothendieck K.toGrothendieck) I' M' ρ')) := by
  sorry

end CategoryTheory.SiteInjectiveSectionsModel
