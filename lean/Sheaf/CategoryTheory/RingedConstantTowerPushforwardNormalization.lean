/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Constant strict towers and ringed direct image

Source: Stacks Project, Cohomology on Sites, Tag 0A07, lemma-Rf-commutes-with-Rlim,
diagram-topos proof, specialized to constant towers
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization).

The natural number n denotes positive tower level n+1. The comparisons supplied as
parameters below are characterized by their ordinary localization equations; they are
models of the specified derived operations, rather than additional geometric assumptions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.all false
set_option linter.unusedVariables false
universe u v w uA vA wA wTA uB vB wB wTB
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Additivity of the exact constant tower functor, obtained from its preserved products.
Source: Stacks Project, Tag 0A07, constant diagram specialization
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization). -/
instance ringedConstantTowerAdditive
    (A : Type uA) [Category.{vA} A] [Abelian A] :
    (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Canonical evaluation of an exact constant strict tower, using the ordinary identity.
Source: Stacks Project, Tag 0A07, constant diagram specialization
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization). -/
def ringedConstantTowerEvaluation
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] (n : ℕᵒᵖ) :
    (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory ⋙
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory ≅ 𝟭 (DerivedCategory A) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.constCompEvaluationObj (D := A) n) ≪≫
      Functor.mapDerivedCategoryIdIso A

/-- The canonical constant-tower/exact-pullback interchange. Its ordinary components
are identities, as specified by compConstIso.
Source: Stacks Project, Tag 0A07, constant diagram specialization
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization). -/
def ringedConstantTowerPullback
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)).mapDerivedCategory ⋙
        ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory ≅
      F.mapDerivedCategory ⋙
        (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F).symm ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Instance shortcut: the abelian structure of module sheaves on a small ringed site,
the inherited Mathlib `SheafOfModules` instance, recorded once for the statement below.
Source: Stacks Project, Modules on Sites, sheaves of modules; Tag 0A07, constant diagram
specialization (blueprint: lem-weil-pbc-constant-tower-pushforward-normalization). -/
instance ringedConstantTowerModulesAbelian
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) :
    Abelian (ringedSiteModules.{u} R) :=
  inferInstance

/-- Instance shortcut: strict inverse sequences of module sheaves form the abelian functor
category, with levelwise kernels and cokernels (Mathlib's `functorCategoryAbelian`).
Source: Stacks Project, Tag 0A07, constant diagram specialization
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization). -/
instance ringedConstantTowerTowersAbelian
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) :
    Abelian (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) :=
  inferInstance

/-- A constant strict tower commutes with total derived direct image, with the specified
representative, evaluation, limit and whole-tower counit normalizations.
Source: Stacks Project, Tag 0A07, lemma-Rf-commutes-with-Rlim, first proof;
Derived Categories, Tags 08BJ, 070K, 070I and 09T5
(blueprint: lem-weil-pbc-constant-tower-pushforward-normalization).

Proof plan (the eight steps of the node):
1. Apply small-module-diagrams-grothendieck to the point and the inverse-sequence category.
Functorial K-injective resolutions exist. Levelwise kernels and cokernels make constants,
evaluation and F on towers exact; exact-functor-derived-factorization localizes them.
2. A tower map to a constant tower is determined at terminal index 0. Hence evaluation at
0 is exact left adjoint to constants. Right-adjoint-preserves-kinjective implies that the
constant tower on a K-injective complex is K-injective.
3. The same preservation theorem for adj implies that GJ is K-injective. Both constant
complexes are K-injective, and their ordinary direct-image square is the identity square.
4. Define chi on QJ by the two derived units and this ordinary square. K-injective-total-
derived makes the units invertible. The K-injective Hom bijection and termwise-adjunction-
homotopy descend the construction naturally and independently of representatives.
5. Substitute the unit-normalization equation for beta in the representative equation for
chi. Cancel the invertible unit to obtain the displayed identity at every evaluation.
6. The cone of identity maps computes lim of a constant ordinary tower. Derive its unit
on a K-injective constant tower to obtain bR and bS, then descend by the same Hom bijection.
7. The normalization of a is the derived comparison of the common ordinary composite.
On the constant K-injective model it is the identity of GJ. Insert bR, bS and chi and cancel
to obtain the whole-map limit identity; no faithfulness of evaluated maps is asserted.
8. The Hom normalizations for d and dT compute their counits by ordinary counit chain maps
on J and its constant tower. The ordinary tower counit is the constant ordinary counit.
Localize this chain-map identity and insert the exact interchange to obtain the strict
counit equation in the derived category of towers. Naturality gives every derived object. -/
theorem ringedConstantTowerPushforwardNormalization
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J RingCat.{u}) (S : Sheaf K RingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} R)] [HasDerivedCategory.{w}
      (ringedSiteModules.{u} S)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R))] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤
      (ringedSiteModules.{u} S))]
    (f : RingedToposMorphism R S) [IsIso f.ringMap]
    (F : (ringedSiteModules.{u} S) ⥤ (ringedSiteModules.{u} R)) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ f.modules)
    (RG : DerivedCategory (ringedSiteModules.{u} R) ⥤ DerivedCategory (ringedSiteModules.{u} S))
    (RT : DerivedCategory (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ⥤ DerivedCategory (ℕᵒᵖ ⥤
      (ringedSiteModules.{u} S)))
    (LR : DerivedCategory (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ⥤ DerivedCategory (ringedSiteModules.{u}
      R))
    (LS : DerivedCategory (ℕᵒᵖ ⥤ (ringedSiteModules.{u} S)) ⥤ DerivedCategory (ringedSiteModules.{u}
      S))
    (η : f.modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG)
    (ηT : ((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} R) (ringedSiteModules.{u} S)).obj
      f.modules).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RT)
    (ηR : (lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ⥤ (ringedSiteModules.{u}
      R)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ LR)
    (ηS : (lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} S)) ⥤ (ringedSiteModules.{u}
      S)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ LS)
    [RG.IsRightDerivedFunctor η (HomologicalComplex.quasiIso (ringedSiteModules.{u} R) (.up ℤ))]
    [RT.IsRightDerivedFunctor ηT (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) (.up
      ℤ))]
    [LR.IsRightDerivedFunctor ηR (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) (.up
      ℤ))]
    [LS.IsRightDerivedFunctor ηS (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ (ringedSiteModules.{u} S)) (.up
      ℤ))]
    (c : (lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ⥤ (ringedSiteModules.{u} R)) ⋙ f.modules ≅
      ((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} R) (ringedSiteModules.{u} S)).obj
      f.modules) ⋙ (lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} S)) ⥤ (ringedSiteModules.{u} S)))
    (hc : ∀ M : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)), c.hom.app M = limit.post M f.modules)
    (a : LR ⋙ RG ≅ RT ⋙ LS)
    (ha : ∀ X : CochainComplex (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ℤ,
      η.app ((lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ⥤ (ringedSiteModules.{u}
        R)).mapHomologicalComplex (.up ℤ) |>.obj X) ≫
          RG.map (ηR.app X) ≫ a.hom.app (DerivedCategory.Q.obj X) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app X) ≫
          ηS.app (((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} R) (ringedSiteModules.{u}
            S)).obj f.modules).mapHomologicalComplex (.up ℤ) |>.obj X) ≫ LS.map (ηT.app X))
    (β : ∀ n : ℕᵒᵖ, RT ⋙ ((evaluation ℕᵒᵖ (ringedSiteModules.{u} S)).obj n).mapDerivedCategory ≅
      ((evaluation ℕᵒᵖ (ringedSiteModules.{u} R)).obj n).mapDerivedCategory ⋙ RG)
    (hβ : ∀ (n : ℕᵒᵖ) (I : CochainComplex (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ℤ), I.IsKInjective →
      (((evaluation ℕᵒᵖ (ringedSiteModules.{u} S)).obj) n).mapDerivedCategoryFactors.inv.app
          (((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} R) (ringedSiteModules.{u} S)).obj
            f.modules).mapHomologicalComplex (.up ℤ) |>.obj I) ≫
        (((evaluation ℕᵒᵖ (ringedSiteModules.{u} S)).obj n).mapDerivedCategory).map (ηT.app I) ≫ (β
          n).hom.app (DerivedCategory.Q.obj I) ≫
        RG.map ((((evaluation ℕᵒᵖ (ringedSiteModules.{u} R)).obj)
          n).mapDerivedCategoryFactors.hom.app I) =
      η.app ((((evaluation ℕᵒᵖ (ringedSiteModules.{u} R)).obj) n).mapHomologicalComplex (.up ℤ)
        |>.obj I))
    (d : F.mapDerivedCategory ⊣ RG)
    (dT : ((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} S) (ringedSiteModules.{u} R)).obj
      F).mapDerivedCategory ⊣ RT)
    (hd : ∀ (M : CochainComplex (ringedSiteModules.{u} S) ℤ) (I : CochainComplex
      (ringedSiteModules.{u} R) ℤ)
      (g : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
      d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
          (F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map g) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I g) ≫ η.app I)
    (hdT : ∀ (M : CochainComplex (ℕᵒᵖ ⥤ (ringedSiteModules.{u} S)) ℤ) (I : CochainComplex (ℕᵒᵖ ⥤
      (ringedSiteModules.{u} R)) ℤ)
      (g : (((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} S) (ringedSiteModules.{u} R)).obj
        F).mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
      dT.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
          (((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} S) (ringedSiteModules.{u} R)).obj
            F).mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map g) =
        DerivedCategory.Q.map
          (((adj.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).homEquiv M I g) ≫ ηT.app I) :
    ∃ (χ : RG ⋙ (Functor.const ℕᵒᵖ : (ringedSiteModules.{u} S) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
      S))).mapDerivedCategory ≅ (Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤
      (ringedSiteModules.{u} R))).mapDerivedCategory ⋙ RT)
      (bR : 𝟭 (DerivedCategory (ringedSiteModules.{u} R)) ≅ (Functor.const ℕᵒᵖ :
        (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R))).mapDerivedCategory ⋙ LR)
      (bS : 𝟭 (DerivedCategory (ringedSiteModules.{u} S)) ≅ (Functor.const ℕᵒᵖ :
        (ringedSiteModules.{u} S) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u} S))).mapDerivedCategory ⋙ LS),
      (∀ I : CochainComplex (ringedSiteModules.{u} R) ℤ, I.IsKInjective →
        (Functor.const ℕᵒᵖ : (ringedSiteModules.{u} S) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
          S))).mapDerivedCategory.map (η.app I) ≫ χ.hom.app (DerivedCategory.Q.obj I) ≫
            RT.map ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
              R))).mapDerivedCategoryFactors.hom.app I) =
          (Functor.const ℕᵒᵖ : (ringedSiteModules.{u} S) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
            S))).mapDerivedCategoryFactors.hom.app
              (f.modules.mapHomologicalComplex (.up ℤ) |>.obj I) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
              (Functor.compConstIso ℕᵒᵖ f.modules) (.up ℤ)).hom.app I) ≫
            ηT.app ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
              R))).mapHomologicalComplex (.up ℤ) |>.obj I)) ∧
      (∀ (M : DerivedCategory (ringedSiteModules.{u} R)) (n : ℕᵒᵖ),
        (ringedConstantTowerEvaluation (ringedSiteModules.{u} S) n).inv.app (RG.obj M) ≫
            (((evaluation ℕᵒᵖ (ringedSiteModules.{u} S)).obj n).mapDerivedCategory).map (χ.hom.app
              M) ≫ (β n).hom.app ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤
              (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R))).mapDerivedCategory.obj M) ≫
            RG.map ((ringedConstantTowerEvaluation (ringedSiteModules.{u} R) n).hom.app M) = 𝟙
              (RG.obj M)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} R) ℤ, I.IsKInjective →
        bR.hom.app (DerivedCategory.Q.obj I) ≫
            LR.map ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
              R))).mapDerivedCategoryFactors.hom.app I) =
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (constLimAdj : (Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤
              (ringedSiteModules.{u} R))) ⊣ (lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R)) ⥤
              (ringedSiteModules.{u} R))).unit (.up ℤ)).app I) ≫
            ηR.app ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
              R))).mapHomologicalComplex (.up ℤ) |>.obj I)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} S) ℤ, I.IsKInjective →
        bS.hom.app (DerivedCategory.Q.obj I) ≫
            LS.map ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} S) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
              S))).mapDerivedCategoryFactors.hom.app I) =
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (constLimAdj : (Functor.const ℕᵒᵖ : (ringedSiteModules.{u} S) ⥤ (ℕᵒᵖ ⥤
              (ringedSiteModules.{u} S))) ⊣ (lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{u} S)) ⥤
              (ringedSiteModules.{u} S))).unit (.up ℤ)).app I) ≫
            ηS.app ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} S) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
              S))).mapHomologicalComplex (.up ℤ) |>.obj I)) ∧
      (∀ M : DerivedCategory (ringedSiteModules.{u} R),
        RG.map (bR.hom.app M) ≫ a.hom.app ((Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤
          (ringedSiteModules.{u} R))).mapDerivedCategory.obj M) ≫
            LS.map (χ.inv.app M) ≫ bS.inv.app (RG.obj M) = 𝟙 (RG.obj M)) ∧
      (∀ M : DerivedCategory (ringedSiteModules.{u} R),
        ((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} S) (ringedSiteModules.{u} R)).obj
          F).mapDerivedCategory.map (χ.hom.app M) ≫ dT.counit.app ((Functor.const ℕᵒᵖ :
          (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u} R))).mapDerivedCategory.obj M) =
          (ringedConstantTowerPullback F).hom.app (RG.obj M) ≫
            (Functor.const ℕᵒᵖ : (ringedSiteModules.{u} R) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{u}
              R))).mapDerivedCategory.map (d.counit.app M)) := by
  sorry

end CategoryTheory
