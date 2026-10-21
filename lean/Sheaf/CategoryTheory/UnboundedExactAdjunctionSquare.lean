/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.Abelian
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-!
# Exact unbounded adjunctions, strict towers, and square mates

Source: Stacks Project, Derived Categories, Tags 0DVC, 0FND, 08BJ and 070I;
Cohomology on Sites, Tag 07A7; the constant/evaluation application is agent supplied
(blueprint: lem-sbc-unbounded-exact-adjunction-square).

The index `op n` denotes positive level `n + 1`. All comparisons below are constructed
from the specified ordinary adjunction and exact-localization comparisons. In particular,
no arbitrary natural isomorphism or faithful derived evaluation is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u vA uA vB uB wA wB wTA wTB wA' wB' wTA' wTB'

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.UnboundedExactTower

/-- The data already specified by a coefficient-preserving ringed-site morphism:
its induced module inverse image, exactness, and its adjunction to the supplied
module direct image. The isomorphism is required on the actual structural map.
Source: Stacks 08BJ and 07A7
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
structure ExactMorphism
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J RingCat.{u}) (S : Sheaf K RingCat.{u}) where
  ringed : RingedToposMorphism R S
  coefficientIso : IsIso ringed.ringMap
  inverse : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} R
  [additive : inverse.Additive]
  [finiteLimits : PreservesFiniteLimits inverse]
  [finiteColimits : PreservesFiniteColimits inverse]
  adjunction : inverse ⊣ ringed.modules

attribute [instance] ExactMorphism.additive ExactMorphism.finiteLimits
  ExactMorphism.finiteColimits

/-- The existing Grothendieck-category K-injective resolution construction for module
sheaves. Source: Stacks 079P, 07A5
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
instance moduleResolutions
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} R) :=
  letI := SheafOfModules.isGrothendieckAbelian R
  inferInstance

/-- The same existing resolution construction for strict towers, which are module
sheaves on the small diagram site. Source: Stacks 079P, 07A5 and the diagram-site
realization (blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
instance towerResolutions
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) :=
  letI := smallModuleDiagrams_isGrothendieckAbelian J R (AsSmall.{u} ℕᵒᵖ)
  letI : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) :=
    IsGrothendieckAbelian.of_equivalence
      (Equivalence.congrLeft (AsSmall.equiv : ℕᵒᵖ ≌ AsSmall.{u} ℕᵒᵖ)).symm
  inferInstance

section Comparisons

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The descended constant/inverse-image identity, using the ordinary identity-component
comparison `compConstIso`. Source: Stacks 015F, 0DVC
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def constantInterchange :
    (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory ⋙
        ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (Functor.const ℕᵒᵖ)
    ((Functor.whiskeringRight ℕᵒᵖ B A).obj F)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F).symm ≪≫
    Functor.mapDerivedCategoryCompIso F (Functor.const ℕᵒᵖ)

variable {F} {G : A ⥤ B} [G.Additive]
  [Abelian.HasKInjectiveResolutions A]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]

/-- The constant comparison is the mate of the canonical descended inverse-image
comparison. Its invertibility and representative normalization are conclusions below.
Source: Stacks 07A7, 0DVC
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def constantComparison (a : F ⊣ G) :
    G.rightDerivedFunctor ⋙ (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory ⟶
      (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory ⋙
        ((Functor.whiskeringRight ℕᵒᵖ A B).obj G).rightDerivedFunctor :=
  (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
    (a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (constantInterchange F).hom)).natTrans

/-- The evaluation comparison is the mate of the inverse of the canonical descended
termwise/evaluation identity. Source: Stacks 07A7, 0DVC
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def evaluationComparison (a : F ⊣ G) (n : ℕᵒᵖ) :
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj G).rightDerivedFunctor ⋙
        ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory ⟶
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory ⋙ G.rightDerivedFunctor :=
  (mateEquiv (a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
    a.mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (towerDerivedEvaluationInterchange F n).inv)).natTrans

/-- The canonical cochain-level unit of the existing total right derived functor.
It is obtained from its homotopy-level unit using the quotient factorization isomorphisms.
Source: Stacks 070K (blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def cochainUnit (G : A ⥤ B) [G.Additive] (I : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj I) ⟶
      G.rightDerivedFunctor.obj (DerivedCategory.Q.obj I) :=
  (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
    DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (.up ℤ)).inv.app I) ≫
    G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj I) ≫
    G.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).hom.app I)

/-- The representative normalization and all-adjunct compatibility of the two specified
mates. All functors and adjunctions here are the existing localization constructions.
Source: Stacks 070I, 0DVC, 0FND and 07A7
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def ComparisonsCompatible (a : F ⊣ G) : Prop :=
  IsIso (constantComparison a) ∧
  (∀ n : ℕᵒᵖ, IsIso (evaluationComparison a n)) ∧
  (∀ I : CochainComplex A ℤ, I.IsKInjective →
    (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategoryFactors.inv.app
          ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map (cochainUnit G I) ≫
        (constantComparison a).app (DerivedCategory.Q.obj I) ≫
        ((Functor.whiskeringRight ℕᵒᵖ A B).obj G).rightDerivedFunctor.map
          ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategoryFactors.hom.app I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (Functor.compConstIso ℕᵒᵖ G).hom (.up ℤ)).app I) ≫
        cochainUnit ((Functor.whiskeringRight ℕᵒᵖ A B).obj G)
          (((Functor.const ℕᵒᵖ : A ⥤ _).mapHomologicalComplex (.up ℤ)).obj I)) ∧
  (∀ (n : ℕᵒᵖ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ), I.IsKInjective →
    ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.inv.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj G).mapHomologicalComplex (.up ℤ)).obj I) ≫
        ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map
          (cochainUnit ((Functor.whiskeringRight ℕᵒᵖ A B).obj G) I) ≫
        (evaluationComparison a n).app (DerivedCategory.Q.obj I) ≫
        G.rightDerivedFunctor.map
          (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app I) =
      cochainUnit G ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).obj I)) ∧
  (∀ (M : DerivedCategory B) (N : DerivedCategory A)
      (t : F.mapDerivedCategory.obj M ⟶ N),
    (a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
        ((constantInterchange F).hom.app M ≫
          (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.map t) =
      (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map
          (a.mapDerivedCategoryRightDerivedAdjunction.homEquiv M N t) ≫
        (constantComparison a).app N) ∧
  (∀ (n : ℕᵒᵖ) (M : DerivedCategory (ℕᵒᵖ ⥤ B))
      (N : DerivedCategory (ℕᵒᵖ ⥤ A))
      (t : ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory.obj M ⟶ N),
    a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
        ((towerDerivedEvaluationInterchange F n).inv.app M ≫
          ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.map t) =
      ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map
          ((a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction.homEquiv M N t) ≫
        (evaluationComparison a n).app N) ∧
  (∀ M : DerivedCategory B,
    (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.map
        (a.mapDerivedCategoryRightDerivedAdjunction.unit.app M) ≫
      (constantComparison a).app (F.mapDerivedCategory.obj M) =
    (a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction.unit.app
        ((Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory.obj M) ≫
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj G).rightDerivedFunctor.map
        ((constantInterchange F).hom.app M)) ∧
  (∀ N : DerivedCategory A,
    (constantInterchange F).hom.app (G.rightDerivedFunctor.obj N) ≫
      (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.map
        (a.mapDerivedCategoryRightDerivedAdjunction.counit.app N) =
    ((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory.map
        ((constantComparison a).app N) ≫
      (a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction.counit.app
        ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj N)) ∧
  (∀ (n : ℕᵒᵖ) (M : DerivedCategory (ℕᵒᵖ ⥤ B)),
    ((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.map
        ((a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction.unit.app M) ≫
      (evaluationComparison a n).app
        (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategory.obj M) =
    a.mapDerivedCategoryRightDerivedAdjunction.unit.app
        (((evaluation ℕᵒᵖ B).obj n).mapDerivedCategory.obj M) ≫
      G.rightDerivedFunctor.map ((towerDerivedEvaluationInterchange F n).inv.app M)) ∧
  (∀ (n : ℕᵒᵖ) (N : DerivedCategory (ℕᵒᵖ ⥤ A)),
    ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.map
        ((a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction.counit.app N) =
    (towerDerivedEvaluationInterchange F n).hom.app
        (((Functor.whiskeringRight ℕᵒᵖ A B).obj G).rightDerivedFunctor.obj N) ≫
      F.mapDerivedCategory.map ((evaluationComparison a n).app N) ≫
      a.mapDerivedCategoryRightDerivedAdjunction.counit.app
        (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.obj N))

end Comparisons

/-- Exactness and K-injective preservation for constant towers and all evaluations,
with evaluation at positive level one left adjoint to constants.
Source: Stacks 08BJ; terminal-index adjunction and levelwise kernels and cokernels
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def TowerProperties (A : Type uA) [Category.{vA} A] [Abelian A] : Prop :=
  Nonempty ((evaluation ℕᵒᵖ A).obj (op 0) ⊣ Functor.const ℕᵒᵖ) ∧
  PreservesFiniteLimits (Functor.const ℕᵒᵖ : A ⥤ _) ∧
  PreservesFiniteColimits (Functor.const ℕᵒᵖ : A ⥤ _) ∧
  (∀ n : ℕᵒᵖ, PreservesFiniteLimits ((evaluation ℕᵒᵖ A).obj n) ∧
    PreservesFiniteColimits ((evaluation ℕᵒᵖ A).obj n)) ∧
  (∀ I : CochainComplex A ℤ, I.IsKInjective →
    CochainComplex.IsKInjective
      (((Functor.const ℕᵒᵖ : A ⥤ _).mapHomologicalComplex (.up ℤ)).obj I)) ∧
  (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ), I.IsKInjective →
    CochainComplex.IsKInjective
      ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).obj I))

section Square

universe uA' vA' uB' vB'

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wB'} B']
  [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
  [HasDerivedCategory.{wTA'} (ℕᵒᵖ ⥤ A')] [HasDerivedCategory.{wTB'} (ℕᵒᵖ ⥤ B')]
  (F : B ⥤ A) (F' : B' ⥤ A') (g : B ⥤ B') (h : A ⥤ A')
  [F.Additive] [F'.Additive] [g.Additive] [h.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]
  [PreservesFiniteLimits h] [PreservesFiniteColimits h]

/-- Localize the given inverse-image composition comparison with the specified
composition isomorphisms. Source: Stacks 015F and 07A7
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def localizedSquare (θ : g ⋙ F' ≅ F ⋙ h) :
    g.mapDerivedCategory ⋙ F'.mapDerivedCategory ≅
      F.mapDerivedCategory ⋙ h.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso g F').symm ≪≫
    Functor.mapDerivedCategoryNatIso θ ≪≫ Functor.mapDerivedCategoryCompIso F h

/-- The termwise inverse-image comparison, with component θ at each level.
Source: Stacks 07A7, termwise diagram application
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def towerSquare (θ : g ⋙ F' ≅ F ⋙ h) :
    (Functor.whiskeringRight ℕᵒᵖ B B').obj g ⋙
        (Functor.whiskeringRight ℕᵒᵖ B' A').obj F' ≅
      (Functor.whiskeringRight ℕᵒᵖ B A).obj F ⋙
        (Functor.whiskeringRight ℕᵒᵖ A A').obj h :=
  NatIso.ofComponents (fun T => Functor.isoWhiskerLeft T θ) (fun {T U} t => by
    ext n
    exact θ.hom.naturality (t.app n))

variable {F F' g h} {G : A ⥤ B} {G' : A' ⥤ B'} [G.Additive] [G'.Additive]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions A']
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A')]

/-- Equality of the actual ordinary and tower square mates after constants and evaluation.
Neither equality requires the mate to be invertible or derived evaluation to be faithful.
Source: Stacks 07A7 and the explicit counit-transpose calculation
(blueprint: lem-sbc-unbounded-exact-adjunction-square). -/
def SquareCompatible (a : F ⊣ G) (a' : F' ⊣ G') (θ : g ⋙ F' ≅ F ⋙ h) : Prop :=
  (∀ K : DerivedCategory A,
    (constantInterchange g).inv.app (G.rightDerivedFunctor.obj K) ≫
      ((Functor.whiskeringRight ℕᵒᵖ B B').obj g).mapDerivedCategory.map
        ((constantComparison a).app K) ≫
      (mateEquiv (a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
        (a'.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _ (localizedSquare _ _ _ _ (towerSquare F F' g h θ)).hom)).app
          ((Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory.obj K) =
    (Functor.const ℕᵒᵖ : B' ⥤ _).mapDerivedCategory.map
        ((mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
          a'.mapDerivedCategoryRightDerivedAdjunction
          (TwoSquare.mk _ _ _ _ (localizedSquare F F' g h θ).hom)).app K) ≫
      (constantComparison a').app (h.mapDerivedCategory.obj K) ≫
      ((Functor.whiskeringRight ℕᵒᵖ A' B').obj G').rightDerivedFunctor.map
        ((constantInterchange h).inv.app K)) ∧
  (∀ (n : ℕᵒᵖ) (K : DerivedCategory (ℕᵒᵖ ⥤ A)),
    ((evaluation ℕᵒᵖ B').obj n).mapDerivedCategory.map
        ((mateEquiv (a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
          (a'.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
          (TwoSquare.mk _ _ _ _
            (localizedSquare _ _ _ _ (towerSquare F F' g h θ)).hom)).app K) ≫
      (evaluationComparison a' n).app
        (((Functor.whiskeringRight ℕᵒᵖ A A').obj h).mapDerivedCategory.obj K) ≫
      G'.rightDerivedFunctor.map ((towerDerivedEvaluationInterchange h n).hom.app K) =
    (towerDerivedEvaluationInterchange g n).hom.app
        (((Functor.whiskeringRight ℕᵒᵖ A B).obj G).rightDerivedFunctor.obj K) ≫
      g.mapDerivedCategory.map ((evaluationComparison a n).app K) ≫
      (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
        a'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _ (localizedSquare F F' g h θ).hom)).app
          (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.obj K))

end Square

/-- Constants and evaluations preserve K-injectives and the canonical unbounded
adjunction, with the identity comparison on K-injective representatives.
Source: Stacks 08BJ, 070I, 070K, 0DVC, 0FND, 07A5 and 07A7
(blueprint: lem-sbc-unbounded-exact-adjunction-square).

Proof plan (node steps 1-9):
1. A map T → ΔM is determined by its component T₁ → M. The inverse uses the
   transitions Tₙ → T₁. This gives ev₁ ⊣ Δ. Kernels and cokernels are levelwise
   (`lem-weil-tower-category-levelwise-abelian`), so constants and evaluations are exact.
2. The exact-left-adjoint criterion makes Δ preserve K-injectives; the tower evaluation
   theorem gives the evaluation assertion (`lem-weil-pbc-right-adjoint-preserves-kinjective`,
   `lem-weil-tower-evaluation-kinjective`). The ordinary adjunction extends termwise.
3. Realize towers on the small diagram site. Module and tower categories have K-injective
   resolutions (`lem-weil-pbc-diagram-site-realization`, `prop-pur-kinjective-resolutions-exist`).
   Exact functors and their termwise identities descend through localization
   (`lem-weil-pbc-exact-functor-derived-factorization`,
   `lem-weil-pbc-localization-universal-property`, `lem-weil-pbc-kinjective-total-derived`).
4. On a K-injective I both constant-side functors are represented by Δu_*I; use its
   identity. The Hom bijection and invariance under homotopy equivalences prove naturality
   and independence (`lem-weil-pbc-kinjective-hom-derived`).
5. The same construction for a K-injective tower is the identity on u_*Iₙ. Thus both
   displayed mates are invertible with exactly the two universal-unit normalizations.
6. Normalize the canonical adjunction by Hom into K-injectives, using the all-object
   resolving class, the homotopy adjunction and the exactness of inverse image
   (`lem-weil-pbc-termwise-adjunction-homotopy`,
   `lem-sfb-resolving-derived-adjunction-normalization`).
7. Represent every derived t by a chain map into a K-injective I. The constant transpose
   equals the constant of the transpose because the ordinary unit is termwise.
8. Evaluating a tower chain map gives the evaluated transpose for the same reason.
9. Substitute identity morphisms into these two all-adjunct equalities to obtain the
   unit and counit identifications. These are equalities in derived Hom sets. -/
theorem unboundedExactAdjunctionSquare
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J RingCat.{u}) (S : Sheaf K RingCat.{u})
    [HasDerivedCategory.{wA} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{wB} (ringedSiteModules.{u} S)]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R)]
    [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ ringedSiteModules.{u} S)]
    (f : ExactMorphism R S) :
    TowerProperties (ringedSiteModules.{u} R) ∧
      TowerProperties (ringedSiteModules.{u} S) ∧ ComparisonsCompatible f.adjunction := by
  sorry

/-- Constants and evaluations carry the specified ordinary derived square mate to the
specified tower mate, after their canonical comparisons.
Source: Stacks 07A7, remark-base-change; the constant/evaluation application is agent supplied
(blueprint: lem-sbc-unbounded-exact-adjunction-square).

Proof plan (node steps 10-12):
10. Write the square mate as the transpose of θ followed by the first counit, exactly as
    `def-weil-pbc-adjunction-mate`. Localize θ and its termwise tower counterpart using
    the canonical exact composition comparisons.
11. For constants, transpose both sides of the asserted equation under the tower
    adjunction. Naturality of θ and the constant counit identity from steps 7-9 make
    both transposes Δ of the same counit composite. The adjunction Hom bijection is
    injective, so the actual derived tower morphisms are equal.
12. For evaluation, transpose under the ordinary derived adjunction. Naturality of θ
    and the evaluated counit identity from steps 8-9 identify both transposes with the
    evaluation of the same tower counit composite. Injectivity gives the second equality.
    This proves the assertions without faithfulness of evaluation or invertibility of mates. -/
theorem unboundedExactAdjunctionSquare_mates
    {C D C' D' : Type u}
    [SmallCategory C] [SmallCategory D] [SmallCategory C'] [SmallCategory D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {J' : GrothendieckTopology C'} {K' : GrothendieckTopology D'}
    (R : Sheaf J RingCat.{u}) (S : Sheaf K RingCat.{u})
    (R' : Sheaf J' RingCat.{u}) (S' : Sheaf K' RingCat.{u})
    [HasDerivedCategory.{wA} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{wB} (ringedSiteModules.{u} S)]
    [HasDerivedCategory.{wA'} (ringedSiteModules.{u} R')]
    [HasDerivedCategory.{wB'} (ringedSiteModules.{u} S')]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R)]
    [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ ringedSiteModules.{u} S)]
    [HasDerivedCategory.{wTA'} (ℕᵒᵖ ⥤ ringedSiteModules.{u} R')]
    [HasDerivedCategory.{wTB'} (ℕᵒᵖ ⥤ ringedSiteModules.{u} S')]
    (f : ExactMorphism R S) (f' : ExactMorphism R' S')
    (g : ExactMorphism S' S) (h : ExactMorphism R' R)
    (θ : g.inverse ⋙ f'.inverse ≅ f.inverse ⋙ h.inverse) :
    SquareCompatible f.adjunction f'.adjunction θ := by
  sorry

end CategoryTheory.UnboundedExactTower
