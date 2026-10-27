module

public import Sheaf.Paper.QcqsOpenClosedTree
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.FiniteConstantModelResolution
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Sheaf.CategoryTheory.SheafPullbackForgetComparison
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Supported integral models and their actual finite quotient restriction towers

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), closed-fibre
comparison (blueprint: def-sfb-supported-integral-model-tower-data).

Positive level n+1 is indexed by n : ℕ. Quotients are cokernels in the ordinary module
category, and all tower transitions are the actual quotient transitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u w v
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.SupportedIntegral

/-- Use the standard localization of strict towers, without changing the underlying category.
Source: blueprint integral closed-fibre comparison, strict complexes
(blueprint: def-sfb-supported-integral-model-tower-data). -/
instance towerDerived (C : Type w) [Category.{v} C] [Abelian C] :
    HasDerivedCategory (ℕᵒᵖ ⥤ C) := HasDerivedCategory.standard _

/-- Inverse limit is additive since it preserves finite products.
Source: blueprint integral closed-fibre comparison, ordinary inverse limit
(blueprint: def-sfb-supported-integral-model-tower-data). -/
instance limitAdditive (C : Type w) [Category.{v} C] [Abelian C] [HasLimitsOfShape ℕᵒᵖ C] :
    (lim : (ℕᵒᵖ ⥤ C) ⥤ C).Additive :=
  Functor.additive_of_preserves_binary_products _

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The original ordinary internal module category, without completion.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
abbrev Modules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousCoefficientRingObj R) X)

/-- Constant scalar multiplication on the continuous coefficient sheaf.
Source: blueprint integral closed-fibre comparison, pi-power quotients
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def pointScalarMap (a : R) :
    Profinite.continuousCoefficientRingObj R ⟶ Profinite.continuousCoefficientRingObj R :=
  ⟨{ app := fun S ↦ AddCommGrpCat.ofHom
       { toFun := fun f ↦ ULift.up (ContinuousMap.const S.unop a * f.down)
         map_zero' := by apply ULift.ext; exact mul_zero _
         map_add' := by intro f g; apply ULift.ext; exact mul_add _ _ _ }
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The linear scalar endomorphism of the regular coefficient module.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def pointScalar (a : R) : End (Mod.regular (Profinite.continuousCoefficientRingObj R)) := by
  refine Mod.homMk (pointScalarMap R a) ?_
  change MonObj.mul ≫ pointScalarMap R a =
    Profinite.continuousCoefficientRingObj R ◁ pointScalarMap R a ≫ MonObj.mul
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp]
  rw [← Category.assoc, Sheaf.μ_comp_map_mul]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc, Sheaf.μ_comp_map_mul]
  apply NatTrans.ext
  funext S
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply TensorProduct.ext'
  intro f g
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  exact mul_left_comm a (f.down x) (g.down x)

/-- The actual point inverse image on coefficient modules.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
abbrev pointPull (X : Scheme.{u}) :=
  (upperStarFromPoint X).mapMod (Profinite.continuousCoefficientRingObj R)

/-- Monoidal inverse image identifies the regular modules by the identity.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def regularIso (X : Scheme.{u}) :
    (pointPull R X).obj (Mod.regular (Profinite.continuousCoefficientRingObj R)) ≅
      Mod.regular (condensedRingObj (Profinite.continuousCoefficientRingObj R) X) :=
  Iso.refl _

/-- Scalar multiplication on every module, transported from the actual point scalar.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def scalar (X : Scheme.{u}) (a : R) : End (𝟭 (Modules R X)) :=
  let dX : End (Mod.regular
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X)) :=
    (regularIso R X).inv ≫ (pointPull R X).map (pointScalar R a) ≫ (regularIso R X).hom
  (leftUnitorNatIso (Modules R X)).inv ≫
    (tensoringLeft (Modules R X)).map dX ≫ (leftUnitorNatIso (Modules R X)).hom

/-- The ordinary quotient functor M ↦ M/pi^(n+1)M, as a genuine cokernel.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def quotient (X : Scheme.{u}) (π : R) (n : ℕ) : Modules R X ⥤ Modules R X :=
  cokernel (scalar R X π ^ (n + 1))

/-- The actual quotient transition induced by the identity on the original module.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def quotientStep (X : Scheme.{u}) (π : R) (n : ℕ) :
    quotient R X π (n + 1) ⟶ quotient R X π n :=
  cokernel.desc _ (cokernel.π (scalar R X π ^ (n + 1))) (by
    rw [pow_succ]
    change (scalar R X π ≫ (scalar R X π ^ (n + 1))) ≫ _ = 0
    rw [Category.assoc, cokernel.condition, comp_zero])

/-- The strict quotient tower, natural in every actual module map.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def quotientTower (X : Scheme.{u}) (π : R) : Modules R X ⥤ (ℕᵒᵖ ⥤ Modules R X) :=
  (Functor.ofOpSequence (quotientStep R X π)).flip

/-- The quotient augmentation, retaining every actual projection.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def quotientUnit (X : Scheme.{u}) (π : R) (M : Modules R X) :
    (Functor.const ℕᵒᵖ).obj M ⟶ (quotientTower R X π).obj M :=
  NatTrans.ofOpSequence (fun n ↦ (cokernel.π (scalar R X π ^ (n + 1))).app M)
    (fun n ↦ by
      simp only [Functor.const_obj_map, quotientTower, Functor.flip_obj_map,
        Functor.ofOpSequence_map_homOfLE_succ]
      change (cokernel.π (scalar R X π ^ (n + 1))).app M =
        (cokernel.π (scalar R X π ^ (n + 1 + 1))).app M ≫
          (quotientStep R X π n).app M
      exact (congr_app (cokernel.π_desc (scalar R X π ^ (n + 1 + 1))
        (cokernel.π (scalar R X π ^ (n + 1))) _) M).symm)

/-- Finite local models form the full category, retaining all actual module maps.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
abbrev Models (X : Scheme.{u}) :=
  (show ObjectProperty (Modules R X) from
    HasFiniteConstantLocalModel (Profinite.continuousCoefficientRingObj R) X).FullSubcategory

/-- Constant scalar coordinates on the original underlying abelian sheaf. The scalar
normalization prevents an arbitrary action or coefficient twist.
Source: blueprint integral closed-fibre comparison, scalar forgetting
(blueprint: def-sfb-supported-integral-model-tower-data). -/
structure Coordinates (X : Scheme.{u}) where
  functor : Modules R X ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} R))
  underlying : functor ⋙ sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) Ab.{u + 1}) ≅
      Mod.forget (condensedRingObj (Profinite.continuousCoefficientRingObj R) X)
  normalization : ∀ (M : Modules R X) (a : R) (V : X.ProEtᵒᵖ),
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) Ab.{u + 1}).map
      ((functor.map ((scalar R X a).app M)).hom.app V) =
      ((functor.obj M).obj.obj V).smul (ULift.up a)
  [additive : functor.Additive]
  [finiteLimits : PreservesFiniteLimits functor]
  [finiteColimits : PreservesFiniteColimits functor]

attribute [instance] Coordinates.additive Coordinates.finiteLimits Coordinates.finiteColimits

/-- Actual etale module sections, evaluated at the terminal object and then forgotten.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
abbrev etaleSections (X : Scheme.{u}) :=
  (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} R))).obj
    (op (Scheme.Etale.mk (𝟙 X))) ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) Ab.{u + 1}

/-- Actual pro-etale module sections in the same fixed scalar coordinates.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
abbrev proetaleSections (X : Scheme.{u}) :=
  (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} R))).obj
    (op (Scheme.ProEt.mk (𝟙 X))) ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) Ab.{u + 1}

/-- Sections and scalar forgetting are additive on the etale site.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
instance etaleSectionsAdditive (X : Scheme.{u}) : (etaleSections R X).Additive where
  map_add := by intro M N f g; rfl

/-- Sections and scalar forgetting are additive on the pro-etale site.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
instance proetaleSectionsAdditive (X : Scheme.{u}) : (proetaleSections R X).Additive where
  map_add := by intro M N f g; rfl

/-- Functorial packaging of a natural transformation as actual arrows.
Source: blueprint integral closed-fibre comparison, arrow formulation
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def arrows {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ⟶ G) : C ⥤ Arrow D where
  obj M := Arrow.mk (α.app M)
  map f := Arrow.homMk (F.map f) (G.map f) (α.naturality f)

/-- The actual ordinary restriction on internal module sections, from its adjunction unit.
Source: blueprint integral closed-fibre comparison, actual horizontal arrow
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def sectionsRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    condensedModuleSections (Profinite.continuousCoefficientRingObj R) Y ⟶
      CondensedRing.upperStar (Profinite.continuousCoefficientRingObj R) f ⋙
        condensedModuleSections (Profinite.continuousCoefficientRingObj R) X :=
  Functor.whiskerRight
      (CondensedRing.upperStarLowerStarAdjunction
        (Profinite.continuousCoefficientRingObj R) f).unit
      (condensedModuleSections (Profinite.continuousCoefficientRingObj R) Y) ≫
    Functor.whiskerLeft (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj R) f)
      (Functor.whiskerLeft
        (Mod.forget (condensedRingObj (Profinite.continuousCoefficientRingObj R) X))
        ((sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).map
          (MorphismProperty.Over.homMk
            (pullback.lift f (𝟙 X)
              ((Category.comp_id f).trans (Category.id_comp f).symm))
            (pullback.lift_snd _ _ _)).op))

/-- The derived horizontal arrow is the universal derived restriction.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def derivedRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.rightDerivedPullback
    (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj R) f)
    (sectionsRestriction R f)

/-- Ordinary scalar coordinates preserve actual global sections, using the underlying iso.
Source: blueprint integral closed-fibre comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def Coordinates.sectionsIso {X : Scheme.{u}} (c : Coordinates R X) :
    c.functor ⋙ proetaleSections R X ≅
      condensedModuleSections (Profinite.continuousCoefficientRingObj R) X :=
  Functor.isoWhiskerRight c.underlying
    ((sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).obj
      (op (Scheme.ProEt.mk (𝟙 X))))

section General
universe a av b bv
variable {C : Type a} [Category.{av} C] [Abelian C]
  [HasDerivedCategory C] [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
  [Abelian.HasKInjectiveResolutions C]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
  {B : Type b} [Category.{bv} B] [Abelian B]
  [HasDerivedCategory B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]

/-- Postcomposition retains the strict tower, rather than a diagram of derived objects.
Source: blueprint integral closed-fibre comparison, total derived inverse limit
(blueprint: def-sfb-supported-integral-model-tower-data). -/
abbrev towerMap (F : C ⥤ B) := (Functor.whiskeringRight ℕᵒᵖ C B).obj F

variable [HasLimitsOfShape ℕᵒᵖ B]
  [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]

/-- The normalized map to total derived inverse limit obtained from the actual augmentation.
It uses the derived constant/limit adjunction and the universal derived sections map.
Source: blueprint integral closed-fibre comparison, strict augmentation
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def augmentedSections (Γ : C ⥤ B) [Γ.Additive] (M : C) (N : ℕᵒᵖ ⥤ C)
    (q : (Functor.const ℕᵒᵖ).obj M ⟶ N) :
    Γ.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M) ⟶
      (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.obj
        ((towerMap Γ).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ C) 0).obj N)) :=
  let K := (DerivedCategory.singleFunctor C 0).obj M
  let cB : B ⥤ (ℕᵒᵖ ⥤ B) := Functor.const ℕᵒᵖ
  let cC : C ⥤ (ℕᵒᵖ ⥤ C) := Functor.const ℕᵒᵖ
  let L := (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor
  (constLimAdj.mapDerivedCategoryRightDerivedAdjunction.unit.app
      (Γ.rightDerivedFunctor.obj K)) ≫
    L.map ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso Γ cB).inv.app K) ≫
    L.map ((Functor.rightDerivedPullback cC (Functor.compConstIso ℕᵒᵖ Γ).hom).app K) ≫
    L.map ((towerMap Γ).rightDerivedFunctor.map
      ((cC.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ C) 0).map q))

end General

/-- The ordinary etale restriction evaluated on the identity object of the small site.
Source: blueprint integral closed-fibre comparison, actual finite horizontal arrow
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def etaleRestriction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleSections R Y ⟶ Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) f ⋙
      etaleSections R X :=
  let A := ModuleCat.{u + 1} (ULift.{u + 1} R)
  Functor.whiskerRight (Etale.upperStarLowerStarAdjunction A f).unit
      (etaleSections R Y) ≫
    Functor.whiskerLeft (Etale.upperStar A f)
      (Functor.whiskerRight
        ((sheafSections X.smallEtaleTopology A).map
          (MorphismProperty.Over.homMk
            (pullback.lift f (𝟙 X)
              ((Category.comp_id f).trans (Category.id_comp f).symm))
            (pullback.lift_snd _ _ _)).op)
        (forget₂ A Ab.{u + 1}))

/-- The canonical comparison on ordinary sections from the comparison adjunction unit.
Source: blueprint integral closed-fibre comparison, finite-level comparison
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def comparisonSections (X : Scheme.{u}) :
    etaleSections R X ⟶ comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} R)) X ⋙ proetaleSections R X :=
  Functor.whiskerRight
    (comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} R)) X).unit
    (etaleSections R X)

section TowerComparison
universe a av b bv
variable {C : Type a} [Category.{av} C] [Abelian C]
  [HasDerivedCategory C] [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
  [Abelian.HasKInjectiveResolutions C]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ C)]
  {B : Type b} [Category.{bv} B] [Abelian B]
  [HasDerivedCategory B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions B]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]

variable [HasDerivedCategory (ℕᵒᵖ ⥤ Ab.{u + 1})]

/-- Universal derived restriction on strict towers, before any scheme specialization.
Source: blueprint integral closed-fibre comparison, actual tower restriction
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def derivedTowerRestriction (P : C ⥤ B) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Γ : C ⥤ Ab.{u + 1}) (Γ' : B ⥤ Ab.{u + 1}) [Γ.Additive] [Γ'.Additive]
    (α : Γ ⟶ P ⋙ Γ') :
    (towerMap Γ).rightDerivedFunctor ⟶
      (towerMap P).mapDerivedCategory ⋙ (towerMap Γ').rightDerivedFunctor :=
  Functor.rightDerivedPullback (towerMap P)
    (F := towerMap Γ) (F' := towerMap Γ')
    ((Functor.whiskeringRight ℕᵒᵖ C Ab.{u + 1}).map α ≫
      (Functor.whiskeringRightObjCompIso P Γ').inv)

/-- Derive the actual comparison of sections on strict towers, with its ordinary unit.
Source: blueprint integral closed-fibre comparison, strict comparison normalization
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def towerComparison (P : C ⥤ B) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Γ : C ⥤ Ab.{u + 1}) (Γ' : B ⥤ Ab.{u + 1}) [Γ.Additive] [Γ'.Additive]
    (α : Γ ⟶ P ⋙ Γ') (N : ℕᵒᵖ ⥤ C) :
    (towerMap Γ).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ C) 0).obj N) ⟶
      (towerMap Γ').rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj ((towerMap P).obj N)) :=
  (derivedTowerRestriction P Γ Γ' α).app
        ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ C) 0).obj N) ≫
    (towerMap Γ').rightDerivedFunctor.map
      (((towerMap P).mapDerivedCategorySingleFunctor 0).hom.app N)

/-- Total derived inverse limit of the normalized strict-tower comparison.
Source: blueprint integral closed-fibre comparison, vertical arrows
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def totalTowerComparison
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ Ab.{u + 1})]
    (P : C ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Γ : C ⥤ Ab.{u + 1}) (Γ' : B ⥤ Ab.{u + 1}) [Γ.Additive] [Γ'.Additive]
    (α : Γ ⟶ P ⋙ Γ') (N : ℕᵒᵖ ⥤ C) :=
  (lim : (ℕᵒᵖ ⥤ Ab.{u + 1}) ⥤ Ab.{u + 1}).rightDerivedFunctor.map
    (towerComparison P Γ Γ' α N)

/-- Apply total sections to an actual morphism of strict towers.
Source: blueprint integral closed-fibre comparison, marked quotient maps
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def totalTowerMap [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ Ab.{u + 1})]
    (Γ : C ⥤ Ab.{u + 1}) [Γ.Additive] {N N' : ℕᵒᵖ ⥤ C} (f : N ⟶ N') :=
  (lim : (ℕᵒᵖ ⥤ Ab.{u + 1}) ⥤ Ab.{u + 1}).rightDerivedFunctor.map
    ((towerMap Γ).rightDerivedFunctor.map
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ C) 0).map f))

/-- Total sections of the ordinary degree-zero normalization for exact inverse image.
Source: blueprint integral closed-fibre comparison, target endpoint
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def totalTowerSinglePullback [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ Ab.{u + 1})]
    (P : C ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Γ : B ⥤ Ab.{u + 1}) [Γ.Additive] (N : ℕᵒᵖ ⥤ C) :=
  (lim : (ℕᵒᵖ ⥤ Ab.{u + 1}) ⥤ Ab.{u + 1}).rightDerivedFunctor.map
    ((towerMap Γ).rightDerivedFunctor.map
      (((towerMap P).mapDerivedCategorySingleFunctor 0).hom.app N))

/-- Ordinary degree-zero normalization after derived sections of exact inverse image.
Source: blueprint integral closed-fibre comparison, integral target endpoint
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def sectionsSinglePullback (P : C ⥤ B) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (Γ : B ⥤ Ab.{u + 1}) [Γ.Additive] (M : C) :=
  Γ.rightDerivedFunctor.map ((P.mapDerivedCategorySingleFunctor 0).hom.app M)

/-- Canonical endpoint normalization as an equality of maps to the entire strict derived limit.
The left marking is part of the data, and r permits the canonical degree-zero pullback map.
Source: blueprint integral closed-fibre comparison, quotient normalization
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def EndpointNormalized
    {A : Type w} [Category.{v} A] [Abelian A]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ Ab.{u + 1})]
    (P : C ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (V : A ⥤ B) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (Γ : C ⥤ Ab.{u + 1}) (ΓA : A ⥤ Ab.{u + 1}) (ΓB : B ⥤ Ab.{u + 1})
    [Γ.Additive] [ΓA.Additive] [ΓB.Additive]
    (α : ΓA ⟶ V ⋙ ΓB) (β : Γ ⟶ P ⋙ ΓB)
    (M : C) (N : ℕᵒᵖ ⥤ C) (q : (Functor.const ℕᵒᵖ).obj M ⟶ N)
    (F : ℕᵒᵖ ⥤ A) (m : (towerMap V).obj F ⟶ (towerMap P).obj N)
    (K : DerivedCategory Ab.{u + 1})
    (r : K ⟶ Γ.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M))
    (e : K ⟶ (lim : (ℕᵒᵖ ⥤ Ab.{u + 1}) ⥤ Ab.{u + 1}).rightDerivedFunctor.obj
      ((towerMap ΓA).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj F))) : Prop :=
  e ≫ totalTowerComparison V ΓA ΓB α F ≫ totalTowerMap ΓB m =
    r ≫ augmentedSections Γ M N q ≫ totalTowerComparison P Γ ΓB β N

universe w0 v0 w1 v1

/-- Endpoint normalization after exact inverse image, retaining its ordinary single comparison.
Source: blueprint integral closed-fibre comparison, pulled-back quotient augmentation
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def PulledEndpointNormalized
    {C0 : Type w0} [Category.{v0} C0] [Abelian C0] [HasDerivedCategory C0]
    {A0 : Type w1} [Category.{v1} A0] [Abelian A0]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A0)]
    {A : Type w} [Category.{v} A] [Abelian A]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ Ab.{u + 1})]
    (Q : C0 ⥤ C) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (Q' : A0 ⥤ A) [Q'.Additive] [PreservesFiniteLimits Q'] [PreservesFiniteColimits Q']
    (P : C ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (V : A ⥤ B) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (Γ : C ⥤ Ab.{u + 1}) (ΓA : A ⥤ Ab.{u + 1}) (ΓB : B ⥤ Ab.{u + 1})
    [Γ.Additive] [ΓA.Additive] [ΓB.Additive]
    (α : ΓA ⟶ V ⋙ ΓB) (β : Γ ⟶ P ⋙ ΓB)
    (M : C0) (N : ℕᵒᵖ ⥤ C0) (q : (Functor.const ℕᵒᵖ).obj M ⟶ N)
    (F : ℕᵒᵖ ⥤ A0)
    (m : (towerMap V).obj ((towerMap Q').obj F) ⟶
      (towerMap P).obj ((towerMap Q).obj N))
    (e : Γ.rightDerivedFunctor.obj
        (Q.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C0 0).obj M)) ⟶
      (lim : (ℕᵒᵖ ⥤ Ab.{u + 1}) ⥤ Ab.{u + 1}).rightDerivedFunctor.obj
        ((towerMap ΓA).rightDerivedFunctor.obj
          ((towerMap Q').mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A0) 0).obj F)))) : Prop :=
  EndpointNormalized P V Γ ΓA ΓB α β (Q.obj M) ((towerMap Q).obj N)
    ((Functor.compConstIso ℕᵒᵖ Q).hom.app M ≫ (towerMap Q).map q)
    ((towerMap Q').obj F) m _
    (sectionsSinglePullback Q Γ M)
    (e ≫ totalTowerSinglePullback Q' ΓA F)

end TowerComparison

/-- Resolution existence is recorded as proof data in the conclusion, never an added
hypothesis on the schemes or coefficients.
Source: blueprint integral closed-fibre comparison, small Grothendieck module categories
(blueprint: def-sfb-supported-integral-model-tower-data). -/
class Resolutions (X : Scheme.{u}) : Prop where
  [internal : Abelian.HasKInjectiveResolutions (Modules R X)]
  [fixedPro : Abelian.HasKInjectiveResolutions
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} R)))]
  [fixedEt : Abelian.HasKInjectiveResolutions
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} R)))]
  [internalTower : Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ Modules R X)]
  [fixedProTower : Abelian.HasKInjectiveResolutions
    (ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} R)))]
  [fixedEtTower : Abelian.HasKInjectiveResolutions
    (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} R)))]
  [abelianTower : Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ Ab.{u + 1})]

attribute [instance] Resolutions.internal Resolutions.fixedPro Resolutions.fixedEt
  Resolutions.internalTower Resolutions.fixedProTower
  Resolutions.fixedEtTower

/-- Scalar-coordinate pullback is fixed by the actual direct-image map and adjunction mate.
Source: blueprint integral closed-fibre comparison, inverse-image square
(blueprint: def-sfb-supported-integral-model-tower-data). -/
structure PullbackCoordinates {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : Coordinates R X) (cY : Coordinates R Y) where
  lower : CondensedRing.lowerStar (Profinite.continuousCoefficientRingObj R) f ⋙
    cY.functor ≅ cX.functor ⋙ lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) f
  lower_normalization :
    Functor.whiskerRight lower.hom
        (sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} R)) Ab.{u + 1})) ≫
      Functor.whiskerRight cX.underlying.hom (lowerStar Ab.{u + 1} f) =
    Functor.whiskerLeft (CondensedRing.lowerStar
      (Profinite.continuousCoefficientRingObj R) f) cY.underlying.hom
  upper : cY.functor ⋙ upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) f ≅
    CondensedRing.upperStar (Profinite.continuousCoefficientRingObj R) f ⋙ cX.functor
  mate : (mateEquiv
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.continuousCoefficientRingObj R) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} R)) f)
    (.mk _ _ _ _ upper.hom)).natTrans = lower.hom

/-- The chain functor on every finite model and every actual morphism.
Source: blueprint integral closed-fibre comparison, J
(blueprint: def-sfb-supported-integral-model-tower-data). -/
abbrev supportedModels {T S : Scheme.{u}} {tree : QcqsOpenClosedTree T}
    (p : tree.Path S) : Models R S ⥤ Modules R T :=
  (show ObjectProperty (Modules R S) from
    HasFiniteConstantLocalModel (Profinite.continuousCoefficientRingObj R) S).ι ⋙
      p.extension (Profinite.continuousCoefficientRingObj R)

/-- First take ordinary quotients, then apply the actual support functor to the strict tower.
Source: blueprint integral closed-fibre comparison, J L_n
(blueprint: def-sfb-supported-integral-model-tower-data). -/
abbrev supportedQuotients {T S : Scheme.{u}} {tree : QcqsOpenClosedTree T}
    (p : tree.Path S) (π : R) : Models R S ⥤ (ℕᵒᵖ ⥤ Modules R T) :=
  (show ObjectProperty (Modules R S) from
    HasFiniteConstantLocalModel (Profinite.continuousCoefficientRingObj R) S).ι ⋙
      quotientTower R S π ⋙ towerMap (p.extension (Profinite.continuousCoefficientRingObj R))

/-- The actual quotient augmentation after support extension.
Source: blueprint integral closed-fibre comparison, quotient projections
(blueprint: def-sfb-supported-integral-model-tower-data). -/
def supportedUnit {T S : Scheme.{u}} {tree : QcqsOpenClosedTree T}
    (p : tree.Path S) (π : R) (M : Models R S) :
    (Functor.const ℕᵒᵖ).obj ((supportedModels R p).obj M) ⟶
      (supportedQuotients R p π).obj M :=
  (Functor.compConstIso ℕᵒᵖ
      (p.extension (Profinite.continuousCoefficientRingObj R))).hom.app M.obj ≫
    (towerMap (p.extension (Profinite.continuousCoefficientRingObj R))).map
      (quotientUnit R S π M.obj)

/-- Descent of the entire quotient functor with its actual scalar action and transitions.
The uniqueness statement is relative to the displayed identification, so no automorphisms
of an unmarked descent are asserted to vanish.
Source: blueprint integral closed-fibre comparison, finite descent and uniqueness
(blueprint: def-sfb-supported-integral-model-tower-data). -/
structure Descent {T S : Scheme.{u}} {tree : QcqsOpenClosedTree T}
    (p : tree.Path S) (π : R) (ℓ : ℕ) (c : Coordinates R T) where
  functor : Models R S ⥤ (ℕᵒᵖ ⥤ Sheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} R)))
  identification : functor ⋙ towerMap
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) T) ≅
    supportedQuotients R p π ⋙ towerMap c.functor
  quotientAction : ∀ (M : Models R S) (n : ℕ) (V : T.Etaleᵒᵖ),
    (((functor.obj M).obj (op n)).obj.obj V).smul (ULift.up (π ^ (n + 1))) = 0
  ellPower : ∀ (M : Models R S) (n : ℕ), ∃ k : ℕ, ∀ (V : T.Etaleᵒᵖ)
    (x : ((functor.obj M).obj (op n)).obj.obj V), (ℓ ^ k) • x = 0
  unique : ∀ (G : Models R S ⥤ (ℕᵒᵖ ⥤ Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} R))))
    (e : G ⋙ towerMap
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) T) ≅
      supportedQuotients R p π ⋙ towerMap c.functor),
    ∃! i : G ≅ functor,
      Functor.whiskerRight i.hom
          (towerMap (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) T)) ≫
        identification.hom = e.hom

end AlgebraicGeometry.ProEtale.SupportedIntegral
