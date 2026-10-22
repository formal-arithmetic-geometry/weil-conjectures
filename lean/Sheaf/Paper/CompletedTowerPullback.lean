/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q08 and Q31
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.CompletedTowerDerivedLimitFunctor
public import Sheaf.Paper.IntrinsicCompletion
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Sheaf.Paper.FourCorners
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Sheaf.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Pullback of strict completed-coefficient towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1261;
Stacks Project, Tag 099N (blueprint: def-weil-pbc-completed-pullback).

The structure map into the completed coefficient ring is built from its finite
projections. It is a morphism, with no invertibility assumption. The functor here
precedes derived inverse limit and acts on every strict derived tower.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Functor

/-- Transport a homotopy-level derived counit to its actual complex representatives.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
This is the composite of the existing quotient comparisons with the supplied counit. -/
def leftDerivedCounitOnComplex {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ) :
    LF.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
  LF.map ((DerivedCategory.quotientCompQhIso C).inv.app P) ≫
    ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso D).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj P)

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- Finite coefficient comparison obtained from constant sections, with its fixed
constant-section normalization. Source: blueprint order 1261
(blueprint: def-weil-pbc-completed-pullback). -/
def completedFiniteCoefficientMap (n : ℕ) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        ((pbcAdicRings Y d).obj (op n)) ⟶ (pbcAdicRings X d).obj (op n) :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (pbcLevelConstantComparison Y d n).inv ≫
    proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
      (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))) ≫
    (pbcLevelConstantComparison X d n).hom

/-- Finite constant coefficient inverse image has its canonical isomorphism.
Source: Stacks Tags 09AK and 09AL (blueprint: def-weil-pbc-completed-pullback).
Proof: the constant sheaf inverse image comparison is an isomorphism; the other two
factors are the fixed constant-section coefficient comparisons. Compose these isomorphisms. -/
@[instance]
theorem completedFiniteCoefficientMap_isIso (n : ℕ) :
    IsIso (completedFiniteCoefficientMap g d n) := by
  change IsIso (d.finiteRingIso g n).hom
  infer_instance

/-- The components of the completed coefficient structure map.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedCoefficientComponent (n : ℕ) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d) ⟶
      (pbcAdicRings X d).obj (op n) :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (pbcAdicProjection Y d n) ≫
    completedFiniteCoefficientMap g d n

/-- The coefficient components form a limit cone.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: the completion projections commute with quotient maps. The finite coefficient
comparison is induced by constant sections, so is natural in the quotient homomorphism.
Apply inverse-image functoriality and these two equalities. -/
theorem completedCoefficientComponent_naturality {b a : ℕᵒᵖ} (f : b ⟶ a) :
    completedCoefficientComponent g d b.unop ≫ (pbcAdicRings X d).map f =
      completedCoefficientComponent g d a.unop := by
  exact d.integralRingComponent_naturality g f

/-- The canonical coefficient structure map into the actual completed limit.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedCoefficientMap :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d) ⟶
      pbcAdicCompletion X d :=
  limit.lift (pbcAdicRings X d)
    { pt := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d)
      π := { app n := completedCoefficientComponent g d n.unop
             naturality _ _ f := (Category.id_comp _).trans
               (completedCoefficientComponent_naturality g d f).symm } }

/-- Module inverse image followed by extension along the completed structure map.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedModulePullback :
    pbcModules Y (pbcAdicCompletion Y d) ⥤ pbcModules X (pbcAdicCompletion X d) :=
  proEtaleModuleInverseImage g (pbcAdicCompletion Y d) ⋙
    reductionChange X (completedCoefficientMap g d)

/-- Completed module pullback is additive.
Source: Stacks Tag 03EK (blueprint: def-weil-pbc-completed-pullback).
Proof: inverse image of abelian sheaves respects sums of maps, as does the induced
module inverse image. Sheafified scalar extension respects sums on tensor generators.
The composite therefore respects addition. -/
@[instance]
theorem completedModulePullback_additive : (completedModulePullback g d).Additive := by
  dsimp only [completedModulePullback]
  infer_instance

/-- Apply the module pullback to objects and maps at each strict tower level.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedTowerModulePullback :
    pbcTowers Y (pbcAdicCompletion Y d) ⥤ pbcTowers X (pbcAdicCompletion X d) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (completedModulePullback g d)

/-- Levelwise pullback is additive, with equality checked at every level.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: each component is the additive completed module pullback, and equality of
natural transformations is componentwise. -/
@[instance]
theorem completedTowerModulePullback_additive :
    (completedTowerModulePullback g d).Additive := by
  constructor
  intro M N f h
  apply NatTrans.ext
  funext n
  exact (completedModulePullback g d).map_add

private theorem completedCoefficientMap_eq_integralRingIso :
    completedCoefficientMap g d = (d.integralRingIso g).hom := by
  apply limit.hom_ext
  intro n
  change completedCoefficientMap g d ≫ d.projection X n.unop =
    (d.integralRingIso g).hom ≫ d.projection X n.unop
  calc
    _ = completedCoefficientComponent g d n.unop := limit.lift_π _ n
    _ = _ := by
      rw [d.projection_comm]
      rfl

private theorem completedModulePullback_eq_exact :
    completedModulePullback g d =
      proEtaleRingModulePullback g (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso g) := by
  unfold completedModulePullback
  rw [completedCoefficientMap_eq_integralRingIso]
  refine CategoryTheory.Functor.ext (fun M ↦
    (completedAdicChangeData X (d.integralRingIso g).hom).choose_spec.choose
      ((proEtaleModuleInverseImage g (d.completedRing Y)).obj M)) ?_
  intro M N f
  exact (completedAdicChangeData X (d.integralRingIso g).hom).choose_spec.choose_spec.choose
    ((proEtaleModuleInverseImage g (d.completedRing Y)).map f)

private instance completedModulePullback_finiteLimits :
    PreservesFiniteLimits (completedModulePullback g d) := by
  rw [completedModulePullback_eq_exact]
  infer_instance

private instance completedModulePullback_finiteColimits :
    PreservesFiniteColimits (completedModulePullback g d) := by
  rw [completedModulePullback_eq_exact]
  infer_instance

private instance completedTowerModulePullback_finiteLimits :
    PreservesFiniteLimits (completedTowerModulePullback g d) := by
  dsimp only [completedTowerModulePullback]
  exact ⟨fun _ _ _ ↦ inferInstance⟩

private instance completedTowerModulePullback_finiteColimits :
    PreservesFiniteColimits (completedTowerModulePullback g d) := by
  dsimp only [completedTowerModulePullback]
  exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- The universal left-derived property and K-flat representative computation of the
specified pullback pair. Naming this property keeps later choice terms small.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def IsCompletedTowerPullbackPair
    (LF : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
        DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
        (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh) : Prop :=
  LF.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ)) ∧
      (∃ (_ : LF.CommShift ℤ), LF.IsTriangulated) ∧
      ∀ P : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ,
        (∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
          (R := pbcAdicCompletion Y d)
          (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
            (op n)).mapHomologicalComplex (.up ℤ) |>.obj P)) →
        IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- The universal left derived pair is computed on objectwise K-flat representatives.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: strict diagram K-flat replacements supply a quasi-isomorphism with objectwise
K-flat flat-term source. Pullback preserves quasi-isomorphisms between these by exact
inverse image and K-flat scalar extension. The additive termwise functor preserves
shifts and cones. Apply the resolving-class left-derived theorem; its counit is
invertible on every object of this class. All transitions are pulled back with the
same functor, so the computation remains a strict tower computation. -/
theorem completedTowerPullback_exists :
    ∃ (LF : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
        DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      IsCompletedTowerPullbackPair g d LF ε := by
  let F := completedTowerModulePullback g d
  refine ⟨F.mapDerivedCategory, F.mapDerivedCategoryFactorsh.hom, ?_, ?_, ?_⟩
  · exact Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  · exact ⟨inferInstance, inferInstance⟩
  · intro P _
    infer_instance

/-- Canonical total left derived levelwise pullback, with its universal comparison.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedTowerPullback :
    DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcTowers X (pbcAdicCompletion X d)) :=
  (completedTowerPullback_exists g d).choose

/-- The universal counit of strict tower pullback.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedTowerPullbackCounit :
    DerivedCategory.Qh ⋙ completedTowerPullback g d ⟶
      (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (completedTowerPullback_exists g d).choose_spec.choose

/-- The universal left-derived property and K-flat representative computation of the
specified pullback pair. Naming this property keeps later choice terms small.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def IsCompletedOrdinaryPullbackPair
    (LF : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
        DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
    (ε : DerivedCategory.Qh ⋙ LF ⟶
        (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) : Prop :=
  LF.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)) ∧
      ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients
          (R := pbcAdicCompletion Y d) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))

/-- Ordinary derived pullback has the universal pair computed by the one-object
K-flat resolving class. This is ordinary pullback before completion.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: use exact module inverse image followed by the K-flat scalar extension along c_g.
K-flat flat-term resolutions exist on the small site. Scalar extension preserves
quasi-isomorphisms between K-flat complexes. Apply the resolving-class theorem. -/
theorem completedOrdinaryPullback_exists :
    ∃ (LF : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
        DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
      (ε : DerivedCategory.Qh ⋙ LF ⟶
        (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh),
      IsCompletedOrdinaryPullbackPair g d LF ε := by
  let F := completedModulePullback g d
  refine ⟨F.mapDerivedCategory, F.mapDerivedCategoryFactorsh.hom, ?_, ?_⟩
  · exact Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh
  · intro P _
    infer_instance

/-- Ordinary total left derived completed-coefficient pullback.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedOrdinaryPullback :
    DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcModules X (pbcAdicCompletion X d)) :=
  (completedOrdinaryPullback_exists g d).choose

/-- The fixed ordinary left-derived counit.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedOrdinaryPullbackCounit :
    DerivedCategory.Qh ⋙ completedOrdinaryPullback g d ⟶
      (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (completedOrdinaryPullback_exists g d).choose_spec.choose

attribute [irreducible] completedTowerPullback completedOrdinaryPullback

/-- The strict quotient-unit map is fixed on sections by x ↦ 1 tensor x.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: this formula is linear over the completed coefficient ring, commutes with
restriction, and is natural in the module. Each quotient transition takes 1 tensor x
to 1 tensor x, so the maps form a strict tower map. The sectionwise formula gives uniqueness. -/
theorem completedReductionModuleUnit_exists (T : Scheme.{u}) :
    ∃! τ : completedTowerConstant d T ⟶ completedReductionModuleTowerFunctor T d,
      ∀ (M : pbcModules T (pbcAdicCompletion T d)) (n : ℕ)
        (U : T.ProEtᵒᵖ) (x : M.val.obj U),
        ((τ.app M).app (op n)).val.app U x =
          reductionTensorSection T (pbcAdicProjection T d n) M U 1 x := by
  let u (M : pbcModules T (pbcAdicCompletion T d)) (n : ℕ) :
      M ⟶ (completedReductionLevel T d n).obj M :=
    (pbcScalarAdjunction (pbcAdicProjection T d n)).unit.app M
  have hu (M : pbcModules T (pbcAdicCompletion T d)) (n : ℕ)
      (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
      (u M n).val.app U x =
        reductionTensorSection T (pbcAdicProjection T d n) M U 1 x :=
    (pbcScalarAdjunction_exists (pbcAdicProjection T d n)).exists.choose_spec M U x
  let τ : completedTowerConstant d T ⟶ completedReductionModuleTowerFunctor T d :=
    { app := fun M ↦ NatTrans.ofOpSequence (u M) (by
        intro n
        change u M n = u M (n + 1) ≫
          (completedReductionModuleTower T d M).map
            (homOfLE (n.le_add_right 1)).op
        dsimp only [completedReductionModuleTower]
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        ext U x
        change (u M n).val.app U x =
          ((completedReductionTransition T d (n + 1) n (Nat.le_succ n)).app M).val.app U
            ((u M (n + 1)).val.app U x)
        rw [hu, hu]
        have ht := (completedReductionTransition_exists T d (n + 1) n
          (Nat.le_succ n)).exists.choose_spec M U 1 x
        dsimp only [completedReductionTransition] at *
        simpa only [map_one, pbcAdicProjection, completedReductionProjection,
          pbcAdicRings, reductionCoefficientSystem] using ht.symm)
      naturality := by
        intro M N a
        apply NatTrans.ext
        funext n
        exact (pbcScalarAdjunction (pbcAdicProjection T d n.unop)).unit.naturality a }
  refine ⟨τ, hu, ?_⟩
  intro τ' hτ'
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  ext U x
  exact (hτ' M n.unop U x).trans (hu M n.unop U x).symm

/-- The actual module-to-strict-tower quotient unit.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedReductionModuleUnit (T : Scheme.{u}) :
    completedTowerConstant d T ⟶ completedReductionModuleTowerFunctor T d :=
  (completedReductionModuleUnit_exists d T).exists.choose

/-- The reduction tower's fixed universal counit.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedReductionTowerCounit (T : Scheme.{u}) :
    DerivedCategory.Qh ⋙ completedReductionTower T d ⟶ completedReductionHomotopyFunctor T d :=
  (completedReductionTower_exists T d).choose_spec.choose

/-- The representative normalization fixing the canonical comparison uniquely.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def HasCompletedReductionTowerUnitNormalization (T : Scheme.{u})
    (τ : completedDerivedConstant d T ⟶ completedReductionTower T d) : Prop :=
  letI := completedReductionModuleTowerFunctor_additive T d
  ∀ P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients
          (R := pbcAdicCompletion T d) P →
        τ.app (DerivedCategory.Q.obj P) ≫
            (completedReductionTowerCounit d T).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
          ((completedTowerConstant d T).mapDerivedCategoryFactors).hom.app P ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex (completedReductionModuleUnit d T)
                (.up ℤ)).app P)

private theorem exactAugmentation_existsUnique
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (E F : B ⥤ C) [E.Additive] [F.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (L : DerivedCategory B ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso B (.up ℤ))]
    (u : E ⟶ F) (S : CochainComplex B ℤ → Prop)
    (hiso : ∀ P, S P → IsIso (ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P)))
    (hrep : ∀ K : DerivedCategory B, ∃ P, S P ∧ Nonempty (DerivedCategory.Q.obj P ≅ K)) :
    ∃! τ : E.mapDerivedCategory ⟶ L, ∀ P : CochainComplex B ℤ, S P →
      τ.app (DerivedCategory.Q.obj P) ≫
          ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P) =
        E.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app P) := by
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  let β : DerivedCategory.Qh ⋙ E.mapDerivedCategory ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    E.mapDerivedCategoryFactorsh.hom ≫
      Functor.whiskerRight (NatTrans.mapHomotopyCategory u (.up ℤ)) DerivedCategory.Qh
  let τ := L.leftDerivedLift ε W E.mapDerivedCategory β
  have hτ (P : CochainComplex B ℤ) :
      τ.app (DerivedCategory.Q.obj P) ≫
          ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P) =
        E.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app P) := by
    have h := L.leftDerived_fac_app ε W E.mapDerivedCategory β
      ((HomotopyCategory.quotient B (.up ℤ)).obj P)
    change τ.app _ ≫ ε.app _ = E.mapDerivedCategoryFactorsh.hom.app _ ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory u (.up ℤ)).app _) at h
    rw [E.mapDerivedCategoryFactorsh_hom_app] at h
    change τ.app (DerivedCategory.Q.obj P) ≫
      ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P) =
      (E.mapDerivedCategory.map (𝟙 _) ≫ E.mapDerivedCategoryFactors.hom.app P ≫
        𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _)) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app P) at h
    erw [E.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
      Category.id_comp, Category.comp_id, Category.comp_id] at h
    exact h
  refine ⟨τ, fun P _ ↦ hτ P, ?_⟩
  intro τ' hτ'
  apply NatTrans.ext
  funext K
  obtain ⟨P, hP, ⟨e⟩⟩ := hrep K
  have := hiso P hP
  have he : τ'.app (DerivedCategory.Q.obj P) = τ.app (DerivedCategory.Q.obj P) := by
    apply (cancel_mono (ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P))).1
    exact (hτ' P hP).trans (hτ P).symm
  apply (cancel_epi (E.mapDerivedCategory.map e.hom)).1
  rw [τ'.naturality, τ.naturality, he]

private theorem independentKFlatRepresentatives
    {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{u₂} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u₂} RingCat.{u₂})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u₂}]
    [HasSheafify J AddCommGrpCat.{u₂}]
    (R : Sheaf J CommRingCat.{u₂})
    [HasDerivedCategory (SheafOfModules.{u₂}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (K : DerivedCategory (SheafOfModules.{u₂}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :
    ∃ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  let G := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) G
  have := hp
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map p) ≪≫ e⟩⟩

/-- The quotient unit descends uniquely from its strict K-flat construction.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: for a K-flat representative use its strict quotient-unit map, transported by
the invertible reduction counit. K-flat resolutions compare any two representatives;
naturality on this resolving class descends to the derived category. Every object has
such a representative, so the specified normalization determines the unit uniquely. -/
theorem completedReductionTowerUnit_exists (T : Scheme.{u}) :
    ∃! τ : completedDerivedConstant d T ⟶ completedReductionTower T d,
      HasCompletedReductionTowerUnitNormalization d T τ := by
  have : DerivedCategory.Qh.IsLocalization
      (HomotopyCategory.quasiIso (pbcModules T (pbcAdicCompletion T d)) (.up ℤ)) :=
    inferInstance
  have : (completedReductionTower T d).IsLeftDerivedFunctor
      (completedReductionTowerCounit d T)
      (HomotopyCategory.quasiIso (pbcModules T (pbcAdicCompletion T d)) (.up ℤ)) :=
    (completedReductionTower_properties T d).1
  have : (completedReductionModuleTowerFunctor T d).Additive :=
    completedReductionModuleTowerFunctor_additive T d
  have hrep := independentKFlatRepresentatives (pbcAdicCompletion T d)
  exact exactAugmentation_existsUnique (completedTowerConstant d T)
    (completedReductionModuleTowerFunctor T d) (completedReductionTower T d)
    (completedReductionTowerCounit d T) (completedReductionModuleUnit d T)
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion T d) P)
    (completedReductionTower_properties T d).2.2 hrep

/-- The canonical strict derived reduction unit ΔK → K_bullet.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedReductionTowerUnit (T : Scheme.{u}) :
    completedDerivedConstant d T ⟶ completedReductionTower T d :=
  (completedReductionTowerUnit_exists d T).exists.choose

/-- The tower universal counit on actual cochain representatives.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedTowerPullbackComplexCounit
    (P : CochainComplex (pbcTowers Y (pbcAdicCompletion Y d)) ℤ) :
    (completedTowerPullback g d).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((completedTowerModulePullback g d).mapHomologicalComplex
        (.up ℤ)).obj P) :=
  Functor.leftDerivedCounitOnComplex (completedTowerModulePullback g d)
    (completedTowerPullback g d) (completedTowerPullbackCounit g d) P

/-- The ordinary universal counit on actual cochain representatives.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedOrdinaryPullbackComplexCounit
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    (completedOrdinaryPullback g d).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((completedModulePullback g d).mapHomologicalComplex
        (.up ℤ)).obj P) :=
  Functor.leftDerivedCounitOnComplex (completedModulePullback g d)
    (completedOrdinaryPullback g d) (completedOrdinaryPullbackCounit g d) P

private theorem mapComplexObject_eq_of_functor_eq
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (h : F = G) (P : CochainComplex C ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj P =
      (G.mapHomologicalComplex (.up ℤ)).obj P := by
  subst G
  rfl

/-- The two ordinary constant-tower pullback complexes are the same strict complex.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: at each degree and tower index both have g^*(P^q), differential g^*(d^q), and
identity transition. The structure maps and their proofs agree by extensionality. -/
theorem completedPullbackConstantComplex_eq
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ) :
    ((completedTowerConstant d X).mapHomologicalComplex (.up ℤ)).obj
      (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) =
    ((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
      (((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ)).obj P) := by
  have hobj (M : pbcModules Y (pbcAdicCompletion Y d)) :
      (Functor.const ℕᵒᵖ).obj ((completedModulePullback g d).obj M) =
        (Functor.const ℕᵒᵖ).obj M ⋙ completedModulePullback g d := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
      Functor.comp_map, Functor.const_obj_map]
    exact ((completedModulePullback g d).map_id M).symm
  have he : completedModulePullback g d ⋙ completedTowerConstant d X =
      completedTowerConstant d Y ⋙ completedTowerModulePullback g d := by
    refine CategoryTheory.Functor.ext hobj ?_
    intro M N f
    apply NatTrans.ext
    funext n
    simp only [NatTrans.comp_app, eqToHom_app, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    rfl
  exact mapComplexObject_eq_of_functor_eq he P

/-- The representative normalization fixing the canonical comparison uniquely.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def HasCompletedPullbackConstantNormalization
    (e : completedOrdinaryPullback g d ⋙ completedDerivedConstant d X ≅
        completedDerivedConstant d Y ⋙ completedTowerPullback g d) : Prop :=
  ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients
          (R := pbcAdicCompletion Y d) P →
        (completedDerivedConstant d X).map
            (completedOrdinaryPullbackComplexCounit g d P) ≫
          ((completedTowerConstant d X).mapDerivedCategoryFactors).hom.app
            (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (eqToHom (completedPullbackConstantComplex_eq g d P)) =
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (completedTowerPullback g d).map
            (((completedTowerConstant d Y).mapDerivedCategoryFactors).hom.app P) ≫
          completedTowerPullbackComplexCounit g d
            (((completedTowerConstant d Y).mapHomologicalComplex (.up ℤ)).obj P)

/-- Pullback of a constant tower is canonically the constant tower of ordinary pullback.
The equality on strict representatives and both universal counits fix the comparison.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: constant K-flat representatives lie in the tower resolving class. Both sides
compute the same pulled-back constant complex. Its strict equality gives the displayed
normalization. Universal left derivation extends it uniquely and proves invertibility. -/
theorem completedPullbackConstantIso_exists :
    ∃! e : completedOrdinaryPullback g d ⋙ completedDerivedConstant d X ≅
        completedDerivedConstant d Y ⋙ completedTowerPullback g d,
      HasCompletedPullbackConstantNormalization g d e := by
  sorry

/-- The uniquely normalized constant-tower pullback comparison.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedPullbackConstantIso :
    completedOrdinaryPullback g d ⋙ completedDerivedConstant d X ≅
      completedDerivedConstant d Y ⋙ completedTowerPullback g d :=
  (completedPullbackConstantIso_exists g d).exists.choose

/-- Completed pullback is the derived inverse limit of the pulled-back reduction tower.
Its restriction to intrinsically complete objects is the completed pullback of the node.
Source: Stacks Tag 099N (blueprint: def-weil-pbc-completed-pullback). -/
def completedPullbackObject
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) :
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)) :=
  (completedTowerRlim d X).obj
    ((completedTowerPullback g d).obj ((completedReductionTower Y d).obj K))

/-- The strict-tower-induced comparison, using the canonical K → Rlim ΔK unit.
No map between independently selected cones is used.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedPullbackComparison
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) :
    (completedOrdinaryPullback g d).obj K ⟶ completedPullbackObject g d K :=
  (completedConstantRlimUnit d X).app ((completedOrdinaryPullback g d).obj K) ≫
    (completedTowerRlim d X).map
      ((completedPullbackConstantIso g d).hom.app K ≫
        (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app K))

/-- Finite evaluation comparison applies to reduction towers, with their quotient
coefficients. It is not a formula for arbitrary completed-coefficient tower evaluations.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: use a flat-term K-flat representative, the flat constant-to-completed comparison,
and its finite reductions. Finite constant inverse image is exact. The balancing
identification gives the level comparison; its tensor formula commutes with quotient
maps, so the evaluation comparisons respect the strict transitions. -/
theorem completedPullback_reductionEvaluation (n : ℕ) :
    Nonempty (completedReductionTower Y d ⋙ completedTowerPullback g d ⋙
        pbcTowerEvaluation X (pbcAdicCompletion X d) n ≅
      reductionDerivedChange Y (pbcAdicProjection Y d n) ⋙
        proEtaleRingDerivedPullback g ((pbcAdicRings Y d).obj (op n))
          ((pbcAdicRings X d).obj (op n))
          (asIso (completedFiniteCoefficientMap g d n)) ⋙
        pbcDerivedRestrict (pbcAdicProjection X d n)) := by
  sorry

/-- On intrinsically complete inputs this construction is ordinary pullback followed
by intrinsic derived completion, with exactly its completion unit. Under the canonical
derived-complete constant/completed coefficient equivalences this is Stacks' completed pullback.
Source: Stacks Tag 099N, clauses (2),(5) (blueprint: def-weil-pbc-completed-pullback).
Proof: apply the constant/completed coefficient equivalence to a K-flat representative.
Its finite-reduction comparisons identify the pulled-back strict tower, including
transitions, with the reduction tower of ordinary pullback. They identify the derived
limits and their units. The intrinsic Koszul completion comparison identifies that
limit with the displayed intrinsic completion and takes the comparison to its unit. -/
theorem completedPullback_isCompletion (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (C : CochainComplex (pbcModules Y (pbcAdicCompletion Y d)) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K)
    (_hK : IsDerivedCompleteIntrinsic Y d r a ha K C e)
    (P : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ (completedOrdinaryPullback g d).obj K) :
    ∃ α : completedPullbackObject g d K ≅
        intrinsicCompletion X d r a ha ((completedOrdinaryPullback g d).obj K) P eP,
      completedPullbackComparison g d K ≫ α.hom =
        intrinsicCompletionUnit X d r a ha ((completedOrdinaryPullback g d).obj K) P eP := by
  sorry

end AlgebraicGeometry.Scheme
