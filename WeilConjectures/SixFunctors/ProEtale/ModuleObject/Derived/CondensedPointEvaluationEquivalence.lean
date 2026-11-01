/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.PointFiberFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarLimits
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonScalarColimits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointFiniteFreeModels


/-! # Evaluation equivalence at one geometric point -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem finite_support_iff_bounded
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) :
    (∃ I : Finset ℤ, ∀ i, i ∉ I →
      IsZero ((DerivedCategory.homologyFunctor C i).obj K)) ↔
      DerivedCategory.TStructure.t.bounded K := by
  classical
  have h : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K)} ↔
      DerivedCategory.TStructure.t.bounded K := by
    rw [Set.finite_iff_bddBelow_bddAbove]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨⟨a, (DerivedCategory.isGE_iff K a).2 fun i hi ↦ by
        by_contra hh
        exact (not_le_of_gt hi) (ha hh)⟩,
        ⟨b, (DerivedCategory.isLE_iff K b).2 fun i hi ↦ by
          by_contra hh
          exact (not_le_of_gt hi) (hb hh)⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨⟨a, fun i hi ↦ le_of_not_gt fun hh ↦
        hi ((DerivedCategory.isGE_iff K a).1 ha i hh)⟩,
        ⟨b, fun i hi ↦ le_of_not_gt fun hh ↦
          hi ((DerivedCategory.isLE_iff K b).1 hb i hh)⟩⟩
  rw [← h]
  constructor
  · rintro ⟨I, hI⟩
    exact I.finite_toSet.subset fun i hi ↦ by
      by_contra hh
      exact hi (hI i hh)
  · intro hI
    exact ⟨hI.toFinset, fun i hi ↦ by
      by_contra hh
      exact hi (hI.mem_toFinset.mpr hh)⟩

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]

private theorem finite_dimensional_sections (M : PointMod ℓ k)
    (hM : pointFiniteFree ℓ k M) :
    Module.Finite (ULift.{u + 1} (PadicAlgCl ℓ)) ((pointSections ℓ k).obj M) := by
  obtain ⟨n, ⟨e⟩⟩ := hM
  let r := (pointSections ℓ k).mapIso e ≪≫
    (pointSections ℓ k).mapBiproduct (fun _ : Fin n ↦ 𝟙_ (PointMod ℓ k)) ≪≫
      biproduct.mapIso (fun _ ↦ (pointSectionsUnitIso ℓ k).symm) ≪≫
        ModuleCat.biproductIsoPi (fun _ : Fin n ↦
          ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl ℓ)))
  have : Module.Finite (ULift.{u + 1} (PadicAlgCl ℓ))
      (Fin n → ULift.{u + 1} (PadicAlgCl ℓ)) := inferInstance
  exact Module.Finite.equiv r.toLinearEquiv.symm

private theorem point_evaluation_finite
    (K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) (point k).left) :
    DerivedCategory.pointFiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))
      ((pointSections ℓ k).mapDerivedCategory.obj K.obj) := by
  refine ⟨(finite_support_iff_bounded _).mpr
    ((pointSections ℓ k).bounded_mapDerivedCategory_obj K.property.1), fun n ↦ ?_⟩
  let e := ((pointSections ℓ k).mapDerivedCategoryHomologyFunctorIso n).app K.obj
  exact (Module.Finite.equiv_iff e.toLinearEquiv).mp
    (finite_dimensional_sections ℓ k _
      ((constantModelConstructible_iff_pointFiniteFree ℓ k _).mp (K.property.2 n)))

private theorem point_constant_model_shift_sum
    (K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) (point k).left) :
    DerivedCategory.IsShiftSum (pointFiniteFree ℓ k) K.obj := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property.1
  exact DerivedCategory.isShiftSum_of_isGE_of_isLE
    (fun X hX ↦ pointFiniteFree_of_isZero ℓ k hX)
    (fun X hX ↦ projective_of_pointFiniteFree ℓ k hX) ha hb
    (fun q ↦ (constantModelConstructible_iff_pointFiniteFree ℓ k _).mp (K.property.2 q))

private def scalarExtension_regular_iso :
    (condensedPointScalarExtension ℓ k).obj
      (ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl ℓ))) ≅ 𝟙_ (PointMod ℓ k) := by
  let F := pointSections ℓ k ⋙ forget (ModuleCat.{u + 1}
    (ULift.{u + 1} (PadicAlgCl ℓ)))
  let adj := condensedPointScalarAdjunction ℓ k
  let p : F.CorepresentableBy ((condensedPointScalarExtension ℓ k).obj
      (ModuleCat.of _ (ULift.{u + 1} (PadicAlgCl ℓ)))) :=
    { homEquiv := fun {M} ↦ (adj.homEquiv _ M).trans
        (ModuleCat.homEquiv.trans
          (LinearMap.ringLmapEquivSelf (ULift.{u + 1} (PadicAlgCl ℓ)) ℤ
            ((pointSections ℓ k).obj M)).toEquiv)
      homEquiv_comp := by
        intro M N f g
        simp only [Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
        rfl }
  let q : F.CorepresentableBy (𝟙_ (PointMod ℓ k)) :=
    { homEquiv := Equiv.refl _
      homEquiv_comp := by intros; rfl }
  exact p.uniqueUpToIso q

private theorem finite_free_scalarExtension
    (M : ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)))
    [Module.Finite (ULift.{u + 1} (PadicAlgCl ℓ)) M] :
    pointFiniteFree ℓ k ((condensedPointScalarExtension ℓ k).obj M) := by
  let L := condensedPointScalarExtension ℓ k
  let K := ULift.{u + 1} (PadicAlgCl ℓ)
  let n := Module.finrank K M
  let e : M ≅ ModuleCat.of K (Fin n → K) := (Module.finBasis K M).equivFun.toModuleIso
  exact ⟨n, ⟨L.mapIso e ≪≫
    L.mapIso (ModuleCat.biproductIsoPi (fun _ : Fin n ↦ ModuleCat.of K K)).symm ≪≫
      L.mapBiproduct (fun _ : Fin n ↦ ModuleCat.of K K) ≪≫
        biproduct.mapIso (fun _ ↦ scalarExtension_regular_iso ℓ k)⟩⟩

private theorem scalarExtension_constructible
    (M : (DerivedCategory.pointFiniteDimensional
      (ULift.{u + 1} (PadicAlgCl ℓ))).FullSubcategory) :
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) (point k).left
      ((condensedPointScalarExtension ℓ k).mapDerivedCategory.obj M.obj) := by
  refine ⟨(condensedPointScalarExtension ℓ k).bounded_mapDerivedCategory_obj
    ((finite_support_iff_bounded _).mp M.property.1), fun n ↦ ?_⟩
  apply (constantModelConstructible_iff_pointFiniteFree ℓ k _).mpr
  have := M.property.2 n
  let e := ((condensedPointScalarExtension ℓ k).mapDerivedCategoryHomologyFunctorIso n).app
    M.obj
  exact (pointFiniteFree ℓ k).prop_of_iso e
    (finite_free_scalarExtension ℓ k _)

/-- Point evaluation is an equivalence on the finite constant model subcategory.
Source: blueprint local boundary duality, Step 5, point reconstruction.
Proof: the finite constant model classification gives finite free cohomology. Since
the unit is projective, truncation triangles split into shifts of finite free objects.
Evaluation is bijective on morphisms between their shifts, hence fully faithful.
Its cohomology is bounded and finite dimensional. Conversely the existing point-fiber
essential-image theorem gives a bounded constructible representative of any finite
scalar complex; its cohomology is finite free and hence has finite constant models.
Finite support and boundedness are equivalent, including the zero complex.
(blueprint: lem-a1-condensed-point-evaluation-equivalence) -/
theorem point_evaluation_equivalence
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    ∃ P : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
      (point k).left ≌
        (DerivedCategory.pointFiniteDimensional
          (ULift.{u + 1} (PadicAlgCl ℓ))).FullSubcategory,
      Nonempty (P.functor ⋙
        (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))).ι ≅
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
          (point k).left).ι ⋙ (pointSections ℓ k).mapDerivedCategory) := by
  classical
  let Q := constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) (point k).left
  let T := DerivedCategory.pointFiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))
  let F := Q.ι ⋙ (pointSections ℓ k).mapDerivedCategory
  have hF (K L : Q.FullSubcategory) : Function.Bijective (fun f : K ⟶ L ↦ F.map f) :=
    (DerivedCategory.homBijective_of_isShiftSum
      (fun _ _ hX hY b ↦ homBijective_pointSections_finiteFree ℓ k hX hY b)
      (point_constant_model_shift_sum ℓ k K) (point_constant_model_shift_sum ℓ k L)).comp
      ((ObjectProperty.fullyFaithfulι Q).map_bijective K L)
  have : F.Full := ⟨fun f ↦ (hF _ _).2 f⟩
  have : F.Faithful := ⟨fun h ↦ (hF _ _).1 h⟩
  let G := T.lift F (point_evaluation_finite ℓ k)
  have : G.EssSurj := by
    constructor
    intro M
    have hM : DerivedCategory.boundedFiniteCohomology _ M.obj :=
      ⟨(finite_support_iff_bounded _).mp M.property.1, M.property.2⟩
    obtain ⟨K, ⟨e⟩⟩ := exists_pointFiberFunctor_obj_iso ℓ k hM
    have hK : Q K.obj := by
      refine ⟨K.property.1, fun q ↦ ?_⟩
      apply (constantModelConstructible_iff_pointFiniteFree ℓ k _).mpr
      obtain ⟨n, ⟨en⟩⟩ := isFiniteFree_upperStar_homology ℓ (Field.toIsField k)
        IsField.isSepClosed_toField K q (𝟙 _)
      exact ⟨n, ⟨((upperStarId _ _).app _).symm ≪≫ en⟩⟩
    exact ⟨⟨K.obj, hK⟩, ⟨T.isoMk e⟩⟩
  have : G.IsEquivalence := {}
  exact ⟨G.asEquivalence, ⟨Iso.refl _⟩⟩

/-- The inverse of point evaluation is the specified copower scalar extension.
Source: blueprint local boundary duality, Step 5, derived adjunction.
Proof: scalar extension sends the regular scalar module to the coefficient unit,
by their identical corepresented section functors. A finite basis therefore shows
that it sends finite dimensional modules to finite free coefficient modules.
Exactness and homology comparison restrict its derived adjunction to the two full
subcategories. Uniqueness of left adjoints identifies it with the inverse of the
point evaluation equivalence, retaining both ambient functor comparisons.
(blueprint: lem-a1-condensed-point-evaluation-equivalence) -/
theorem point_evaluation_equivalence_with_inverse
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    ∃ P : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
      (point k).left ≌
        (DerivedCategory.pointFiniteDimensional
          (ULift.{u + 1} (PadicAlgCl ℓ))).FullSubcategory,
      Nonempty (P.functor ⋙
        (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))).ι ≅
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
          (point k).left).ι ⋙ (pointSections ℓ k).mapDerivedCategory) ∧
      Nonempty (P.inverse ⋙
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
          (point k).left).ι ≅
        (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))).ι ⋙
          (condensedPointScalarExtension ℓ k).mapDerivedCategory) := by
  obtain ⟨P, ⟨e⟩⟩ := point_evaluation_equivalence ℓ k
  let Q := constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) (point k).left
  let T := DerivedCategory.pointFiniteDimensional (ULift.{u + 1} (PadicAlgCl ℓ))
  let L := Q.lift (T.ι ⋙ (condensedPointScalarExtension ℓ k).mapDerivedCategory)
    (scalarExtension_constructible ℓ k)
  let R := T.lift (Q.ι ⋙ (pointSections ℓ k).mapDerivedCategory)
    (point_evaluation_finite ℓ k)
  let a : L ⊣ R :=
    (condensedPointScalarAdjunction ℓ k).mapDerivedCategoryAdjunction.restrictFullyFaithful
      (ObjectProperty.fullyFaithfulι T) (ObjectProperty.fullyFaithfulι Q)
      (Iso.refl _) (Iso.refl _)
  let b : R ≅ P.functor := (Functor.fullyFaithfulCancelRight T.ι e).symm
  let c := (a.ofNatIsoRight b).leftAdjointUniq P.symm.toAdjunction
  exact ⟨P, ⟨e⟩, ⟨Functor.isoWhiskerRight c.symm Q.ι⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
