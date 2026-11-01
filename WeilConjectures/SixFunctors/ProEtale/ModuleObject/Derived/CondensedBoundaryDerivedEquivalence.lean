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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedBoundaryModuleEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedBoundaryConstructibility
import WeilConjectures.CategoryTheory.FiniteProductDerived.FiniteProductDerivedLocalization
import WeilConjectures.CategoryTheory.FiniteProductCoordinates.AdditiveFiniteProductCoordinates
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude

/-! # Derived finite-component decomposition with constructible bounds -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
attribute [local instance] CategoryTheory.FiniteProductCoordinates.piPreadditive
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
  (I : Type w) [Finite I]

omit [IsAlgClosed k] in
private theorem boundary_derived_equivalence :
    ∃ E : DerivedCategory (CondensedBoundaryMod ℓ k I) ≌
        (I → DerivedCategory (PointMod ℓ k)),
      E.functor = Functor.pi' (fun i ↦
        (condensedBoundaryRestriction ℓ k I i).mapDerivedCategory) := by
  obtain ⟨E, hE⟩ := condensed_boundary_module_equivalence ℓ k I
  let r := condensedBoundaryRestriction ℓ k I
  have : E.functor.Additive := by
    rw [hE]
    constructor
    intro M N f g
    funext i
    exact (r i).map_add
  have hr : JointlyReflectIsomorphisms r := by
    constructor
    intro M N f hf
    have : IsIso (E.functor.map f) := by
      rw [hE]
      exact (isIso_pi_iff _).mpr fun i ↦ hf i
    exact isIso_of_reflects_iso f E.functor
  have η : 𝟭 _ ≅ Functor.pi' r ⋙ E.inverse := by simpa only [hE] using E.unitIso
  have ε : E.inverse ⋙ Functor.pi' r ≅ 𝟭 _ := by simpa only [hE] using E.counitIso
  have : (Functor.pi' (fun i ↦ (r i).mapDerivedCategory)).IsEquivalence :=
    CategoryTheory.FiniteProductDerived.derivedPi_isEquivalence r E.inverse
      (fun M N ↦ E.inverse.map_zero M N) η ε hr
  exact ⟨(Functor.pi' (fun i ↦ (r i).mapDerivedCategory)).asEquivalence, rfl⟩

omit [IsAlgClosed k] in
private theorem boundary_zero_of_restrictions (M : CondensedBoundaryMod ℓ k I)
    (h : ∀ i, IsZero ((condensedBoundaryRestriction ℓ k I i).obj M)) : IsZero M := by
  obtain ⟨E, hE⟩ := condensed_boundary_module_equivalence ℓ k I
  have : E.functor.Additive := by
    rw [hE]
    constructor
    intro X Y f g
    funext i
    exact (condensedBoundaryRestriction ℓ k I i).map_add
  rw [IsZero.iff_id_eq_zero]
  apply E.functor.map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero, hE]
  funext i
  exact (h i).eq_of_src _ _

omit [IsAlgClosed k] in
private theorem boundary_bounded_iff (K : DerivedCategory (CondensedBoundaryMod ℓ k I)) :
    DerivedCategory.TStructure.t.bounded K ↔ ∀ i,
      DerivedCategory.TStructure.t.bounded
        ((condensedBoundaryRestriction ℓ k I i).mapDerivedCategory.obj K) := by
  classical
  constructor
  · intro h i
    exact (condensedBoundaryRestriction ℓ k I i).bounded_mapDerivedCategory_obj h
  · intro h
    let := Fintype.ofFinite I
    choose S hS using fun i ↦ (finite_support_iff_bounded _).mpr (h i)
    apply (finite_support_iff_bounded K).mp
    refine ⟨Finset.univ.biUnion S, fun n hn ↦ ?_⟩
    apply boundary_zero_of_restrictions ℓ k I
    intro i
    let F := condensedBoundaryRestriction ℓ k I i
    let e := (F.mapDerivedCategoryHomologyFunctorIso n).app K
    exact (hS i n (by
      intro hh
      exact hn (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hh⟩))).of_iso e

private theorem boundary_constructible_bounded_iff
    (K : DerivedCategory (CondensedBoundaryMod ℓ k I)) :
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
        (condensedPointBoundary k I) K ↔ ∀ i,
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) (point k).left
        ((condensedBoundaryRestriction ℓ k I i).mapDerivedCategory.obj K) := by
  have := (constantModelConstructibleFiniteTor_wellDefined
    (Profinite.padicAlgClRingObj ℓ) (point k).left).1
  constructor
  · intro h i
    refine ⟨(boundary_bounded_iff ℓ k I K).mp h.1 i, fun n ↦ ?_⟩
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible
      (Profinite.padicAlgClRingObj ℓ) (point k).left)
      (((condensedBoundaryRestriction ℓ k I i).mapDerivedCategoryHomologyFunctorIso n).app K)
      ((condensed_boundary_constructible_iff ℓ k I _).mp (h.2 n) i)
  · intro h
    refine ⟨(boundary_bounded_iff ℓ k I K).mpr (fun i ↦ (h i).1), fun n ↦ ?_⟩
    apply (condensed_boundary_constructible_iff ℓ k I _).mpr
    intro i
    let F := condensedBoundaryRestriction ℓ k I i
    let e := (F.mapDerivedCategoryHomologyFunctorIso n).app K
    exact ObjectProperty.prop_of_iso (IsConstantModelConstructible
      (Profinite.padicAlgClRingObj ℓ) (point k).left) e.symm ((h i).2 n)

private theorem restrictProductEquivalence
    {C : Type*} [Category C] {J : Type*} {D : J → Type*} [∀ i, Category (D i)]
    (r : ∀ i, C ⥤ D i) (E : C ≌ ∀ i, D i)
    (hE : E.functor = Functor.pi' r) (P : ObjectProperty C)
    (Q : ∀ i, ObjectProperty (D i))
    (hP : ∀ K, P K ↔ ∀ i, Q i ((r i).obj K))
    (hQ : ∀ i {K L : D i}, (K ≅ L) → Q i K → Q i L) :
    ∃ e : P.FullSubcategory ≌ ∀ i, (Q i).FullSubcategory,
      Nonempty (e.functor ⋙ Functor.pi (fun i ↦ (Q i).ι) ≅
        P.ι ⋙ Functor.pi' r) := by
  let E := E.changeFunctor (eqToIso hE)
  let F : P.FullSubcategory ⥤ ∀ i, (Q i).FullSubcategory :=
    Functor.pi' (fun i ↦ (Q i).lift (P.ι ⋙ r i) (fun K ↦ (hP K.obj).mp K.property i))
  let G : (∀ i, (Q i).FullSubcategory) ⥤ P.FullSubcategory :=
    P.lift (Functor.pi (fun i ↦ (Q i).ι) ⋙ E.inverse) (fun K ↦ (hP _).mpr
      (fun i ↦ hQ i ((Pi.eval D i).mapIso
        (E.counitIso.app (fun i ↦ (K i).obj))).symm (K i).property))
  have η : 𝟭 _ ≅ F ⋙ G := by
    refine NatIso.ofComponents (fun K ↦ P.isoMk (E.unitIso.app K.obj)) ?_
    intro K L f
    apply ObjectProperty.hom_ext P
    exact E.unitIso.hom.naturality f.hom
  have ε : G ⋙ F ≅ 𝟭 _ := by
    refine NatIso.ofComponents (fun K ↦ Pi.isoMk (fun i ↦
      (Q i).isoMk ((Pi.eval D i).mapIso (E.counitIso.app (fun i ↦ (K i).obj))))) ?_
    intro K L f
    funext i
    apply ObjectProperty.hom_ext (Q i)
    exact congrFun (E.counitIso.hom.naturality (fun i ↦ (f i).hom)) i
  exact ⟨CategoryTheory.Equivalence.mk F G η ε, ⟨Iso.refl _⟩⟩

/-- Finite clopen gluing restricts to bounded constructible derived objects.
Source: blueprint local boundary duality, Step 5, finite clopen gluing.
Proof: derive the equivalence of module categories by the finite product
localization theorem. Exact restriction commutes with cohomology, and module
constructibility is componentwise. Boundedness is componentwise because the
finite union of the component cohomological supports is finite and restriction
jointly detects zero. Restrict the resulting equivalence to these full
subcategories; its forward functor remains the actual component restrictions.
The empty family is included in the finite-support argument.
(blueprint: lem-a1-condensed-boundary-derived-equivalence) -/
theorem condensed_boundary_derived_equivalence :
    ∃ E : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
        (condensedPointBoundary k I) ≌
      (I → ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) (point k).left),
      ∀ i, Nonempty (E.functor ⋙ Pi.eval _ i ⋙
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) (point k).left).ι ≅
        (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
          (condensedPointBoundary k I)).ι ⋙
          (condensedBoundaryRestriction ℓ k I i).mapDerivedCategory) := by
  obtain ⟨E, hE⟩ := boundary_derived_equivalence ℓ k I
  obtain ⟨e, ⟨he⟩⟩ := restrictProductEquivalence
    (fun i ↦ (condensedBoundaryRestriction ℓ k I i).mapDerivedCategory) E hE
    (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ)
      (condensedPointBoundary k I))
    (fun _ ↦ constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) (point k).left)
    (boundary_constructible_bounded_iff ℓ k I) (fun _ _ _ e h ↦ by
      have := (constantModelConstructibleFiniteTor_wellDefined
        (Profinite.padicAlgClRingObj ℓ) (point k).left).2.1
      exact ObjectProperty.prop_of_iso _ e h)
  refine ⟨e, fun i ↦ ⟨?_⟩⟩
  exact Functor.isoWhiskerRight he (Pi.eval _ i)

end AlgebraicGeometry.ProEtale.CondensedRing
