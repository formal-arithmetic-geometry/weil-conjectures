/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.Limits.FullSubcategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheaves
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Classical module sheaves form a weak Serre subcategory

Classical pro-étale module sheaves are closed under kernels, cokernels and extensions
(blueprint: `corollary-bounded-below-classical-complexes--1`).

Kernels and cokernels: classical sheaves form the essential image of the exact fully faithful
functor `ν^*`. Extensions: the derived counit of `ν^* ⊣ Rν_*` is invertible on classical
sheaves placed in degree `0`, hence, by the triangle attached to a short exact sequence, on the middle
term, which is therefore `ν^*` of the étale sheaf `H⁰(Rν_* G)`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (P : ObjectProperty C)

/-- A property closed under limits of parallel pairs is closed under kernels. -/
lemma isClosedUnderKernels_of_isClosedUnderLimitsOfShape
    [P.IsClosedUnderLimitsOfShape WalkingParallelPair] : P.IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact P.prop_of_isLimit hk (by rintro (_ | _) <;> assumption)

/-- A property closed under colimits of parallel pairs is closed under cokernels. -/
lemma isClosedUnderCokernels_of_isClosedUnderColimitsOfShape
    [P.IsClosedUnderColimitsOfShape WalkingParallelPair] : P.IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact P.prop_of_isColimit hk (by rintro (_ | _) <;> assumption)

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.ProEtale

/-- Classicality of module sheaves is invariant under isomorphism. -/
theorem isClassicalModuleFor_of_iso (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
    (e : F ≅ G) (hF : IsClassicalModuleFor X Λ F) : IsClassicalModuleFor X Λ G := by
  intro I _ _ P
  have : IsIso (continuityMap P F.obj) := hF P
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map e.hom))
  apply (isIso_comp_left_iff
    (colimMap (Functor.whiskerLeft P.diagram.op e.hom.hom)) _).mp
  rw [continuityMap_natural P e.hom.hom]
  infer_instance

instance (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    ObjectProperty.IsClosedUnderIsomorphisms (IsClassicalModuleFor X Λ) :=
  ⟨fun e h ↦ isClassicalModuleFor_of_iso X Λ e h⟩

/-- Classical module sheaves are exactly the essential image of the comparison
inverse image `ν^*`. -/
theorem isClassicalModuleFor_eq_essImage (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    IsClassicalModuleFor X Λ = (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).essImage := by
  obtain ⟨E, hE, hEq, -, -⟩ := (AlgebraicGeometry.proEtaleClassicalSheaves X).2.2 Λ
  rw [← hE]
  ext G
  constructor
  · intro hG
    obtain ⟨M, ⟨e⟩⟩ : E.essImage ⟨G, hG⟩ :=
      Functor.EssSurj.mem_essImage E _
    exact ⟨M, ⟨(ObjectProperty.ι _).mapIso e⟩⟩
  · rintro ⟨M, ⟨e⟩⟩
    exact isClassicalModuleFor_of_iso X Λ e (E.obj M).property

/-- Classical module sheaves are closed under kernels
(blueprint: `corollary-bounded-below-classical-complexes--1`). -/
instance isClosedUnderKernels_isClassicalModuleFor (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] : ObjectProperty.IsClosedUnderKernels (IsClassicalModuleFor X Λ) := by
  rw [isClassicalModuleFor_eq_essImage]
  exact ObjectProperty.isClosedUnderKernels_of_isClosedUnderLimitsOfShape _

/-- Classical module sheaves are closed under cokernels
(blueprint: `corollary-bounded-below-classical-complexes--1`). -/
instance isClosedUnderCokernels_isClassicalModuleFor (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] : ObjectProperty.IsClosedUnderCokernels (IsClassicalModuleFor X Λ) := by
  rw [isClassicalModuleFor_eq_essImage]
  exact ObjectProperty.isClosedUnderCokernels_of_isClosedUnderColimitsOfShape _

/-- Classical module sheaves are closed under extensions
(blueprint: `corollary-bounded-below-classical-complexes--1`). -/
instance isClosedUnderExtensions_isClassicalModuleFor (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] : ObjectProperty.IsClosedUnderExtensions (IsClassicalModuleFor X Λ) where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    let A := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    let B := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
    let F₀ := comparisonUpperStar (ModuleCat.{u + 1} Λ) X
    let R₀ := comparisonLowerStar (ModuleCat.{u + 1} Λ) X
    let F := F₀.mapDerivedCategoryPlus
    let R := R₀.rightDerivedFunctorPlus
    let adj := (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus
    let : R.CommShift ℤ := adj.rightAdjointCommShift ℤ
    let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
    let : R.IsTriangulated := adj.isTriangulated_rightAdjoint
    have : IsIso adj.unit := (boundedBelowComparison X Λ).1
    let ff := adj.fullyFaithfulLOfIsIsoUnit
    let : F.Full := ff.full
    let : F.Faithful := ff.faithful
    have hsingle (G : B) (hG : IsClassicalModuleFor X Λ G) :
        IsIso (adj.counit.app ((DerivedCategory.Plus.singleFunctor B 0).obj G)) := by
      rw [isClassicalModuleFor_eq_essImage] at hG
      obtain ⟨M, ⟨eG⟩⟩ := hG
      exact adj.isIso_counit_app_of_iso
        ((F₀.mapDerivedCategoryPlusSingleFunctor 0).app M ≪≫
          (DerivedCategory.Plus.singleFunctor B 0).mapIso eG).symm
    have h₂ : IsIso (adj.counit.app hS.singleTrianglePlus.obj₂) :=
      NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃ adj.counit
        hS.singleTrianglePlus_distinguished
        (hsingle _ h₁) (hsingle _ h₃)
    rw [isClassicalModuleFor_eq_essImage]
    exact ⟨(DerivedCategory.Plus.homologyFunctor A 0).obj
        (R.obj ((DerivedCategory.Plus.singleFunctor B 0).obj S.X₂)),
      ⟨(F₀.mapDerivedCategoryPlusHomologyFunctorIso 0).app _ ≪≫
        (DerivedCategory.Plus.homologyFunctor B 0).mapIso (@asIso _ _ _ _ _ h₂) ≪≫
        (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app S.X₂⟩⟩

/-- Classical module sheaves form a weak Serre subcategory: they are closed under kernels,
cokernels and extensions
(blueprint: `corollary-bounded-below-classical-complexes--1`). -/
theorem isClassicalModuleFor_isWeakSerre (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    ObjectProperty.IsClosedUnderKernels (IsClassicalModuleFor X Λ) ∧
      ObjectProperty.IsClosedUnderCokernels (IsClassicalModuleFor X Λ) ∧
      ObjectProperty.IsClosedUnderExtensions (IsClassicalModuleFor X Λ) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.ProEtale

end
