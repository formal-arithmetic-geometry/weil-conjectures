/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Shift.Localization
import all Sheaf.Paper.ScalarExtensionExactIntrinsic

/-! # Exactness descends to the raw rational point fibre

Source: Stacks, Derived Categories, Tag 05R6; step 10 of the point-fibre proof.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option cleanup.letToHave false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private instance pointFdIsoClosed (F : Type u) [Field F] :
    (DerivedCategory.pointFiniteDimensional F).IsClosedUnderIsomorphisms where
  of_iso e h := by
    obtain ⟨⟨s, hs⟩, hfd⟩ := h
    refine ⟨⟨s, fun i hi ↦ (hs i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e).symm⟩, ?_⟩
    intro i
    have := hfd i
    exact ((DerivedCategory.homologyFunctor _ i).mapIso e).toLinearEquiv.finiteDimensional

private instance pointFdTriangulated (F : Type u) [Field F] :
    (DerivedCategory.pointFiniteDimensional F).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, ⟨⟨∅, fun i _ ↦
    (DerivedCategory.homologyFunctor _ i).map_isZero (isZero_zero _)⟩,
    fun i ↦ by
      have := ModuleCat.isZero_iff_subsingleton.mp
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} F) i).map_isZero (isZero_zero _))
      infer_instance⟩⟩
  isStableUnderShiftBy a := ⟨fun X hX ↦ DerivedCategory.pointFd_shift_mem X hX a⟩
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦ by
    obtain ⟨⟨s₁, hs₁⟩, hf₁⟩ := h₁
    obtain ⟨⟨s₃, hs₃⟩, hf₃⟩ := h₃
    refine ⟨⟨s₁ ∪ s₃, ?_⟩, ?_⟩
    · intro i hi
      exact (DerivedCategory.HomologySequence.exact₂ T hT i).isZero_of_both_isZero
        (hs₁ i (fun h ↦ hi (Finset.mem_union_left _ h)))
        (hs₃ i (fun h ↦ hi (Finset.mem_union_right _ h)))
    · intro i
      have := hf₁ i
      have := hf₃ i
      let f := ((DerivedCategory.homologyFunctor _ i).map T.mor₁).hom
      let g := ((DerivedCategory.homologyFunctor _ i).map T.mor₂).hom
      have hex : Function.Exact f g :=
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
          (DerivedCategory.HomologySequence.exact₂ T hT i)
      exact Module.Finite.of_exact (f := f) (g := g.rangeRestrict)
        (fun y ↦ by rw [← hex y]; simp [Subtype.ext_iff]) g.surjective_rangeRestrict

/-- The specified rational fibre is exact after its fully faithful ambient inclusion.
Source: Stacks, Derived Categories, Tag 05R6; the exactness part of step 10 in the
point-fibre argument.
(blueprint: lem-weil-point-rational-fibre-exact).

Proof: integral sections and scalar extension to E are exact termwise functors.
Their derived composite commutes with integer shifts and takes distinguished
triangles to distinguished triangles. The canonical carrier lift on bounded
finite-dimensional complexes is an equivalence, and its ambient realization is
exact, so its inverse transports this exact structure to the specified small
integral-rational fibre. On each integral object, the object equality and the
pure-tensor formula defining pointRationalFibre identify its restriction along
raw localization with this functor. Since the uniformizer acts invertibly in E,
localization's shift universal property descends its shift comparison, with the
zero and addition laws inherited from the integral comparison. Every rational
distinguished triangle is isomorphic to an image of an integral distinguished
triangle. The factorization isomorphism commutes with shifts, so this image,
including its last arrow, has distinguished image. Closure under triangle
isomorphisms completes the argument. No idempotent completion is used. -/
theorem pointRationalFibre_exact
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ c : (pointRationalFibre D l hl E ⋙
        (DerivedCategory.pointFiniteDimensional E).ι).CommShift ℤ,
      ∀ T, T ∈ distTriang _ →
        (@Functor.mapTriangle _ _ _ _ _ _ _ c).obj T ∈ distTriang _ := by
  classical
  have : (pointFibreSizeLift E).IsEquivalence := pointFibreSizeLift_equivalence E
  let : (pointFibreSizeLift E).CommShift ℤ := by
    dsimp only [pointFibreSizeLift]
    infer_instance
  have : (pointFibreSizeLift E).IsTriangulated := by
    dsimp only [pointFibreSizeLift]
    infer_instance
  let t : pointFibreSizeDescent E ⋙ pointFibreSizeLift E ≅ 𝟭 _ :=
    (pointFibreSizeLift E).asEquivalence.counitIso
  let : (pointFibreSizeDescent E).CommShift ℤ := Functor.CommShift.ofComp t ℤ
  have : NatTrans.CommShift t.hom ℤ := Functor.CommShift.ofComp_compatibility t ℤ
  have : (pointFibreSizeDescent E).IsTriangulated :=
    (Functor.isTriangulated_iff_comp_right t).mpr inferInstance
  let H := pointIntegralRationalFibre D l hl E ⋙
    (DerivedCategory.pointFiniteDimensional E).ι
  let : H.CommShift ℤ := by
    dsimp only [H, pointIntegralRationalFibre]
    infer_instance
  have : H.IsTriangulated := by
    dsimp only [H, pointIntegralRationalFibre]
    infer_instance
  let Q := sfRationalConstructibleLocalization l E (Spec (.of D.k))
  let F := pointRationalFibre D l hl E ⋙ (DerivedCategory.pointFiniteDimensional E).ι
  let W := Rationalization.W
    (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
    (sfIntegralConstructibleCategory l E (Spec (.of D.k)))
  have : Q.IsLocalization W := rawLocalization
    (Padic.coefficientExtensionIntegers l E)
    (sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (Padic.coefficientExtensionUniformizer l E)
  have ho (K) : F.obj (Q.obj K) = H.obj K :=
    congrArg ObjectProperty.FullSubcategory.obj
      ((pointRationalFibre_existsUnique D l hl E).exists.choose_spec.1 (Q.obj K))
  let c : Q ⋙ F ≅ H := NatIso.ofComponents (fun K ↦ eqToIso (ho K)) (by
    intro K M f
    change F.map (Q.map f) ≫ eqToHom (ho M) = eqToHom (ho K) ≫ H.map f
    have hh := (pointRationalFibre_existsUnique D l hl E).exists.choose_spec.2 K M f 1
    have hh' : HEq (F.map (Q.map f)) (H.map f) := by
      dsimp only [F, H, Q, Functor.comp_map, Functor.comp_obj, ObjectProperty.ι, inducedFunctor,
        pointRationalFibre, sfRationalConstructibleLocalization,
        ScalarLocalization.localization] at hh ⊢
      simpa only [map_one, one_smul] using hh
    exact eq_of_heq ((comp_eqToHom_heq _ _).trans
      (hh'.trans (eqToHom_comp_heq _ _).symm)))
  let : Localization.Lifting Q W H F := ⟨c⟩
  let cs : F.CommShift ℤ := Functor.commShiftOfLocalization Q W ℤ H F
  refine ⟨cs, ?_⟩
  have : NatTrans.CommShift c.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift (Localization.Lifting.iso Q W H F).hom ℤ)
  have : Q.mapArrow.EssSurj := Localization.essSurj_mapArrow Q W
  have : F.IsTriangulated := Functor.isTriangulated_of_precomp_iso c
  exact F.map_distinguished

end WeilConjectures
