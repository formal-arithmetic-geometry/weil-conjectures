/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.SixFunctors.Finite.Stalk
import Sheaf.AlgebraicGeometry.Curve.GenericPointedEtaleExtension

/-! # Cofinality of pointed étale neighbourhoods at the generic point

Source: Stacks Project, Tags 03Q1 and 02GH; the generic counit argument of
blueprint `lem-sc-affine-generic-second`, proof paragraph 3.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem exists_map_comp_eq_generic_baseChangeNbhd
    (D : Scheme.{u}) [IsIntegral D]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec D.functionField)
    {d : (pointSmallEtale s).fiber.Elements}
    {c : (pointSmallEtale (s ≫ D.fromSpecFunctionField)).fiber.Elements}
    (σ σ' : (Etale.baseChangeNbhd D.fromSpecFunctionField
      (s ≫ D.fromSpecFunctionField) ⟨s, rfl⟩).obj c ⟶ d) :
    ∃ (c' : (pointSmallEtale (s ≫ D.fromSpecFunctionField)).fiber.Elements) (τ : c' ⟶ c),
      (Etale.baseChangeNbhd D.fromSpecFunctionField
      (s ≫ D.fromSpecFunctionField) ⟨s, rfl⟩).map τ ≫ σ =
        (Etale.baseChangeNbhd D.fromSpecFunctionField
      (s ≫ D.fromSpecFunctionField) ⟨s, rfl⟩).map τ ≫ σ' := by
  have : IsPreimmersion D.fromSpecFunctionField :=
    inferInstanceAs (IsPreimmersion (D.fromSpecStalk (genericPoint D)))
  obtain ⟨V, v⟩ := c
  obtain ⟨W, w⟩ := d
  -- `p` is the marked point of `V ×_X Z`; both `σ` and `σ'` send it to the marked point of `W`
  set p : Spec (.of Ω) ⟶ pullback V.hom D.fromSpecFunctionField :=
    (Scheme.Hom.basePt D.fromSpecFunctionField ⟨V, v⟩ ⟨s, rfl⟩)
  have key : ∀ τ : (Etale.baseChangeNbhd D.fromSpecFunctionField
      (s ≫ D.fromSpecFunctionField) ⟨s, rfl⟩).obj ⟨V, v⟩ ⟶ ⟨W, w⟩,
      p ≫ τ.val.left = w.left := fun τ ↦ congrArg CategoryTheory.Over.Hom.left τ.property
  have hab : σ.val.left ≫ W.hom = σ'.val.left ≫ W.hom := by
    rw [CategoryTheory.Over.w, CategoryTheory.Over.w]
  have hpab : p ≫ σ.val.left = p ≫ σ'.val.left := by rw [key σ, key σ']
  have hvfst : p ≫ pullback.fst V.hom D.fromSpecFunctionField = v.left :=
    Scheme.Hom.basePt_fst D.fromSpecFunctionField ⟨V, v⟩ ⟨s, rfl⟩
  -- the agreement locus of `σ` and `σ'` is the trace of an open `V₀` of `V`
  obtain ⟨S, hS, hSU⟩ :=
    (pullback.fst V.hom D.fromSpecFunctionField).isEmbedding.isInducing.isOpen_iff.1
      (FormallyUnramified.eqLocus W.hom σ.val.left σ'.val.left hab).2
  set V₀ : V.left.Opens := ⟨S, hS⟩
  -- `V₀` contains the marked point of `V`, which is the image of `p`
  have hVrange : Set.range v.left.base ⊆ Set.range V₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx := FormallyUnramified.range_subset_eqLocus W.hom σ.val.left σ'.val.left hab p hpab
      (Set.mem_range_self x)
    have hx' : (pullback.fst V.hom D.fromSpecFunctionField).base (p.base x) ∈ S := by
      rwa [← Set.mem_preimage, hSU]
    rw [← hvfst]
    exact hx'
  set v₀ := IsOpenImmersion.lift V₀.ι v.left hVrange
  have hv₀ι : v₀ ≫ V₀.ι = v.left := IsOpenImmersion.lift_fac _ _ _
  set θ : Scheme.Etale.mk (V₀.ι ≫ V.hom) ⟶ V :=
    MorphismProperty.Over.homMk V₀.ι rfl with hθ
  have hmfst : (D.fromSpecFunctionField.Etale.map θ).left ≫
      pullback.fst V.hom D.fromSpecFunctionField =
      pullback.fst (Scheme.Etale.mk (V₀.ι ≫ V.hom )).hom D.fromSpecFunctionField ≫ V₀.ι := by
    simp [Scheme.Hom.Etale, hθ]
  refine ⟨⟨Scheme.Etale.mk (V₀.ι ≫ V.hom), CategoryTheory.Over.homMk v₀ ?_⟩,
    CategoryOfElements.homMk _ _ θ ?_, ?_⟩
  · change v₀ ≫ V₀.ι ≫ V.hom = s ≫ D.fromSpecFunctionField
    rw [← Category.assoc, hv₀ι]
    exact CategoryTheory.Over.w v
  · exact CategoryTheory.Over.OverMorphism.ext hv₀ι
  · -- `V₀ ×_X Z` lands in the agreement locus, so `σ` and `σ'` agree on it
    have hmr : Set.range (D.fromSpecFunctionField.Etale.map θ).left.base ⊆
        Set.range (FormallyUnramified.eqLocus W.hom σ.val.left σ'.val.left hab).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      have h₁ : (pullback.fst V.hom D.fromSpecFunctionField)
          ((D.fromSpecFunctionField.Etale.map θ).left x) =
          V₀.ι ((pullback.fst (Scheme.Etale.mk (V₀.ι ≫ V.hom )).hom D.fromSpecFunctionField) x) :=
        congrArg (fun m ↦ m.base x) hmfst
      have hmem : (D.fromSpecFunctionField.Etale.map θ).left.base x ∈
          ⇑(pullback.fst V.hom D.fromSpecFunctionField) ⁻¹' S := by
        change (pullback.fst V.hom D.fromSpecFunctionField)
          ((D.fromSpecFunctionField.Etale.map θ).left x) ∈ S
        rw [h₁]
        exact (Scheme.Opens.range_ι V₀).subset (Set.mem_range_self _)
      rwa [hSU] at hmem
    refine Subtype.ext (MorphismProperty.Over.Hom.ext ?_)
    change (D.fromSpecFunctionField.Etale.map θ).left ≫ σ.val.left =
      (D.fromSpecFunctionField.Etale.map θ).left ≫ σ'.val.left
    rw [← IsOpenImmersion.lift_fac
      (FormallyUnramified.eqLocus W.hom σ.val.left σ'.val.left hab).ι _ hmr,
      Category.assoc, Category.assoc, FormallyUnramified.eqLocus_ι_comp_eq]


/-- Base change to the function field is initial on pointed étale neighbourhoods.

Source: Stacks Project, Tags 03Q1 (stalks) and 02GH (standard étale presentations);
blueprint `lem-sc-affine-generic-second`, proof paragraph 3.
(blueprint: lem-sc-generic-pointed-etale-cofinality)

Proof: The categories of pointed étale neighbourhoods are cofiltered. For a pointed
étale neighbourhood W of s over K, first restrict to an affine standard étale
neighbourhood of its marked point. Choose a nonempty affine open Spec A of D.
Its fraction field is K. A standard étale presentation over K involves finitely
many coefficients and equations. Clearing their denominators gives, after
localizing A at a nonzero element, a standard étale A-algebra whose generic fibre
is that neighbourhood of W. Compose its spectrum with this open immersion into D.
The marked K-point lifts to the resulting base change, and composing it with the
projection supplies the marked point over D. Thus every W receives a morphism
from a base-changed pointed neighbourhood.

For two pointed morphisms from the same base-changed neighbourhood V_K to W,
their agreement locus is open in V_K, because W is unramified over K, and contains
the marked point. The generic-point morphism is a preimmersion, as is its base
change V_K -> V. Its underlying map is inducing, so that this agreement locus is
the inverse image of an open V₀ of V. Restrict V to V₀. The marking factors through
V₀, and the base change of V₀ maps into the agreement locus, equalizing the two
morphisms. Apply the initiality criterion for cofiltered categories to the
extension theorem and this equalization. -/
theorem initial_generic_baseChangeNbhd
    (D : Scheme.{u}) [IsIntegral D]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec D.functionField) :
    (Etale.baseChangeNbhd D.fromSpecFunctionField
      (s ≫ D.fromSpecFunctionField) ⟨s, rfl⟩).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · exact exists_hom_generic_baseChangeNbhd D s
  · intro d c σ σ'
    exact exists_map_comp_eq_generic_baseChangeNbhd D s σ σ'


end AlgebraicGeometry.Scheme
