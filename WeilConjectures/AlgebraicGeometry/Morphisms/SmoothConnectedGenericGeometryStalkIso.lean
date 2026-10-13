/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The integral generic fibre of a smooth morphism has the same function field
as its integral total space.

Source: Stacks Project, Tag 01UA; generic-fibre localization of the generic stalk.
(blueprint: lem-sbc-smooth-connected-generic-geometry-stalk-iso)

Proof: The spectrum of the base function field has dense image in S. Since c is
open, its inverse image is dense in C. The pullback range formula therefore
makes j dominant. Its image sends the generic point of Cη to that of C.
The map from the spectrum of a stalk is a preimmersion, and this property is
stable under base change, so j is a preimmersion. Its generic stalk map is
surjective. Both generic stalks are fields, so this map is also injective,
hence an isomorphism. Take the spectrum of that ring isomorphism. Naturality
of fromSpecStalk gives the required compatibility equation. -/
theorem smooth_connected_generic_geometry_stalk_iso {S C : Scheme.{u}} [IsIntegral S]
    [IsIntegral C] (c : C ⟶ S) [Smooth c]
    {Cη : Scheme.{u}} [IsIntegral Cη]
    (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c) :
    ∃ e : Spec C.functionField ≅ Spec Cη.functionField,
      (e.hom ≫ Cη.fromSpecStalk (genericPoint Cη)) ≫ j =
        C.fromSpecStalk (genericPoint C) := by
  have hd : Dense (Set.range (S.fromSpecStalk (genericPoint S))) := by
    have hg : Dense ({genericPoint S} : Set S) := by
      rw [dense_iff_closure_eq]
      exact (genericPoint_spec S).def
    exact hg.mono (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨IsLocalRing.closedPoint _, S.fromSpecStalk_closedPoint⟩)
  have : IsDominant (pullback.fst c (S.fromSpecStalk (genericPoint S))) := by
    constructor
    change Dense (Set.range (pullback.fst c (S.fromSpecStalk (genericPoint S))))
    rw [Pullback.range_fst]
    exact hd.preimage c.isOpenMap
  have : IsDominant j := by
    rw [← hCη.flip.isoPullback_hom_fst]
    infer_instance
  have hj : j (genericPoint Cη) = genericPoint C := by
    apply ((genericPoint_spec C).eq _).symm
    have hi := (genericPoint_spec Cη).image j.continuous
    rwa [Set.image_univ, j.denseRange.closure_range] at hi
  have : IsPreimmersion j :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hCη inferInstance
  let φ : C.functionField ⟶ Cη.functionField :=
    (C.presheaf.stalkCongr (Inseparable.of_eq hj.symm)).hom ≫
      j.stalkMap (genericPoint Cη)
  have : IsIso φ := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨φ.hom.injective, ?_⟩
    exact (j.stalkMap_surjective _).comp
      (ConcreteCategory.bijective_of_isIso
        (C.presheaf.stalkCongr (Inseparable.of_eq hj.symm)).hom).surjective
  have hnat : Spec.map φ ≫ C.fromSpecStalk (genericPoint C) =
      Cη.fromSpecStalk (genericPoint Cη) ≫ j := by
    dsimp [φ]
    rw [Spec.map_comp, Category.assoc]
    rw [TopCat.Presheaf.stalkCongr_hom,
      SpecMap_stalkSpecializes_fromSpecStalk,
      SpecMap_stalkMap_fromSpecStalk]
  refine ⟨(asIso (Spec.map φ)).symm, ?_⟩
  rw [Category.assoc]
  exact (IsIso.inv_comp_eq (Spec.map φ)).mpr hnat.symm

end AlgebraicGeometry.Scheme
