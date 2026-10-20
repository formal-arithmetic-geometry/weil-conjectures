/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
import Sheaf.AlgebraicGeometry.DerivedBaseChangeOpenUnit
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeNaturality
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeOpenRestriction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive


/-! # Unit and restriction squares for relative Mayer--Vietoris base change

Source: Stacks Project, Tags 08BV, 08HY and 0DJ9
(blueprint: lem-pc-rf-mv-base-change-first-two-squares).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem biprod_unit_square
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ E) (G : D ⥤ E) [F.Additive] [G.Additive]
    {A B Z : C} {A' B' Z' : D}
    [HasBinaryBiproduct A B] [HasBinaryBiproduct A' B']
    (u : Z ⟶ A) (v : Z ⟶ B) (u' : Z' ⟶ A') (v' : Z' ⟶ B')
    (a₀ : F.obj Z ⟶ G.obj Z') (a : F.obj A ⟶ G.obj A') (b : F.obj B ⟶ G.obj B')
    (hu : F.map u ≫ a = a₀ ≫ G.map u') (hv : F.map v ≫ b = a₀ ≫ G.map v') :
    F.map (biprod.lift u v) ≫
        (F.map biprod.fst ≫ a ≫ G.map biprod.inl +
          F.map biprod.snd ≫ b ≫ G.map biprod.inr) =
      a₀ ≫ G.map (biprod.lift u' v') := by
  simp only [Preadditive.comp_add, ← Category.assoc, ← F.map_comp,
    biprod.lift_fst, biprod.lift_snd, hu, hv]
  simp only [Category.assoc, ← Preadditive.comp_add, ← G.map_comp,
    ← G.map_add, ← biprod.lift_eq]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem biprod_restriction_square
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ E) (G : D ⥤ E) [F.Additive] [G.Additive]
    {A B Z : C} {A' B' Z' : D}
    [HasBinaryBiproduct A B] [HasBinaryBiproduct A' B']
    (r : A ⟶ Z) (s : B ⟶ Z) (r' : A' ⟶ Z') (s' : B' ⟶ Z')
    (a : F.obj A ⟶ G.obj A') (b : F.obj B ⟶ G.obj B') (c : F.obj Z ⟶ G.obj Z')
    (hr : F.map r ≫ c = a ≫ G.map r') (hs : F.map s ≫ c = b ≫ G.map s') :
    F.map (biprod.desc r (-s)) ≫ c =
      (F.map biprod.fst ≫ a ≫ G.map biprod.inl +
        F.map biprod.snd ≫ b ≫ G.map biprod.inr) ≫
          G.map (biprod.desc r' (-s')) := by
  have hr₁ := congrArg (fun k ↦ F.map (biprod.fst : A ⊞ B ⟶ A) ≫ k) hr
  have hs₁ := congrArg (fun k ↦ F.map (biprod.snd : A ⊞ B ⟶ B) ≫ k) hs
  simp only [biprod.desc_eq, Functor.map_add, Functor.map_comp, Functor.map_neg,
    Preadditive.add_comp, Preadditive.comp_add, Preadditive.neg_comp,
    Preadditive.comp_neg, Category.assoc]
  rw [hr₁, hs₁]
  simp only [← G.map_comp, biprod.inl_fst_assoc, biprod.inl_snd_assoc,
    biprod.inr_fst_assoc, biprod.inr_snd_assoc, Functor.map_zero,
    zero_comp, comp_zero, add_zero, zero_add]

private theorem mvBaseChangeOpenMap_unit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (ψ : (derivedPullback g').obj K ⟶ K') (U : X.Opens) :
    (schemeDerivedDirectImage f ⋙ derivedPullback g).map
        ((mvOpenRestrictionAdjunction X U).unit.app K) ≫
      mvBaseChangeOpenMap f f' g g' h K K' ψ U =
    (schemeDerivedBaseChangeMap f f' g g' h K ≫
      (schemeDerivedDirectImage f').map ψ) ≫
        (schemeDerivedDirectImage f').map
          ((mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U)).unit.app K')  := by
  dsimp only [mvBaseChangeOpenMap]
  have hn := schemeDerivedBaseChangeMap_naturality f f' g g' h
    ((mvOpenRestrictionAdjunction X U).unit.app K)
  dsimp only [Functor.id_obj, Functor.comp_obj] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [mvOpenBaseChange_unit]


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The unit and difference-of-restrictions squares commute for the canonical
open adjunctions and the constructed pullback/restriction comparisons. No
boundary or triangle morphism is asserted.
Source: Stacks Project, Tags 08HY and 0DJ9, induction step, using Tag 0D5S
(blueprint: lem-pc-rf-mv-base-change-first-two-squares).
Proof:
1. The local open base-change mate respects the exact-open adjunction units:
   transpose the equality, use naturality and the triangle identities, and
   transport along left-adjoint uniqueness. Naturality of the whole-space
   base-change map then proves the unit square for each open.
2. Apply the unit square to U and V. Distribute composition over the diagonal
   component sum, cancel biproduct projections against the lift, and reassemble
   the target lift using additivity. This proves the first square.
3. Nested-open restriction sends the larger-open unit to the smaller-open unit.
   Restriction to the smaller inverse-image open inverts the pulled-back
   larger-open unit: open restriction has a fully faithful right adjoint,
   and composition and pullback/restriction isomorphisms preserve this fact.
   Precomposition with that unit is injective on maps into the smaller-open
   right adjoint. The local restriction square therefore follows from the
   local unit squares. Naturality of whole-space base change gives the full
   restriction square.
4. Apply the restriction square to U intersect V contained in U and in V.
   Expand the two biproduct desc maps as projection sums, distribute and map
   their negatives, and use the inclusion/projection identities. Additivity
   assembles the difference square. No connecting morphism is used. -/
theorem derivedBaseChange_mayerVietoris_firstTwoSquares
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    (hsq : IsPullback g' f' f g)
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hUV : IsCompact ((U ⊓ V : X.Opens) : Set X)) (hcover : U ⊔ V = ⊤)
:
    ∀ (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X'),
      schemeDerivedQCohProperty X K → schemeDerivedQCohProperty X' K' →
      ∀ ψ : (derivedPullback g').obj K ⟶ K',
    let adjU := mvOpenRestrictionAdjunction X U
    let adjV := mvOpenRestrictionAdjunction X V
    let adjUV := mvOpenRestrictionAdjunction X (U ⊓ V)
    let adjU' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U)
    let adjV' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ V)
    let adjUV' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ (U ⊓ V))
    let F := schemeDerivedDirectImage f ⋙ derivedPullback g
    let G := schemeDerivedDirectImage f'
    let a₀ := schemeDerivedBaseChangeMap f f' g g' hsq.w K ≫ G.map ψ
    let a₂ := mvBaseChangeMiddle f f' g g' hsq.w K K' ψ U V
    let a₃ := mvBaseChangeOpenMap f f' g g' hsq.w K K' ψ (U ⊓ V)
    let T := mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
        (homOfLE inf_le_right) adjU adjV adjUV K 0
    let T' := mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
        ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
        ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
        adjU' adjV' adjUV' K' 0
    F.map T.mor₁ ≫ a₂ = a₀ ≫ G.map T'.mor₁ ∧
    F.map T.mor₂ ≫ a₃ = a₂ ≫ G.map T'.mor₂  := by
  intro K K' hK hK' ψ
  have _ := hU
  have _ := hV
  have _ := hUV
  have _ := hcover
  let : Preadditive (schemeDerivedCategory X) := inferInstance
  let : Preadditive (schemeDerivedCategory X') := inferInstance
  let : Preadditive (schemeDerivedCategory S') := inferInstance
  let : HasFiniteBiproducts (schemeDerivedCategory X) := inferInstance
  let : HasFiniteBiproducts (schemeDerivedCategory X') := inferInstance
  let : (derivedPullback g).Additive :=
    (mvDerivedPullbackAdjunction g).left_adjoint_additive
  dsimp only
  constructor
  · exact biprod_unit_square _ _ _ _ _ _ _ _ _
      (mvBaseChangeOpenMap_unit f f' g g' hsq.w K K' ψ U)
      (mvBaseChangeOpenMap_unit f f' g g' hsq.w K K' ψ V)
  · exact biprod_restriction_square _ _ _ _ _ _ _ _ _
      (mvBaseChangeOpenMap_restriction f f' g g' hsq.w K K' ψ (homOfLE inf_le_left))
      (mvBaseChangeOpenMap_restriction f f' g g' hsq.w K K' ψ (homOfLE inf_le_right))

end AlgebraicGeometry
