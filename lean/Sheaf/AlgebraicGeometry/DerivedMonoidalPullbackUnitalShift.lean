/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShiftKFlatOne
import Sheaf.Algebra.Homology.KFlatResolution

/-! # Exact shifts compatible with a specified derived monoidal pullback

Source: Stacks Project, Tags 0A9U and 0A9S, equation-compare-with-pullback.
(blueprint: lem-sc-derived-monoidal-pullback-unital-shift).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

-- Cancel the b-comparison from the (a + b)-square, then use faithfulness of shift by b.
private theorem core_of_add
    {C : Type*} {D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    (a b : ℤ) (hb : NatTrans.CommShiftCore τ b)
    (hab : NatTrans.CommShiftCore τ (a + b)) : NatTrans.CommShiftCore τ a := by
  constructor
  ext X
  apply (shiftFunctor D b).map_injective
  have h := hab.shift_app_comm τ X
  simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
    Functor.comp_obj] at h
  have hD := (shiftFunctorAdd D a b).inv.naturality (τ.app X)
  have hC := τ.naturality ((shiftFunctorAdd C a b).hom.app X)
  dsimp at hD hC
  simp only [Category.assoc] at h ⊢
  rw [← hD] at h
  rw [← reassoc_of% hC] at h
  rw [← hb.shift_app_comm_assoc τ] at h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp]
  have h := (cancel_epi (F.map ((shiftFunctorAdd C a b).hom.app X))).1 h
  have h := (cancel_epi ((F.commShiftIso b).hom.app (X⟦a⟧))).1 h
  apply (cancel_mono ((shiftFunctorAdd D a b).inv.app (G.obj X))).1
  simpa only [Category.assoc] using h

-- The zero square and cancellation give -1; addition then covers every integer.
private theorem shift_of_one
    {C : Type*} {D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    (h : NatTrans.CommShiftCore τ (1 : ℤ)) : NatTrans.CommShift τ ℤ := by
  apply NatTrans.CommShift.of_core
  have hn : NatTrans.CommShiftCore τ (-1 : ℤ) :=
    core_of_add τ (-1) 1 h (by simpa using (NatTrans.CommShiftCore.zero ℤ))
  intro n
  induction n using Int.induction_on with
  | zero => exact NatTrans.CommShiftCore.zero ℤ
  | succ n ih => exact ih.add h
  | pred n ih => simpa only [sub_eq_add_neg] using ih.add hn

-- The two sides are natural transformations, so equality transports across an isomorphism.
private theorem core_of_iso_representatives
    {C : Type*} {D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    {ι : Type*} (obj : ι → C) (S : ι → Prop)
    (hS : ∀ X, ∃ P, S P ∧ Nonempty (obj P ≅ X))
    (h : ∀ P, S P →
      (F.commShiftIso (1 : ℤ)).hom.app (obj P) ≫ (τ.app (obj P))⟦(1 : ℤ)⟧' =
        τ.app ((obj P)⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app (obj P)) :
    NatTrans.CommShiftCore τ (1 : ℤ) := by
  constructor
  let α := (F.commShiftIso (1 : ℤ)).hom ≫
    Functor.whiskerRight τ (shiftFunctor D (1 : ℤ))
  let β := Functor.whiskerLeft (shiftFunctor C (1 : ℤ)) τ ≫
    (G.commShiftIso (1 : ℤ)).hom
  change α = β
  ext X
  obtain ⟨P, hP, ⟨e⟩⟩ := hS X
  rw [← cancel_epi ((shiftFunctor C (1 : ℤ) ⋙ F).map e.hom),
    α.naturality, β.naturality]
  congr 1
  exact h P hP

-- Localization inverts a K-flat resolution of a complex representing the derived object.
private theorem exists_kFlat_derived_iso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K : schemeDerivedCategory X) :
    ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsKFlat (R := X.sheaf) P ∧ Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) (DerivedCategory.Q.objPreimage K)
  have : QuasiIso s := hs
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩⟩


/-- Simultaneous exact tensor and pullback shifts, natural in the fixed tensor
factor on both schemes and compatible with the right unitor on the base.
Source: Stacks Project, Tags 0A9U and 0A9S, equation-compare-with-pullback;
representative-complex step 1 of lem-sc-pinned-projection-counit-exact-shift.
(blueprint: lem-sc-derived-monoidal-pullback-unital-shift).

Proof. Compute derived tensor and pullback on K-flat representatives. Translation
in the first tensor variable has the Koszul comparison, natural in the second
factor, and tensor of a cone is the cone of the tensor map. These comparisons
descend through localization, including their zero and addition identities, so
all tensorRight functors are exact and their maps commute with shifts on both
schemes. The complex right unitor identifies the translation comparison for
K tensor O_Y with translation of K, and this equation descends as well. Compute
pullback by termwise tensor pullback of K-flat resolutions: it takes cones to cones.
For the supplied strong monoidal structure, choose the pullback comparison
simultaneously with these tensor comparisons by expressing translation as tensor
with the translated unit, then applying its tensorator and unit isomorphism.
Associativity of the tensorator gives addition coherence, and its unit equations
give zero coherence and the right-unitor equation. The inverse tensorator then
commutes with translation in its varying first factor. The comparison identifies
the images of representative cone triangles, proving exactness for the chosen
pullback shift. Descend all equations through K-flat localization. No direct
image, adjunction, projection isomorphism, or map to the unit is used. Zero tensor
factors, empty schemes and translation by zero satisfy the same unit equations. -/
theorem exists_derivedMonoidalPullback_unitalShift
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ (sL : (derivedPullback f).CommShift ℤ)
      (sY : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ)
      (sZ : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ),
      letI := sL
      letI := sY
      letI := sZ
      (derivedPullback f).IsTriangulated ∧
      (∀ M : schemeDerivedCategory Z, (tensorRight M).IsTriangulated) ∧
      (∀ {M N : schemeDerivedCategory Y} (b : M ⟶ N),
        NatTrans.CommShift ((curriedTensor (schemeDerivedCategory Y)).flip.map b) ℤ) ∧
      (∀ {M N : schemeDerivedCategory Z} (b : M ⟶ N),
        NatTrans.CommShift ((curriedTensor (schemeDerivedCategory Z)).flip.map b) ℤ) ∧
      (∀ M : schemeDerivedCategory Y,
        NatTrans.CommShift (F₁ := tensorRight M ⋙ derivedPullback f)
          (F₂ := derivedPullback f ⋙ tensorRight ((derivedPullback f).obj M))
          ((Functor.OplaxMonoidal.δNatTrans (derivedPullback f)).flipApp M) ℤ) ∧
      NatTrans.CommShift (rightUnitorNatIso (schemeDerivedCategory Y)).hom ℤ := by
  obtain ⟨sL, sY, sZ, hL, hZ, hmapY, hmapZ, hδ, hρ⟩ :=
    derivedMonoidalPullback_unitalShift_kFlat_one f
  let := sL
  let := sY
  let := sZ
  refine ⟨sL, sY, sZ, hL, hZ, ?_, ?_, ?_, ?_⟩
  · intro M N b
    apply shift_of_one
    exact core_of_iso_representatives _ DerivedCategory.Q.obj
      (CochainComplex.IsKFlat (R := Y.sheaf)) (exists_kFlat_derived_iso Y) (hmapY b)
  · intro M N b
    apply shift_of_one
    exact core_of_iso_representatives _ DerivedCategory.Q.obj
      (CochainComplex.IsKFlat (R := Z.sheaf)) (exists_kFlat_derived_iso Z) (hmapZ b)
  · intro M
    apply shift_of_one
    exact core_of_iso_representatives _ DerivedCategory.Q.obj
      (CochainComplex.IsKFlat (R := Y.sheaf)) (exists_kFlat_derived_iso Y) (hδ M)
  · apply shift_of_one
    exact core_of_iso_representatives _ DerivedCategory.Q.obj
      (CochainComplex.IsKFlat (R := Y.sheaf)) (exists_kFlat_derived_iso Y) hρ


end AlgebraicGeometry
