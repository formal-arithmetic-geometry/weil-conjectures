/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitShift
import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitAssociativity
/-! # Pullback relative to canonical tensor shifts
Source: Stacks Project, Tag 08EU; parent representative construction step 2.
(blueprint: lem-sc-derived-pullback-canonical-tensor-shift-one).
-/
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
private theorem unit_shift_naturality (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {K N : schemeDerivedCategory X} (b : K ⟶ N) :
    (schemeCanonicalShiftUnitIso X K).hom ≫ b⟦(1 : ℤ)⟧' =
      ((𝟙_ (schemeDerivedCategory X))⟦(1 : ℤ)⟧) ◁ b ≫
        (schemeCanonicalShiftUnitIso X N).hom := by
  let := schemeCanonicalTensorShift X
  let : ∀ M : schemeDerivedCategory X, (tensorRight M).CommShift ℤ :=
    fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
  have : NatTrans.CommShift ((curriedTensor (schemeDerivedCategory X)).flip.map b) ℤ :=
    Functor.CommShift₂.commShift_flip_map (h := .int) b
  dsimp [schemeCanonicalShiftUnitIso]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← leftUnitor_naturality,
    Functor.map_comp]
  simpa only [Category.assoc, tensorRight, Functor.flip, curriedTensor] using
    congrArg (fun g ↦ g ≫ (shiftFunctor (schemeDerivedCategory X) (1 : ℤ)).map (λ_ N).hom)
      (NatTrans.shift_app_comm ((curriedTensor (schemeDerivedCategory X)).flip.map b)
        (1 : ℤ) (𝟙_ (schemeDerivedCategory X)))


private theorem unit_shift_tensor_inv (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K M : schemeDerivedCategory X) :
    let := schemeCanonicalTensorShift X
    let : (tensorRight M).CommShift ℤ :=
      Functor.CommShift₂.commShiftFlipObj (h := .int) M
    ((tensorRight M).commShiftIso (1 : ℤ)).hom.app K ≫
        (schemeCanonicalShiftUnitIso X (K ⊗ M)).inv =
      (schemeCanonicalShiftUnitIso X K).inv ▷ M ≫
        (α_ ((𝟙_ (schemeDerivedCategory X))⟦(1 : ℤ)⟧) K M).hom := by
  let := schemeCanonicalTensorShift X
  let : (tensorRight M).CommShift ℤ :=
    Functor.CommShift₂.commShiftFlipObj (h := .int) M
  apply (cancel_mono (schemeCanonicalShiftUnitIso X (K ⊗ M)).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    schemeCanonicalShiftUnitIso_tensor X K M]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
    Iso.inv_hom_id, id_whiskerRight, Category.id_comp]

private theorem tensor_unit_shift_square {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
      (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (K M : schemeDerivedCategory Y) :
    let := schemeCanonicalTensorShift Y
    let := schemeCanonicalTensorShift Z
    let : (tensorRight M).CommShift ℤ :=
      Functor.CommShift₂.commShiftFlipObj (h := .int) M
    let : (tensorRight ((derivedPullback f).obj M)).CommShift ℤ :=
      Functor.CommShift₂.commShiftFlipObj (h := .int) ((derivedPullback f).obj M)
    (derivedPullback f).map (((tensorRight M).commShiftIso (1 : ℤ)).hom.app K) ≫
        (derivedPullbackTensorUnitShiftIso f e (K ⊗ M)).hom ≫
        (Functor.OplaxMonoidal.δ (derivedPullback f) K M)⟦(1 : ℤ)⟧' =
      Functor.OplaxMonoidal.δ (derivedPullback f) (K⟦(1 : ℤ)⟧) M ≫
        (derivedPullbackTensorUnitShiftIso f e K).hom ▷ (derivedPullback f).obj M ≫
        ((tensorRight ((derivedPullback f).obj M)).commShiftIso
          (1 : ℤ)).hom.app ((derivedPullback f).obj K) := by
  let := schemeCanonicalTensorShift Y
  let := schemeCanonicalTensorShift Z
  let : (tensorRight M).CommShift ℤ :=
    Functor.CommShift₂.commShiftFlipObj (h := .int) M
  let : (tensorRight ((derivedPullback f).obj M)).CommShift ℤ :=
    Functor.CommShift₂.commShiftFlipObj (h := .int) ((derivedPullback f).obj M)
  dsimp only [derivedPullbackTensorUnitShiftIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom, tensorIso_hom, Iso.refl_hom]
  simp only [Category.assoc]
  rw [← (derivedPullback f).map_comp_assoc, unit_shift_tensor_inv]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [unit_shift_naturality Z (Functor.OplaxMonoidal.δ (derivedPullback f) K M)]
  simp only [tensorIso, Iso.refl_hom, tensorHom_def, whiskerLeft_id, Category.comp_id]
  rw [← whisker_exchange_assoc]
  rw [← Functor.OplaxMonoidal.associativity_assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
  rw [← associator_naturality_left_assoc]
  rw [schemeCanonicalShiftUnitIso_tensor Z ((derivedPullback f).obj K)
    ((derivedPullback f).obj M)]
  simp only [Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc]

/-- Pullback exact shift and its inverse-tensorator square relative to canonical tensor shifts.
Source: Stacks Tag 08EU, proof, with the translated-unit argument of the parent plan.
(blueprint: lem-sc-derived-pullback-canonical-tensor-shift-one).

Proof. Compute pullback on K-flat resolutions by termwise tensor pullback, which
preserves mapping-cone triangles. Identify translation with tensoring by the translated
unit using the Koszul comparison. Apply the supplied inverse tensorator and unit
isomorphism to transport this expression to the target. Iterate the degree-one
comparison and its inverse for all integers. Tensorator associativity gives addition
coherence and the unit equations give zero coherence. The mapping-cone comparison gives
exactness. Expand the inverse-tensorator square at shift one: both paths identify the
same translated tensor pullback, by tensorator associativity and the unit equations.
These equalities descend along the K-flat localization. Zero complexes and empty
schemes satisfy the same equations. Stacks supplies geometric exactness; transport
for the supplied monoidal structure is the agent expansion of the parent plan. -/
theorem derivedPullback_canonicalTensorShift_one
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    letI := schemeCanonicalTensorShift Y
    letI := schemeCanonicalTensorShift Z
    letI : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ :=
      fun M => Functor.CommShift₂.commShiftFlipObj (h := .int) M
    letI : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ :=
      fun M => Functor.CommShift₂.commShiftFlipObj (h := .int) M
    ∃ (sF : (derivedPullback f).CommShift ℤ),
      letI := sF
      (derivedPullback f).IsTriangulated ∧
      (∀ (M : schemeDerivedCategory Y)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ),
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := ((Functor.OplaxMonoidal.δNatTrans (derivedPullback f)).flipApp M)
        ((tensorRight M ⋙ derivedPullback f).commShiftIso (1 : ℤ)).hom.app K ≫
            (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫
            ((derivedPullback f ⋙ tensorRight ((derivedPullback f).obj M)).commShiftIso
              (1 : ℤ)).hom.app K) := by
  let := schemeCanonicalTensorShift Y
  let := schemeCanonicalTensorShift Z
  let : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ :=
    fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
  let : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ :=
    fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
  obtain ⟨sF, e, hF, hs⟩ := exists_derivedPullback_tensorUnitShift f
  let := sF
  refine ⟨sF, hF, ?_⟩
  intro M P _
  dsimp only
  simp only [Functor.commShiftIso_comp_hom_app, hs]
  simpa only [Category.assoc, Functor.OplaxMonoidal.δNatTrans, NatTrans.flipApp,
    Functor.comp_obj, tensorRight, curriedTensor, Functor.flip, flipFunctor,
    Functor.whiskeringLeft₂, Functor.whiskeringLeft, Functor.whiskeringRight] using
    tensor_unit_shift_square f e (DerivedCategory.Q.obj P) M

end AlgebraicGeometry
