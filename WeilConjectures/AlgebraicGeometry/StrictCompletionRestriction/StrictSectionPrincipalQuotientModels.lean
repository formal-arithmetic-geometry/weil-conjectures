/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionData
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictSectionQuotientTensorModels
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictSectionQuotientConeMaps
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus
import all WeilConjectures.Algebra.Homology.KFlatRoos.KFlatRoosRepresentativeInvariance
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.Algebra.Homology.RoosCoordinatesQuasiIso
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi

/-! # Principal quotient tensor models for strict section cones -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b w
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
open scoped CategoryTheory.Obj
open CategoryTheory.InternalAbelianSheafModule
open AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

-- Upstream's `HasDerivedCategory` instances on these module categories are found first and then
-- fail the final defeq check, which blocks `HasDerivedCategory.ofIsGrothendieckAbelian`.
attribute [-instance] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  AlgebraicGeometry.Scheme.ProjectionRestriction.derived
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOverModules

namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction
section RoosCoordinates
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
open CategoryTheory.RoosConeCalculus

@[irreducible] private def signedCoordinates (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (i : ℤ) :
    (roosF.obj N).X i ≅ (roosP N).X i ⊞ (roosP N).X (i - 1) where
  hom := biprod.lift (v N i) (-ucoord N i (i - 1) rfl)
  inv := fibrePair N i (i - 1) rfl biprod.fst (-biprod.snd)
  hom_inv_id := by
    apply roos_ext i <;> simp [Category.assoc, fibrePair_v, fibrePair_u]
  inv_hom_id := by
    apply biprod.hom_ext <;> simp [Category.assoc, fibrePair_v, fibrePair_u]

@[irreducible] private def coordinatesMap (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (V' L' : CochainComplex A ℤ) (s' : V' ⟶ V')
    (e' : ∀ i : ℤ, L'.X i ≅ V'.X i ⊞ V'.X (i - 1))
    (hd' : ∀ i : ℤ, L'.d i (i + 1) ≫ (e' (i + 1)).hom =
      (e' i).hom ≫ biprod.lift (biprod.fst ≫ V'.d i (i + 1))
        (biprod.fst ≫ s'.f i ≫
          eqToHom (congrArg V'.X (Int.add_sub_cancel i 1).symm) -
          biprod.snd ≫ V'.d (i - 1) ((i + 1) - 1)))
    (p : roosP N ⟶ V') (hs : roosU N ≫ p = p ≫ s') : roosF.obj N ⟶ L' :=
  CochainComplex.ofHom (fun i ↦ (signedCoordinates N i).hom ≫
    biprod.map (p.f i) (p.f (i - 1)) ≫ (e' i).inv) (by
      intro i
      apply (cancel_mono (e' (i + 1)).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hd', Iso.inv_hom_id_assoc]
      rw [← Category.assoc ((roosF.obj N).d i (i + 1)), signedCoordinates_d]
      simp only [Category.assoc]
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.map_fst_assoc, biprod.lift_fst,
          biprod.lift_fst_assoc, biprod.map_fst, p.comm]
      · have hi (j : ℤ) := congrArg (fun f ↦ f.f j) hs
        simp only [HomologicalComplex.comp_f] at hi
        simp only [Category.assoc, Preadditive.comp_sub, Preadditive.sub_comp,
          biprod.map_fst_assoc, biprod.map_snd_assoc, biprod.lift_snd,
          biprod.lift_snd_assoc, biprod.map_snd, HomologicalComplex.Hom.comm,
          Category.assoc]
        rw [← eqToHom_naturality (fun j ↦ p.f j) (Int.add_sub_cancel i 1).symm]
        rw [← Category.assoc ((roosU N).f i), hi i]
        simp only [Category.assoc])

end RoosCoordinates

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
