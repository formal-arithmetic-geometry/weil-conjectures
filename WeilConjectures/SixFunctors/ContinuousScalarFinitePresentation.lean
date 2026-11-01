/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
public import Mathlib.Algebra.Module.FinitePresentation
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import Mathlib.Algebra.Category.ModuleCat.Kernels
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars

/-!
# Finite presentations over continuous condensed coefficients

Finite presentations over the continuous coefficient ring are extensions of ordinary
finite scalar presentations. Only sections at the one-point profinite set enter.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale

namespace ContinuousScalarPresentation

open FiniteConstantModel
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [TopologicalSpace A] [IsTopologicalRing A] in
omit [TopologicalSpace A] [IsTopologicalRing A] in
attribute [local instance] scalarModules_full scalarModules_faithful

private abbrev B : Ab.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} A)
private abbrev F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
private abbrev H := (F.mapMod (B A)) ⋙ Mod.extendScalars (φ A)

private def regularIso : (H A).obj (Mod.regular (B A)) ≅ Mod.regular (Λ A) :=
  (Mod.extendScalars (φ A)).mapIso (Mod.isoMk (Iso.refl _) (by simp)) ≪≫
    Mod.regularExtensionIso (φ A)

private def freeIso (n : ℕ) : (H A).obj (Mod.finiteFree (B A) n) ≅
    Mod.finiteFree (Λ A) n :=
  (H A).mapBiproduct (fun _ : Fin n ↦ Mod.regular (B A)) ≪≫
    biproduct.mapIso (fun _ ↦ regularIso A)

private def continuousFreeIso (n : ℕ) :
    (continuousScalarFunctor A).obj (freeScalars A n) ≅ Mod.finiteFree (Λ A) n :=
  (H A).mapIso (scalarFiniteFreeIso A n) ≪≫ freeIso A n

attribute [local irreducible] regularIso freeIso continuousFreeIso

omit [TopologicalSpace A] [IsTopologicalRing A] in
omit [TopologicalSpace A] [IsTopologicalRing A] in
end ContinuousScalarPresentation

end AlgebraicGeometry.ProEtale
