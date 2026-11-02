/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.CondensedQcqsCompositionDefs
import WeilConjectures.Compactification.NagataCompactification

/-! Compatible compactification triangle for qcqs composition.
(blueprint: new-p3-qcqs-compatible-triangle)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
open CompactSupportComposition
variable (ℓ : ℕ)
def CompatibleTriangleData {X Z Y : Scheme.{u}} (h : X ⟶ Z) (g : Z ⟶ Y) : Prop :=
  Nonempty (Compactification.Triangle h g)

/-- Stacks Tag 0F7J supplies a compatible compactification triangle. -/
theorem qcqsCompatibleTriangleExists
    (D : WeilConjectures.FiniteFieldDatum.{u}) (_hℓ : ℓ ≠ D.p)
    {X₀ Z₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [QuasiSeparated Z₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (h₀ : X₀ ⟶ Z₀) (g₀ : Z₀ ⟶ Y₀)
    [IsSeparated h₀.left] [LocallyOfFiniteType h₀.left] [QuasiCompact h₀.left]
    [IsSeparated g₀.left] [LocallyOfFiniteType g₀.left] [QuasiCompact g₀.left] :
    CompatibleTriangleData (modelMap D h₀) (modelMap D g₀) := by
  let t := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  let : IsSeparated (modelMap D h₀) :=
    MorphismProperty.overPullbackMap (P := @IsSeparated) t h₀ inferInstance
  let : LocallyOfFiniteType (modelMap D h₀) :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) t h₀ inferInstance
  let : QuasiCompact (modelMap D h₀) :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) t h₀ inferInstance
  let : IsSeparated (modelMap D g₀) :=
    MorphismProperty.overPullbackMap (P := @IsSeparated) t g₀ inferInstance
  let : LocallyOfFiniteType (modelMap D g₀) :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) t g₀ inferInstance
  let : QuasiCompact (modelMap D g₀) :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) t g₀ inferInstance
  let : QuasiCompact ((Over.pullback t).obj Y₀).hom :=
    MorphismProperty.baseChange_obj (P := @QuasiCompact) t Y₀ inferInstance
  let : QuasiSeparated ((Over.pullback t).obj Y₀).hom :=
    MorphismProperty.baseChange_obj (P := @QuasiSeparated) t Y₀ inferInstance
  let : CompactSpace ((Over.pullback t).obj Y₀).left :=
    QuasiCompact.compactSpace_of_compactSpace ((Over.pullback t).obj Y₀).hom
  let : QuasiSeparatedSpace ((Over.pullback t).obj Y₀).left :=
    quasiSeparatedSpace_of_quasiSeparated ((Over.pullback t).obj Y₀).hom
  let := NagataCompactification (modelMap D g₀)
  let := NagataCompactification (modelMap D h₀ ≫ modelMap D g₀)
  exact ⟨Compactification.Triangle.ofHasCompactification _ _⟩
end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
