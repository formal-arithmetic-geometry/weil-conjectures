/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ClosedStructureTensorProjection
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # The ordinary complex projection formula for a closed structure sheaf

Source: Stacks Project, Modules, Tags 01AX and 08KS; More on Algebra, Tag 068G. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 512
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- Tensor with the pushed-forward structure sheaf is termwise pullback and pushforward.
Source: Stacks Project, Modules, Tags 01AX and 08KS; More on Algebra, Tag 068G. -/
theorem nonempty_closedStructure_tensor_complex_projection
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex (SheafOfModules.{u} Y.ringCatSheaf) ℤ) :
    letI : MonoidalCategory (SheafOfModules.{u} Y.ringCatSheaf) :=
      SheafOfModules.monoidalCategory Y.sheaf
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    Nonempty (CochainComplex.mapBifunctor P
      ((HomologicalComplex.single (SheafOfModules.{u} Y.ringCatSheaf) (.up ℤ) 0).obj B)
      (curriedTensor _) ≅
      ((Scheme.Modules.pushforward i).mapHomologicalComplex (.up ℤ)).obj T) := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  have : (Scheme.Modules.tensorPullback i ⋙ Scheme.Modules.pushforward i).Additive :=
    inferInstance
  obtain ⟨e⟩ := nonempty_closedStructure_tensor_projection i
  let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  exact ⟨CochainComplex.mapBifunctorSingle₂Iso
    (curriedTensor (SheafOfModules.{u} Y.ringCatSheaf)) B P ≪≫
    (NatIso.mapHomologicalComplex e (.up ℤ)).app P ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (Scheme.Modules.tensorPullback i ⋙ Scheme.Modules.pushforward i))
      (.up ℤ)).symm.app P⟩

end AlgebraicGeometry
