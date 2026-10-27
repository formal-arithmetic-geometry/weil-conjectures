module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap
public import Mathlib.CategoryTheory.Subobject.Basic

/-! # Quasi-coherent ideals on algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tag 03MB
(blueprint: def-sfb-space-quasi-coherent-ideal).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- An ideal is an O_X-submodule of O_X; quasi-coherence is the existing module predicate.
Subobjects identify presentations by the unique isomorphism commuting with inclusion.
Source: Stacks Project, Morphisms of Spaces, Tag 03MB
(blueprint: def-sfb-space-quasi-coherent-ideal). -/
abbrev QuasiCoherentIdeal {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  {I : Subobject (SheafOfModules.unit X.structureSheaf) //
    (I : X.Modules).IsQuasicoherent}

/-- The canonical map h^* I → O_Y, adjoint to I → O_X → h_* O_Y.
This is the tensor map b ⊗ s ↦ b h^sharp(s), with the recorded adjunction's unit.
Source: Stacks Project, Morphisms of Spaces, Tag 03MB, factorization criterion
(blueprint: def-sfb-space-quasi-coherent-ideal). -/
def idealTensorMap {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (h : Y ⟶ X) (I : QuasiCoherentIdeal X) :
    (moduleTensorPullback h).obj (I.val : X.Modules) ⟶
      SheafOfModules.unit Y.structureSheaf :=
  ((moduleTensorAdjunction h).homEquiv _ _).symm (I.val.arrow ≫ moduleStructureMap h)

end AlgebraicGeometry.AlgebraicSpace
