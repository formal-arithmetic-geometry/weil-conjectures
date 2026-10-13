/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk
import Sheaf.AlgebraicGeometry.ClosedPushforwardStalks

/-! # The local calculation for the closed structure tensor projection
Source: Stacks Project, Tags 08KS, 01CB and 0098.
(blueprint: new-closed-structure-tensor-projection-stalk). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry
open Scheme.Modules

/-- The stalk of a module map with the specified section-pairing formula is invertible.
Source: Stacks Project, Tags 08KS, 01CB, 0098, and Sheaves Tag 007T.
(blueprint: new-closed-structure-tensor-projection-stalk).

Proof: At a point i(z), the tensor-stalk comparison identifies the source with
M_i(z) tensor over O_Y,i(z) O_Z,z. The closed-pushforward and tensor-pullback
comparisons identify the target with O_Z,z tensor over O_Y,i(z) M_i(z).
The canonical pullback unit has germ 1 tensor m. Taking germs in the given
section formula therefore sends m tensor r to r tensor m. Represent the two
germs on a common neighbourhood, using the closed-embedding cofinality for r;
pure tensors generate, so the stalk map is scalar-extension symmetry and is
bijective. At a point outside the closed image, both pushforward stalks vanish:
restrict to the open complement. Tensor-stalk comparison makes the source
zero as well. The unique map between zero abelian groups is invertible.
The identity immersion gives tensor symmetry followed by the scalar unitor;
the empty source and the zero module give the zero-group case. -/
theorem closedStructure_projection_stalk_isIso
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (M : Y.Modules)
    (α : M ⊗ (pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      (pushforward i).obj ((tensorPullback i).obj M))
    (hα : ∀ (U : Y.Opens) (s : Γ(M, U))
      (r : Γ((pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf), U)),
      α.app U (tmulSection s r) = (show Γ(Z, i ⁻¹ᵁ U) from r) •
        (show Γ((tensorPullback i).obj M, i ⁻¹ᵁ U) from
          ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app M).app U s))
    (x : Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α.mapPresheaf) := by
  sorry

end AlgebraicGeometry
