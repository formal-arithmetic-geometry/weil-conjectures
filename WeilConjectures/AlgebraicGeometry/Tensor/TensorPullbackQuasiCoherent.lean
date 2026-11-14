/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Quasi-coherence of the tensor-formula pullback

Source: Stacks Project, Modules on Schemes, Tag 01BG.
-/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false

/-- The canonical comparison of tensor pullback with ordinary module pullback.
It is the unique comparison of left adjoints determined by their specified units.
Source: Stacks Project, Modules, Tag 01BG. -/
noncomputable def tensorOrdinaryPullbackIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    tensorPullback g ≅ pullback g :=
  (Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (pullbackPushforwardAdjunction g)

/-- Tensor pullback preserves quasi-coherent modules.
Source: Stacks Project, Modules on Schemes, Tag 01BG. -/
@[instance]
theorem isQuasicoherent_tensorPullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (F : Y.Modules) [F.IsQuasicoherent] : ((tensorPullback g).obj F).IsQuasicoherent := by
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((tensorOrdinaryPullbackIso g).app F).symm (isQuasicoherent_pullback g F)

end AlgebraicGeometry.Scheme.Modules
