/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.TensorPullback

/-! # Localizing the actual kernel conormal

Source: Stacks Project, Tags 01R3 (1), 00A0 and 0096.
(blueprint: lem-sc-open-kernel-conormal-transport).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Restrict the actual kernel pullback to a chart where the morphism is closed.
Source: Stacks Project, Tags 01R3 (1), 00A0 and 0096.
(blueprint: lem-sc-open-kernel-conormal-transport).

Proof: The preimage equality identifies the square of g and its restriction i
with a Cartesian square of open immersions. Restriction of sheaves preserves
kernels. On every open T of W the two maps on functions are identified by the
open-section isomorphisms, so their kernels, including their inclusions, agree.
Since i is closed, its actual kernel is its quasi-coherent ideal module.
Thus restriction gives an isomorphism between the original kernel and this
ideal module, taking s to the unique t with the displayed inclusion equation.
Compose the two pullback adjunctions around the Cartesian square. The canonical
isomorphism of left adjoints identifies their units; using the explicit units
from exists_tensorPullbackAdjunction, both images of s are the sheafification
of 1 ⊗ s. Pullback along the open inclusions is restriction. Take sections,
identify sections on the open subschemes with sections on the ambient opens,
and restrict scalars through the displayed map. This gives e and the unit
identity. This construction does not require g to be globally closed or its
kernel to be globally quasi-coherent. Empty opens give the zero-module maps. -/
theorem open_kernel_conormal_transport {X Y : Scheme.{u}} (g : X ⟶ Y)
    (W : Y.Opens) (U : X.Opens) (h : U ≤ g ⁻¹ᵁ W) (hpre : g ⁻¹ᵁ W = U)
    [IsClosedImmersion (g.resLE W U h)] :
    let i := g.resLE W U h
    let K := kernel (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)
    let N := (tensorPullback g).obj K
    let C := (pushforward i).obj ((tensorPullback i).obj i.ker.toModules)
    letI : Module Γ(W.toScheme, ⊤) Γ(N, U) :=
      Module.compHom _ ((g.appLE W U h).hom.comp W.topIso.hom.hom)
    ∃ e : Γ(C, ⊤) ≃ₗ[Γ(W.toScheme, ⊤)] Γ(N, U),
      ∀ s : Γ(K, W), ∃ t : Γ(i.ker.toModules, ⊤),
        i.ker.toModulesι.app ⊤ t = W.topIso.inv
          ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            g.toRingCatSheafHom)).val.app (op W) s) ∧
        e (((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
          i.ker.toModules).app ⊤ t) = N.presheaf.map (homOfLE h).op
            (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app K).val.app
              (op W) s) := by sorry

end AlgebraicGeometry.Scheme.Modules
