/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-!
# Pullback of associated modules on affine schemes

Source: Stacks Project, Schemes, Tag 01I9 (1), using Tags 01I7 and 01BJ
(blueprint: lem-weil-pbc-tilde-pullback-base-change).
-/

universe u

open CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pullback of `M` tilde along `Spec φ` is naturally the tilde of `S ⊗[R] M`.
The comparison takes the pullback-unit image of the canonical section of `m` to
that of `1 ⊗ m`. The unit is the canonical tensor-formula adjunction unit.
Source: Stacks Project, Schemes, Tag 01I9 (1), Tags 01I7 and 01BJ
(blueprint: lem-weil-pbc-tilde-pullback-base-change).
Proof, following the node's three steps:
1. Identify the section rings of the spectra with R and S, and their induced map with φ
   (def-weil-affine-spectrum). Tag 01I7 identifies tilde M naturally with the associated
   module sheaf, carrying its canonical sections to tilde.toOpen
   (lem-weil-pbc-affine-tilde-gamma-adjunction).
2. Tag 01BJ identifies the tensor pullback of this associated sheaf with the associated
   sheaf of S tensor_R M (lem-weil-pbc-associated-module-pullback). Apply Tag 01I7 over S
   and compose. Both comparisons are natural in M, so their composite is a natural iso.
3. In the one-point-ringed-space construction of Tag 01BJ, pullback composition takes the
   unit image of m to 1 tensor m. The comparisons of Tag 01I7 take canonical sections to
   tilde.toOpen, giving the displayed equality (def-pc-module-pullback). -/
theorem exists_tensorPullback_tilde_iso {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    ∃ θ : tilde.functor R ⋙ tensorPullback (Spec.map φ) ≅
        ModuleCat.extendScalars φ.hom ⋙ tilde.functor S,
      ∀ (M : ModuleCat.{u} R) (m : M),
        (θ.hom.app M).app ⊤
          (((Classical.choose (exists_tensorPullbackAdjunction (Spec.map φ))).unit.app
            (tilde M)).app ⊤ (tilde.toOpen M ⊤ m)) =
          tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤
            ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M m) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
