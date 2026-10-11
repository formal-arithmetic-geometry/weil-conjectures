/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading.Datum

/-!
# The normalization of `C` in the Galois cover over the generic fibre

In the situation of the spreading theorem (blueprint `sbc-thm-spreading-finite-etale-galois`),
the relative normalization of `C` in `ν : Z.P ⟶ C_η ⟶ C` restricts to `Z.P` over the generic
fibre `C_η`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.SpreadingDatum

variable {G : Type (u + 1)} [Group G] [Finite G] (D : SpreadingDatum G)

/-- Step of the proof of blueprint `sbc-thm-spreading-finite-etale-galois`: the relative
normalization `N ⟶ C` of `C` in `ν : Z.P ⟶ C` restricts to `Z.P ⟶ C_η` over the generic fibre,
that is, the square formed by `ν.toNormalization`, `Z.π`, `ν.fromNormalization` and `j` is
cartesian.

Proof sketch: relative normalization commutes with localization (as in the proof of
[Stacks 03GV] for smooth base change, `AlgebraicGeometry.Scheme.Hom.normalizationPullback`, with
`TensorProduct.toIntegralClosure_bijective_of_smooth` replaced by the fact that integral closure
commutes with localization). Over affine opens `Spec A ⊆ S` and `Spec B ⊆ c⁻¹(Spec A)`, the
generic fibre is `Spec (B ⊗_A K) = Spec (B_{A∖0})`, `Z.P` is `Spec D` for a finite étale
`B_{A∖0}`-algebra `D`, and the normalization is `Spec B'` with `B'` the integral closure of `B`
in `D`. Then `B' ⊗_B B_{A∖0} = B'_{A∖0}` is the integral closure of `B_{A∖0}` in `D`, which is
`D` since `D` is integral over `B_{A∖0}`. Finally `j` is a monomorphism, so
`Z.P ×_C C_η = Z.P`. -/
theorem isPullback_toNormalization :
    IsPullback D.ν.toNormalization D.Z.π D.ν.fromNormalization D.j :=
  sorry

end AlgebraicGeometry.Scheme.SpreadingDatum
