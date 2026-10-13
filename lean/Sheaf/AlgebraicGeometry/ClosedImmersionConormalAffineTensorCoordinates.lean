/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Cotangent
import Sheaf.AlgebraicGeometry.AffineConormalSections
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-! # Tensor coordinates before the second module pullback

Source: Stacks Project, Morphisms, Tags 0473 and 01R3 (2); Schemes, Tag 01JU (1).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ambient tensor of cotangent classes identifies with the tensor of conormal
sections over the source chart rings. This concerns only the tensor modules, before
applying the section map of the second module pullback.

Source: Stacks Project, Morphisms, Tags 0473 and 01R3 (2); Schemes, Tag 01JU (1).
(blueprint: lem-weil-pbc-closed-immersion-conormal-affine-tensor-coordinates).

Proof: Put A = Γ(X',U'), B = Γ(X,U), J = i'.ker.ideal U',
C = Γ(Z',i'⁻¹U'), and D = Γ(Z,i⁻¹U). Closed immersions make both inverse-image
opens affine and the maps A → C and B → D surjective. The cartesian square gives
ker(B → D) = J.map(A → B), using the pullback projection kernel formula and the
affine ideal-comap formula. Thus C = A/J and D = B/JB, compatibly with C → D.
The affine conormal equivalence identifies N = Γ(i'*i'.ker,i'⁻¹U') with J/J²;
it sends class(a) to the unit on the ideal section representing a and is C-linear,
since it is A-linear and A → C is surjective. Since J annihilates J/J², scalar
cancellation identifies N ⊗[C] D with N ⊗[A] D. The quotient tensor formula
identifies the latter with (B ⊗[A] J/J²)/(JB • ⊤), after swapping factors.
The denominator is zero: g(a) • (b ⊗ m) = b ⊗ (a • m) = 0 for a ∈ J;
linearity extends this from ideal generators and pure tensors. Remove the zero
quotient and compose the equivalences. Their pure-tensor formulas send b ⊗ class(a)
to unit(s') ⊗ i.app(b), proving the normalization. This also covers J = 0, J = A,
and zero chart rings, without a flatness hypothesis. -/
theorem closedImmersion_conormal_affine_tensor_coordinates
    {X Z X' Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')
    (hc : IsLimit (PullbackCone.mk i f h))
    (U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1) :
    letI : Algebra Γ(X', U'.1) Γ(X, U.1) := (g.appLE U'.1 U.1 H).hom.toAlgebra
    let V' : Z'.affineOpens := ⟨i' ⁻¹ᵁ U'.1, U'.2.preimage i'⟩
    let V : Z.affineOpens := ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
    let K : V.1 ≤ f ⁻¹ᵁ V'.1 := by
      change i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ i' ⁻¹ᵁ U'.1
      rw [← Scheme.Hom.comp_preimage, ← h, Scheme.Hom.comp_preimage]
      exact i.preimage_mono H
    letI : Algebra Γ(Z', V'.1) Γ(Z, V.1) := (f.appLE V'.1 V.1 K).hom.toAlgebra
    ∃ e : (Γ(X, U.1) ⊗[Γ(X', U'.1)] (i'.ker.ideal U').Cotangent) ≃+
        (Γ((tensorPullback i').obj i'.ker.toModules, V'.1) ⊗[Γ(Z', V'.1)] Γ(Z, V.1)),
      ∀ (b : Γ(X, U.1)) (a : i'.ker.ideal U') (s' : Γ(i'.ker.toModules, U'.1)),
        i'.ker.toModulesι.app U'.1 s' = (a : Γ(X', U'.1)) →
        e (b ⊗ₜ[Γ(X', U'.1)] (i'.ker.ideal U').toCotangent a) =
          (show Γ((tensorPullback i').obj i'.ker.toModules, V'.1) from
            ((Classical.choose (exists_tensorPullbackAdjunction i')).unit.app
              i'.ker.toModules).app U'.1 s') ⊗ₜ[Γ(Z', V'.1)] i.app U.1 b := by sorry

end AlgebraicGeometry.Scheme.Modules
