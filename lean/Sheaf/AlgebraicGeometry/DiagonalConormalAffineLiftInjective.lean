/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.DiagonalConormalDerivation
import Sheaf.AlgebraicGeometry.AffineConormalSectionsExistence
import Sheaf.AlgebraicGeometry.DiagonalConormal
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Injectivity of the affine diagonal conormal lift

Source: Stacks Project, Tag 08S2, affine calculation; Tags 01KJ, 01R3 and 00RW.
(blueprint: stage3-diagonal-conormal-affine-lift-injective).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}

/-- The lift of a normalized difference derivation has no kernel on an affine chart.
Source: Stacks Project, Tag 08S2, final affine calculation, and Algebra, Tag 00RW.
(blueprint: stage3-diagonal-conormal-affine-lift-injective).
Proof: put A = Γ(X,U), R = Γ(S,V), B = A ⊗[R] A and J = ker(B → A), where
B → A is multiplication. By Tag 01KJ the open U ×_V U is affine with ring B,
and the diagonal restricts to the closed immersion Spec A → Spec B. Restriction
of the actual sheaf-module kernel of O → Δ_* O to this open is the tilde module
of J: restriction preserves kernels and the closed-immersion pushforward is the
module of A with its B-action by multiplication. Tensor pullback and restriction
therefore identify the conormal over U with the tilde module of A ⊗[B] J.
The tensor-over-quotient calculation gives A ⊗[B] J = J/J². Its unit sends a
kernel section to its class modulo J², by Tag 01R3. For each a in A the kernel
section whose image is 1 ⊗ a - a ⊗ 1 exists by the sectionwise kernel property.
The normalization hD identifies D(a) with the class of this section. Hence under
the conormal identification e sends da to the class of 1 ⊗ a - a ⊗ 1.
Mathlib defines the ring Kähler module to be J.Cotangent, with exactly this
formula for its universal derivation. The elements da span that module, so the
conjugate of e is the identity by linear-map extensionality on generators.
Consequently e(x) = e(y) implies x = y. This proof uses only the local diagonal,
and works for nonseparated f and for the zero ring of an empty affine chart. -/
theorem diagonalConormal_affine_lift_injective (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (D : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf)
    (hD : IsDiagonalConormalDerivation f D)
    (e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) →ₗ[Γ(X, U.1)]
      Γ(diagonalConormal f, U.1))
    (he : ∀ a : Γ(X, U.1), e (CommRingCat.KaehlerDifferential.d a) =
      D.d (X := op U.1) a) : Function.Injective e := by sorry

end AlgebraicGeometry
