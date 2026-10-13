/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Extending affine section maps

Source: Stacks Project, Schemes, Lemma 01IB; Properties, Lemma 01PM.
(blueprint: lem-weil-pbc-affine-section-linear-map-extension).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- A linear map on an affine open extends from a quasi-coherent source to a sheaf map.

Source: Stacks Project, Schemes, Lemma 01IB (affine equivalence), and Properties,
Lemma 01PM (passing from linear maps to sheaf maps).
(blueprint: lem-weil-pbc-affine-section-linear-map-extension).

Proof: Identify V with Spec R, R = O_X(V). Quasi-coherence identifies P|V with
Gamma(V,P) tilde. The tilde-Gamma adjunction sends f to a morphism from this
tilde module into Q|V; compose with the inverse of the source identification.
The unit identity of the adjunction says its value on every global section b
is f(b). Transport back along V = Spec R and the equivalence between modules
on V and modules over the category of opens below V. The target need not be
quasi-coherent, since the adjunction applies to every sheaf of modules.
The construction works also when V is empty or P or Q is zero. -/
theorem affine_section_linear_map_extension
    {X : Scheme.{u}} (P Q : X.Modules) [P.IsQuasicoherent]
    (V : X.affineOpens) (f : Γ(P, V.1) →ₗ[Γ(X, V.1)] Γ(Q, V.1)) :
    ∃ φ : P.over V.1 ⟶ Q.over V.1,
      ∀ b : Γ(P, V.1), φ.val.app (op (Over.mk (homOfLE (le_refl V.1)))) b =
        f b := by sorry

end AlgebraicGeometry.Scheme
