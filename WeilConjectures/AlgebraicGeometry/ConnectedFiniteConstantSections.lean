/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantSections
import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Connectedness and finite constant sections

Source: sk-cor-trace, proof step 2; the finite constant sheaf computation.
(blueprint: lem-pd-connected-finite-constant-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale

/-- On a nonempty connected scheme the specified constant-section map for a
finite discrete coefficient ring is bijective, including the zero ring.
Source: sk-cor-trace, proof step 2
(blueprint: lem-pd-connected-finite-constant-sections).
Proof: use the proved ring equivalence from pro-etale constant sections to
continuous functions. Its normalization identifies this map with constant
functions. A continuous map from a connected space to a discrete space is
constant. Evaluation at any point is its inverse; nonemptiness supplies the
point and also proves injectivity of constant functions. -/
theorem connected_finite_constant_sections (X : Scheme.{u}) [ConnectedSpace X]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] :
    Function.Bijective
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A))).app
          (op (Scheme.ProEt.mk (𝟙 X)))) := by
  classical
  obtain ⟨θ, hθ, _⟩ := proEtale_finite_constant_sections X A
  let W := Scheme.ProEt.mk (𝟙 X)
  let x₀ := Classical.arbitrary X
  refine ⟨?_, ?_⟩
  · intro a b hab
    have h := congrArg (fun z ↦ θ W z x₀) hab
    exact (congrArg (fun f : C(W.left, A) ↦ f x₀) (hθ W a)).symm.trans
      (h.trans (congrArg (fun f : C(W.left, A) ↦ f x₀) (hθ W b)))
  · intro z
    refine ⟨θ W z x₀, ?_⟩
    apply (θ W).injective
    rw [hθ]
    ext x
    exact PreconnectedSpace.constant (inferInstance : PreconnectedSpace X)
      (θ W z).continuous

end AlgebraicGeometry.ProEtale
