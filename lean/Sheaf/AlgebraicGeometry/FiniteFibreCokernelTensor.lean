/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Residue-field tensor of the section-map cokernel

Source: Stacks Project, Tag 04DG, proof, affine fibre and Nakayama steps.
(blueprint: lem-weil-pbc-finite-fibre-cokernel-tensor).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The cokernel of the affine section map has zero residue-field tensor when the fibre
is a closed immersion.
Source: Stacks Project, Tag 04DG, proof, affine fibre and Nakayama steps.
(blueprint: lem-weil-pbc-finite-fibre-cokernel-tensor).

Proof: Put A = Γ(S,U) and B = Γ(X,f⁻¹U). Since f is finite, both U and f⁻¹U are affine.
The prime p corresponding to s has residue field canonically isomorphic to κ(s).
The affine pullback formula identifies the fibre with Spec(κ(p) ⊗[A] B), and its map
with the spectrum of the scalar map κ(p) → κ(p) ⊗[A] B. A closed immersion between
these affine schemes gives surjectivity of that scalar map. The image of the map
A → B is its range as an A-linear map. Tensoring its cokernel sequence with κ(p)
is right exact, so its cokernel tensor product is zero. No Nakayama step is needed
here. For an empty fibre the tensor algebra is the zero ring, and the argument
still applies. -/
theorem subsingleton_fibreTensor_sectionCokernel
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (U : S.Opens) (hU : IsAffineOpen U) (s : U)
    (hf : IsClosedImmersion (f.fiberToSpecResidueField s.1)) :
    letI := (f.app U).hom.toAlgebra
    Subsingleton ((hU.primeIdealOf s).asIdeal.ResidueField ⊗[Γ(S, U)]
      (Γ(X, f ⁻¹ᵁ U) ⧸ (Algebra.linearMap Γ(S, U) Γ(X, f ⁻¹ᵁ U)).range)) := by sorry

end AlgebraicGeometry
