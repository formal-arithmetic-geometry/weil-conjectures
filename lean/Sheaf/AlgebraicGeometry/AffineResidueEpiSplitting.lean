/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # Splitting an affine module map detected on residue fibres

Source: Stacks Project, Tags 068V and 00NX, the finite-cokernel Nakayama
argument in the bounded finite-projective specialization.
(blueprint: lem-pc-affine-residue-epi-splitting)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Residue surjectivity splits a map onto a finitely presented flat affine module.

Source: Stacks Project, Tags 068V and 00NX; finite-cokernel Nakayama argument.
(blueprint: lem-pc-affine-residue-epi-splitting).

Proof: Identify S with Spec A for A = Γ(S, ⊤). The affine equivalence identifies
M and N with their section modules and f with an A-linear map. Finite presentation
and flatness of N imply that its section module is finite projective (00NX).
The cokernel C of the section map is finite, being a quotient of the finite target.
Right exactness of tensor identifies C tensor κ(p) with the cokernel of the fibre
map; the hypothesis makes this zero for every prime. Local Nakayama makes C_p
zero. Detection of zero modules by maximal localizations gives C = 0, so the
section map is surjective. Projectivity of the target provides a right inverse.
Apply tilde to this right inverse and conjugate by the affine counit isomorphisms;
functoriality proves that it is a right inverse to f. No finiteness of M is needed.
For the empty affine scheme the section ring is zero and both modules are zero,
so the argument still gives a splitting. -/
theorem affine_isSplitEpi_of_residue_epi (S : Scheme.{u}) (hS : IsAffine S)
    (M N : S.Modules) (f : M ⟶ N)
    (hMqc : M.IsQuasicoherent) (hNqc : N.IsQuasicoherent)
    (hNflat : N.IsFlatOver (𝟙 S)) (hNfp : N.IsFinitePresentation)
    (hf : ∀ s : S, Epi ((Modules.pullback (S.fromSpecResidueField s)).map f)) :
    IsSplitEpi f := by sorry

end AlgebraicGeometry.Scheme.Modules
