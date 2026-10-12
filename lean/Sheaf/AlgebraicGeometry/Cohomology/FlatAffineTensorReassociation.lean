/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Scalar reassociation on a cartesian affine open

Source: Stacks Project, Tag 02KG, the displayed tensor reassociation in its proof.
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}}

/-- Reassociate scalar extension with the coefficient ring of a cartesian affine open.
This concerns the original section module only, and assumes no quasi-coherence.
Source: Stacks Project, Tag 02KG, proof of Lemma 30.5.1.
(blueprint: lem-pc-flat-affine-tensor-reassociation)

Proof: Put A = Gamma(W,O_X), B = Gamma(W',O_{X_S}). The cartesian square of
Spec S and W over Spec R identifies B with S tensor_R A, respecting the maps
from A and S (Stacks 01I4). The scalar action of R on Gamma(W,M) is the
restriction of its A-action, by naturality of the structure map. Tensor
associativity and the tensor-unit equivalence identify
(S tensor_R A) tensor_A Gamma(W,M) with S tensor_R Gamma(W,M).
Compose the inverse with the coefficient ring identification. On pure tensors
this sends b tensor s to the image of b in B tensor s. Each map is S-linear,
so their composite is the asserted equivalence. No flatness is used. If W is
empty, A and B are zero rings and both section tensors are zero; the same
isomorphisms still apply. -/
theorem exists_baseChange_affine_tensor_reassociation (f : X ⟶ Spec (.of R))
    (W : X.Opens) (hW : IsAffineOpen W) (M : X.Modules)
    (W' : (baseChangedScheme (S := S) f).Opens)
    (hW' : W' = baseChangeFst (S := S) f ⁻¹ᵁ W)
    (h : W' ≤ baseChangeFst (S := S) f ⁻¹ᵁ W) :
    let P := M.presheafModuleCat ⋙
      ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    let β := (((baseChangedScheme (S := S) f).presheaf.map
      (homOfLE (le_top : W' ≤ ⊤)).op).hom).comp
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
    letI : Algebra Γ(X, W) Γ(baseChangedScheme (S := S) f, W') :=
      (baseChangeFst (S := S) f |>.appLE W W' h).hom.toAlgebra
    letI : Module S (TensorProduct Γ(X, W) Γ(baseChangedScheme (S := S) f, W')
        Γ(M, W)) := Module.compHom _ β
    ∃ e : TensorProduct R S (P.obj (op W)) ≃ₗ[S]
        TensorProduct Γ(X, W) Γ(baseChangedScheme (S := S) f, W') Γ(M, W),
      ∀ (b : S) (s : P.obj (op W)),
        e (b ⊗ₜ[R] s) = β b ⊗ₜ[Γ(X, W)] (show Γ(M, W) from s) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
