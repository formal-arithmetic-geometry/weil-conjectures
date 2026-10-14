/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Normalized affine pullback models with an isomorphic starting chart

Source: Stacks Project, Tag 01I6, Lemmas 26.7.1, 26.7.3, 26.7.4 and 26.7.5.
(blueprint: lem-pc-affine-isomorphic-source-normalized-models).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
open scoped ChangeOfRings
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Normalized scalar-extension models for one affine pullback, starting
from sections on an isomorphic affine chart. The starting equivalences are fixed
before the destination chart, its coefficient ring, or its ring presentation.
Source: Stacks Project, Tag 01I6, Lemmas 26.7.1, 26.7.3, 26.7.4 and 26.7.5.
(blueprint: lem-pc-affine-isomorphic-source-normalized-models).

Proof: Since s is an isomorphism, its pullback unit is bijective on global
sections. Take its inverse as δM and δN. This choice depends only on s,M,N.
Identify A and T with the spectra of their section rings, and identify W with
Spec S using ρ. The displayed ring equation says precisely that q corresponds
to r composed with s.appTop. Apply affine quasi-coherent reconstruction to M,N
and the scalar-extension/pullback identification. Changing coordinates by s
and ρ gives eM,eN. On tensors this map is b tensor m mapped to ρ(b) times the
pullback of δ(m); thus it is semilinear and has the stated unit formula. Its
inverse is the inverse affine reconstruction comparison, so it is an additive
equivalence, even for zero rings and zero modules. There is no finite-presentation
hypothesis. -/
theorem affine_isomorphic_source_normalized_models
    {A T : Scheme.{u}} [IsAffine A] (s : T ⟶ A) [IsIso s]
    (M N : A.Modules) (hMq : M.IsQuasicoherent) (hNq : N.IsQuasicoherent) :
    let P := ModuleCat.of Γ(T, ⊤) Γ((Scheme.Modules.pullback s).obj M, ⊤)
    let Q := ModuleCat.of Γ(T, ⊤) Γ((Scheme.Modules.pullback s).obj N, ⊤)
    ∃ (δM : (P : Type u) ≃ Γ(M, ⊤)) (δN : (Q : Type u) ≃ Γ(N, ⊤)),
      ∀ (W : Scheme.{u}) (_ : IsAffine W) (q : W ⟶ A)
        (S : CommRingCat.{u}) (r : Γ(T, ⊤) →+* S) (ρ : S ≃+* Γ(W, ⊤)),
        (∀ b, ρ (r (s.appTop b)) = q.appTop b) →
        ∃ (eM : (ModuleCat.extendScalars r).obj P ≃+
            Γ((Scheme.Modules.pullback q).obj M, ⊤))
          (eN : (ModuleCat.extendScalars r).obj Q ≃+
            Γ((Scheme.Modules.pullback q).obj N, ⊤)),
          (∀ b z, eM (b • z) = ρ b • eM z) ∧
          (∀ b z, eN (b • z) = ρ b • eN z) ∧
          (∀ m, eM ((1 : S) ⊗ₜ[Γ(T, ⊤), r] m) = pullbackΓ q M (δM m)) ∧
          (∀ m, eN ((1 : S) ⊗ₜ[Γ(T, ⊤), r] m) = pullbackΓ q N (δN m)) := by sorry

end AlgebraicGeometry
