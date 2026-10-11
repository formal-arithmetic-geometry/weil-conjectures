module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Affine section base change for quasi-coherent modules

Source: Stacks Project, Constructions, Lemma 01LN, using Schemes Lemmas 01I9 and 01IA
(blueprint: lem-weil-pbc-quasi-coherent-affine-section-base-change).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- For affine opens `U ≤ V` of a scheme `X` and a quasi-coherent `F`, the canonical map
`F(V) ⊗[O(V)] O(U) → F(U)`, `m ⊗ r ↦ r • m|_U`, is a bijective linear map, linear also for
the action of `O(U)` on the second tensor factor (written, as in
lem-weil-pbc-module-pullback-affine-sections, by swapping to `O(U) ⊗[O(V)] F(V)`, acting on
the left factor and swapping back).
Source: Stacks Project, Constructions, Lemma 01LN, using Schemes Lemmas 01I9 and 01IA
(blueprint: lem-weil-pbc-quasi-coherent-affine-section-base-change).

Proof: (1) Take the canonical affine charts Spec R → X, Spec R' → X of U and V; the
restriction ρ : R' → R gives the open immersion j = Spec ρ with ι_V ∘ j = ι_U
(lem-weil-pbc-affine-open-spec-points, lem-weil-pbc-affine-open-inclusion-spec-map).
(2) The restriction of F to Spec R' is quasi-coherent, hence the tilde of M' = F(V) by the
affine tilde-Gamma counit ε (lem-weil-pbc-module-restriction-open-immersion-colimits,
lem-weil-pbc-affine-tilde-gamma-adjunction).
(3) Restricting further along j gives the restriction of F along ι_U, with sections F(U).
(4) Open-immersion pullback is restriction, and tilde commutes with pullback along Spec ρ
(lem-weil-pbc-open-immersion-module-pullback-restriction,
lem-weil-pbc-tilde-pullback-base-change); taking sections gives an R-linear isomorphism
Φ : R ⊗[R'] M' → F(U).
(5) Tracing m' through units and counits shows Φ(r ⊗ m') = r • m'|_U, so after swapping the
factors Φ is the canonical map, which is therefore bijective and R-linear. -/
theorem quasiCoherent_affine_section_baseChange
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U V : X.affineOpens) (hUV : U.1 ≤ V.1) :
    letI : Algebra Γ(X, V.1) Γ(X, U.1) :=
      (X.presheaf.map (homOfLE hUV).op).hom.toAlgebra
    letI : Module Γ(X, V.1) Γ(F, U.1) :=
      Module.compHom _ (X.presheaf.map (homOfLE hUV).op).hom
    ∃ c : (Γ(F, V.1) ⊗[Γ(X, V.1)] Γ(X, U.1)) →ₗ[Γ(X, V.1)] Γ(F, U.1),
      Function.Bijective c ∧
      (∀ (r : Γ(X, U.1)) (t : Γ(F, V.1) ⊗[Γ(X, V.1)] Γ(X, U.1)),
        c ((TensorProduct.comm Γ(X, V.1) Γ(F, V.1) Γ(X, U.1)).symm
          (r • TensorProduct.comm Γ(X, V.1) Γ(F, V.1) Γ(X, U.1) t)) = r • c t) ∧
      (∀ (m : Γ(F, V.1)) (r : Γ(X, U.1)),
        c (m ⊗ₜ[Γ(X, V.1)] r) = r • F.presheaf.map (homOfLE hUV).op m) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
