/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Constant multiplication on twisted sections

Source: Stacks Project, Lemma 01YS, proof of (5); homogeneous fraction construction
of the twisting sheaf, Tag 01M6.
(blueprint: lem-sc-p1-twisted-sections-constant-action).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/-- Constant homogeneous multiplication agrees with the canonical base-field action.
Source: Stacks Project, Lemma 01YS, proof of (5), and Tag 01M6.
(blueprint: lem-sc-p1-twisted-sections-constant-action).

Proof: on D₊(Xᵢ) and each of its subopens the structure-map image of c is the degree-zero
fraction C(c)/1. The definition of twistMul multiplies a degree-n fraction a/b by
C(c)/1. This is therefore multiplication by the restriction of the global function
ρ(c), on every section of O(n). Equality on the two basic opens, which cover Proj,
gives equality of these sheaf morphisms after transporting n+0 to n. Tensoring this
morphism with the identity of G acts by the same scalar: on pure tensors,
x tensor (ρ(c) y) = ρ(c) (x tensor y). Additivity gives the equality on the presheaf
tensor product, and sheafification preserves it. Evaluating on global sections gives
the displayed formula. Proof irrelevance makes it independent of the equality p and
of ha. No coherence or positivity assumption is required; c=0 and c=1 give zero and
the identity, and the argument also applies to the zero sheaf and negative twists. -/
theorem serreTwistedSectionsConstantAction
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (n : ℤ) :
    let ρ := ((Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k)).appTop.hom.comp
      (Scheme.ΓSpecIso _).inv.hom).comp
        (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k).toRingHom
    letI := Module.compHom
      Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, ⊤) ρ
    ∀ (c : k)
      (ha : MvPolynomial.C c ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k 0)
      (s : Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, ⊤))
      (p : G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (n + (0 : ℕ)) = G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n),
      Scheme.Modules.Hom.app ((G ◁ Proj.twistMul n ha) ≫ eqToHom p) ⊤ s =
        c • s := by sorry

end AlgebraicGeometry
