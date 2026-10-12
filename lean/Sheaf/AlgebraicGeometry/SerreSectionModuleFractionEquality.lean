/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

import Sheaf.AlgebraicGeometry.SerreSectionModuleComparison

/-!
# Equality of represented homogeneous fractions

Source: Stacks Project, Proposition 0BXD, final paragraph.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace LocalizedModule
open HomogeneousLocalization MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Equality of fractions is equivalent to equality of their represented sections.
Source: Stacks Project, Proposition 0BXD, final paragraph.
(blueprint: lem-sc-p1-serre-section-module-fraction-equality)

Proof: Take witnesses y/f^m and z/f^n for the relations. Equality of fractions
means some f^e kills f^n*y-f^m*z. Apply phi in degree (m+n+e)*d.
Compatibility with homogeneous multiplication and restriction identifies the
result with multiplication by f^(m+n+e) on s-t, which is invertible on D+(f),
so s=t. Conversely, if s=t then the restrictions of phi(f^n*y-f^m*z)
vanish. The annihilation clause of serreSectionModuleComparison supplies a
power f^e killing its image under phi. Compatibility and injectivity of phi
kill f^e*(f^n*y-f^m*z), and LocalizedModule.mk_eq gives equal fractions.
The empty open and zero localization when f=0 satisfy both directions. -/
theorem serreSectionModuleFractionEquality
    (k : Type u) [Field k]
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (homogeneousSubmodule (Fin 2) k)).toRingedSpace G)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (hneg : ∀ z : ℤ, z < 0 → 𝓜 z = ⊥)
    (φ : ∀ z : ℤ, 0 ≤ z →
        (𝓜 z ≃+ Γ(G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k) z, ⊤)))
    (hφ : ∀ (z : ℤ) (hz : 0 ≤ z) (e : ℕ) (hze : 0 ≤ z + e) (a : MvPolynomial (Fin 2) k)
        (ha : a ∈ homogeneousSubmodule (Fin 2) k e)
        (y : 𝓜 z) (hay : a • (y : M) ∈ 𝓜 (z + e)),
        φ (z + e) hze ⟨a • (y : M), hay⟩ =
          Scheme.Modules.Hom.app (G ◁ Proj.twistMul z ha) ⊤ (φ z hz y))
    (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d) :
    let Rel := fun (x : LocalizedModule.Away f M)
      (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))) ↦
      ∃ (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ))),
        x = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) ∧
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • d : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hf))
            (basicOpen (homogeneousSubmodule (Fin 2) k) f) s
    ∀ x z s t, Rel x s → Rel z t → (x = z ↔ s = t) := by sorry

end AlgebraicGeometry.Proj
