/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

/-!
# Scalar calculation on homogeneous chart representatives

Source: Stacks Project, Proposition 0BXD, final paragraph.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace LocalizedModule
open HomogeneousLocalization MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A chart characterized by clearing homogeneous denominators respects homogeneous
localization scalars.
Source: Stacks Project, Proposition 0BXD, final paragraph; step 2 of
lem-sc-p1-serre-section-module-charts.
(blueprint: lem-sc-p1-serre-section-module-chart-scalar)

Proof: the numerator y and scalar numerator a have degrees m*d and l*d. By hsmul,
a*y has degree (l+m)*d. Compatibility hphi identifies phi(a*y) with multiplication
by a on phi(y), and naturality restricts this identity to D+(f). By the hypothesis
hs and the characterization, phi(y) restricts to f^m times s. The definition of
awayToSection on a/f^l identifies its action with multiplication by a divided by
f^l. Hence phi(a*y) restricts to f^(l+m) times (a/f^l)*s. The characterization of
alpha in degree (l+m)*d gives the desired fraction. If f=0 the localization is zero
and the formula holds there as well. The argument includes l=0 and m=0, using the
zeroth twisting isomorphism and the right unitor. -/
theorem serreSectionModuleChartScalar
    (k : Type u) [Field k]
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (φ : ∀ z : ℤ, 0 ≤ z →
        (𝓜 z ≃+ Γ(G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k) z, ⊤)))
    (hφ : ∀ (z : ℤ) (hz : 0 ≤ z) (e : ℕ) (hze : 0 ≤ z + e) (a : MvPolynomial (Fin 2) k)
        (ha : a ∈ homogeneousSubmodule (Fin 2) k e)
        (y : 𝓜 z) (hay : a • (y : M) ∈ 𝓜 (z + e)),
        φ (z + e) hze ⟨a • (y : M), hay⟩ =
          Scheme.Modules.Hom.app (G ◁ Proj.twistMul z ha) ⊤ (φ z hz y))
    (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
    (alpha : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
      LocalizedModule.Away f M)
    (hnorm : ∀ (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alpha s = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) ↔
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • d : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hf))
            (basicOpen (homogeneousSubmodule (Fin 2) k) f) s)
    (l : ℕ) (a : MvPolynomial (Fin 2) k)
    (ha : a ∈ homogeneousSubmodule (Fin 2) k (l • d))
    (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
    (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)))
    (hs : alpha s = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
    alpha (awayToSection (homogeneousSubmodule (Fin 2) k) f
      (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 2) k) hf l a ha) • s) =
        mk (a • (y : M)) (⟨f ^ (l + m), ⟨l + m, rfl⟩⟩ : Submonoid.powers f) := by sorry

end AlgebraicGeometry.Proj
