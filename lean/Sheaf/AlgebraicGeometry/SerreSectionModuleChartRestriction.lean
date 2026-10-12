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
# Restriction calculation on homogeneous chart representatives

Source: Stacks Project, Proposition 0BXD, final paragraph.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace LocalizedModule
open HomogeneousLocalization MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Canonical charts commute with restriction on homogeneous representatives.
Source: Stacks Project, Proposition 0BXD, final paragraph; the homogeneous calculation
in step 3 of lem-sc-p1-serre-section-module-charts.
(blueprint: lem-sc-p1-serre-section-module-chart-restriction)

Proof: for y of degree m*d the characterization of alpha_f identifies the restriction
of phi(y) with multiplication of s by f^m. Restrict this equality to D+(g). Multiply
by a^m and use hphi to identify the numerator with phi(a^m*y). When f,g,a are nonzero,
uniqueness of homogeneous degree in g^e=a*f gives e*b=c+d. Thus a^m*y has degree
e*m*b, and (a*f)^m=g^(e*m) identifies the multiplication on the right with the
one in the characterization of alpha_g. That characterization gives the displayed
fraction formula. If a=0 or f=0, the relation forces g=0 (the polynomial ring is a
domain and e>0); the target chart and target localization are zero. If g=0 directly,
the same zero argument applies. The case m=0 uses the zeroth power, unitToTwistZero
and the right unitor, so the argument also covers denominator one. -/
theorem serreSectionModuleChartRestriction
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
    (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
    (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
    (alphaF : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
      LocalizedModule.Away f M)
    (alphaG : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) g)) →+
      LocalizedModule.Away g M)
    (hnormF : ∀ (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alphaF s = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) ↔
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • d : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hf))
            (basicOpen (homogeneousSubmodule (Fin 2) k) f) s)
    (hnormG : ∀ (m : ℕ) (y : 𝓜 (0 + ((m • b : ℕ) : ℤ)))
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) g))),
      alphaG s = mk (y : M) (⟨g ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers g) ↔
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • b : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) g ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hg))
            (basicOpen (homogeneousSubmodule (Fin 2) k) g) s)
    (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
      basicOpen (homogeneousSubmodule (Fin 2) k) f)
    (e c : ℕ) (a : MvPolynomial (Fin 2) k)
    (he : 0 < e) (ha : a ∈ homogeneousSubmodule (Fin 2) k c) (hrel : g ^ e = a * f)
    (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
    (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)))
    (hs : alphaF s = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
    alphaG (G.val.map (homOfLE inc).op s) =
      mk (a ^ m • (y : M)) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g) := by sorry

end AlgebraicGeometry.Proj
