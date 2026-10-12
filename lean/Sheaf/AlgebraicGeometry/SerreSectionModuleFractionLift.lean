/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Algebra.Module.DegreeZeroFractions
public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous


/-!
# Section represented by a homogeneous fraction

Source: Stacks Project, Proposition 0BXD, final paragraph.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace LocalizedModule
open HomogeneousLocalization MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every degree-zero fraction comes from a section on the standard open.
Source: Stacks Project, Proposition 0BXD, final paragraph.
(blueprint: lem-sc-p1-serre-section-module-fraction-lift)

Proof: If f=0, localization is zero and the standard open is empty; the zero section
works. Otherwise write the denominator as f^m. Its homogeneous degree is m*d,
by uniqueness of degree for nonzero homogeneous polynomials. The numerator
therefore lies in M_(m*d). Multiplication by f^m identifies G on D+(f) with
G tensor O(m*d): restrict unitToTwist, tensor with G and use the right unitor.
Apply its inverse to the restricted phi of the numerator. This yields the
required section and the displayed relation. For another representative,
LocalizedModule.mk_eq provides a power killing the cross multiplied
numerator difference. Apply phi and restrict; multiplication by the extra
power and by the first denominator is invertible on D+(f), giving the
formula for the other representative as well. -/
theorem serreSectionModuleFractionLift
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
    ∀ x, x ∈ degreeZeroFractions
        (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
        (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f) → ∃ s, Rel x s ∧
      (∀ (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ))),
        x = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • d : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hf))
            (basicOpen (homogeneousSubmodule (Fin 2) k) f) s) := by sorry

end AlgebraicGeometry.Proj
