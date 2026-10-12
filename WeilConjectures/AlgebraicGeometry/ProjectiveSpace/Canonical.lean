/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial
public import WeilConjectures.Mathlib.RingTheory.Kaehler.LocalizationPolynomial

/-!
# The canonical sheaf of projective space

Let `A` be a commutative ring and `ℙ = ℙ(n; Spec A)` with `Nat.card n = d + 1`. The canonical
sheaf `ω_ℙ = ⋀ᵈ Ω¹_{ℙ/A}` is invertible, with free generator
`ηᵢ = ± ⋀_{k ≠ i} d(x_k / xᵢ)` on the standard open `Uᵢ = D₊(xᵢ)`, and `ω_ℙ ≅ 𝒪(-d-1)`,
`ηᵢ ↦ eᵢ^{(-d-1)}`.

(blueprint: `lem-pc-projective-space-canonical`)
-/

@[expose] public section

universe u

open CategoryTheory Opposite MvPolynomial Module

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

variable (n : Type u) (A : Type u) [CommRing A]

/-- **The differentials on a basic open of a standard chart.** On a basic open `W = D(f)` of the
standard open `Uᵢ = D₊(xᵢ)` of `ℙ(n; Spec A)`, the sections of `Ω¹_{ℙ/A}` are free with basis
the differentials `d(x_k / xᵢ)`, `k ≠ i`: indeed `Γ(W)` is a localization of the polynomial ring
`Γ(Uᵢ) = A[x_k / xᵢ]` (`chartRingEquiv`), whose Kähler differentials are free on the
differentials of the variables. -/
theorem exists_basis_relativeDifferentials_basicOpen (i : n)
    (f : Γ(ℙ(n; Spec (.of A)), standardOpen n _ i)) :
    ∃ b : Basis {k : n // k ≠ i} Γ(ℙ(n; Spec (.of A)), ℙ(n; Spec (.of A)).basicOpen f)
        Γ((ℙ(n; Spec (.of A)) ↘ Spec (.of A)).relativeDifferentials,
          ℙ(n; Spec (.of A)).basicOpen f),
      ∀ k, b k = (ℙ(n; Spec (.of A)) ↘ Spec (.of A)).relativeDifferentials.presheaf.map
        (homOfLE (ℙ(n; Spec (.of A)).basicOpen_le f)).op
        ((ℙ(n; Spec (.of A)) ↘ Spec (.of A)).sectionsD _ (coordRatio n _ i k)) := by
  set X := ℙ(n; Spec (.of A))
  set g := X ↘ Spec (.of A)
  set W := X.basicOpen f
  have hU := isAffineOpen_standardOpen n (Spec (.of A)) i
  let : Algebra A Γ(X, W) := (g.specStructureMap W).hom.toAlgebra
  let : Algebra (MvPolynomial {k : n // k ≠ i} A) Γ(X, W) :=
    ((algebraMap Γ(X, standardOpen n _ i) Γ(X, W)).comp
      (chartRingEquiv n A i).symm.symm.toRingHom).toAlgebra
  have : IsLocalization ((Submonoid.powers f).map (chartRingEquiv n A i).symm) Γ(X, W) :=
    have := hU.isLocalization_basicOpen f
    IsLocalization.isLocalization_of_base_ringEquiv _ _ (chartRingEquiv n A i).symm
  have : IsScalarTower A (MvPolynomial {k : n // k ≠ i} A) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, MvPolynomial.algebraMap_eq,
        RingEquiv.symm_symm, RingEquiv.toRingHom_eq_coe]
      erw [chartRingEquiv_C]
      rw [← g.specStructureMap_map (X.basicOpen_le f), CommRingCat.comp_apply]
  refine ⟨(KaehlerDifferential.basisOfIsLocalizationMvPolynomial A {k : n // k ≠ i} Γ(X, W)
    ((Submonoid.powers f).map (chartRingEquiv n A i).symm)).map
      (g.kaehlerSectionsEquiv W rfl (hU.basicOpen f)), fun k ↦ ?_⟩
  rw [Basis.map_apply, KaehlerDifferential.basisOfIsLocalizationMvPolynomial_apply,
    Scheme.Hom.kaehlerSectionsEquiv_D, ← Scheme.Hom.sectionsD_map]
  congr 1
  simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingEquiv.symm_symm,
    RingEquiv.toRingHom_eq_coe]
  erw [chartRingEquiv_X]

end AlgebraicGeometry.ProjectiveSpace
