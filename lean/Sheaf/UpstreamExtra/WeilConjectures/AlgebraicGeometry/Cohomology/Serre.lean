module

public import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.AlternatingCechComputes

/-!
Declarations of ours that lived in the upstream file
`WeilConjectures.AlgebraicGeometry.Cohomology.Serre` (moved out by the scheduled sync,
tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live).
-/

/-!
# Serre's theorems on the cohomology of projective schemes

This file states, for the Picard-framework block of the blueprint, the three results of
Serre's *Faisceaux algébriques cohérents* that the rest of the block uses: the computation of
the cohomology of the twisting sheaves on projective space, and Serre's theorems A and B for a
coherent sheaf on a closed subscheme of projective space.

Theorem B is proved from the cohomology of the twisting sheaves: a coherent module on `ℙᵈ_k`
is a quotient of a finite sum of twists `𝒪(-m)` with coherent kernel, and descending induction
on the degree in the long exact cohomology sequence gives Serre vanishing on `ℙᵈ_k`; a closed
subscheme reduces to `ℙᵈ_k` by pushing forward. Serre vanishing for an ample invertible module
follows.

Projective space is the project's relative projective space `ℙ(n; S)`, whose index type `n` is
the index type of the *homogeneous* coordinates, so that `ℙᵈ_k` is `ℙ(n; Spec k)` for a type
`n` with `Nat.card n = d + 1`.

The twisting sheaf `AlgebraicGeometry.ProjectiveSpace.twist` is the pullback along
`AlgebraicGeometry.ProjectiveSpace.toProjInt` of `AlgebraicGeometry.Proj.twist` of the integral
model `Proj ℤ[Tᵢ]`, and `AlgebraicGeometry.ProjectiveSpace.twistRestrict` is its pullback to a
closed subscheme.

## Implementation notes

The symmetric power `Sᵐ(V)` of `V = k^{d+1}` is realised as the degree-`m` homogeneous part
`MvPolynomial.homogeneousSubmodule n k m` of the polynomial ring in the homogeneous
coordinates. Mathlib's `SymmetricPower R ι M` forces the index type `ι` to lie in the same
universe as the ring `R`, which does not fit `Sym^m` for a field in an arbitrary universe, and
the homogeneous part is anyway the object Serre's theorem produces.

Mathlib has no `IsCoherent` predicate for sheaves of modules; "coherent" is spelled here as
`SheafOfModules.IsFinitePresentation` together with `SheafOfModules.IsQuasicoherent`, which
agrees with coherence on a noetherian scheme such as a closed subscheme of `ℙᵈ_k`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.subsingleton_H_twist_of_ne` and `subsingleton_H_twist_top`
  — the vanishing of the cohomology of `𝒪(m)` on `ℙᵈ_k`. The canonical isomorphisms
  `H⁰(ℙᵈ_k, 𝒪(m)) ≅ Sᵐ(V)` and `Hᵈ(ℙᵈ_k, 𝒪(m)) ≅ S^{-m-d-1}(V)^∨` are in
  `WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceOverField`.
- `AlgebraicGeometry.ProjectiveSpace.exists_epi_sigma_twist` — a coherent module on `ℙⁿ_A` is a
  quotient of a finite sum of twists `𝒪(-mⱼ)`.
- `AlgebraicGeometry.ProjectiveSpace.exists_subsingleton_H_tensor_twist` — Serre vanishing on
  `ℙᵈ_k`: `H^q(ℙᵈ_k, ℱ(d)) = 0` for `q > 0` and `d ≫ 0`.
- `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensor_twist` — Serre's theorem B.
- `AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_tensorObj_tensorPow` — Serre vanishing
  for an ample invertible module.
- `AlgebraicGeometry.Scheme.Modules.exists_generatingSections_tensor_twist` — Serre's
  theorem A.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry.Scheme.Modules

-- This migration remnant intentionally retains only private helpers.
set_option linter.privateModule false

noncomputable section

namespace AlgebraicGeometry

variable (n : Type u)

section Pn

private def opensSiteCech (X : Scheme.{u}) (U : n → X.Opens) :
    SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)) where
  W p t := ⨅ k, U (t k)
  pr p t k := homOfLE (iInf_le _ k)
  comm _ _ _ := Subsingleton.elim _ _
  universal p t Z a _ := by
    refine ⟨homOfLE (le_iInf fun k ↦ (a k).le), ?_, ?_⟩
    · intro k
      apply Subsingleton.elim
    · intro b _
      apply Subsingleton.elim
  W_zero t := by simp
  pr_zero _ := Subsingleton.elim _ _
  indexMap t α := homOfLE (le_iInf fun k ↦ iInf_le _ (α k))
  indexMap_pr _ _ _ := Subsingleton.elim _ _

private noncomputable def opensSiteCechIso (X : Scheme.{u}) (U : n → X.Opens)
    (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (opensSiteCech n X U).complex F ≅ (TopCat.Presheaf.cechComplex U).obj F :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro p q hpq
    obtain rfl : p + 1 = q := hpq
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply AddCommGrpCat.ext
    intro s
    funext t
    rw [TopCat.Presheaf.cechComplex_d_apply]
    simp only [SiteCechComplex.complex, CochainComplex.of_d]
    rfl)

end Pn

section TwistQuotient

variable {n}

end TwistQuotient

section SerreVanishing

variable {n} (k : Type u) [Field k]

end SerreVanishing

variable {n} {X : Scheme.{u}} (k : Type u) [Field k]

end AlgebraicGeometry
