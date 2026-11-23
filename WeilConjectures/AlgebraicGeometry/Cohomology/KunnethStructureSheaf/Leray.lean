/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.LerayNatural

/-!
# Bijectivity of maps on cohomology via Čech cohomology

Through Leray's natural isomorphism, a pair of maps `H^q(ℱ) → H^q(𝒢₁)`, `H^q(ℱ) → H^q(𝒢₂)`
induced by morphisms of quasi-coherent modules is jointly bijective as soon as the induced maps on
Čech cohomology, for a covering with affine finite intersections, are.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.bijective_H_map_prod_of_bijective_cechCohomologyFunctor_map`
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Leray's isomorphism, precomposed with the identification of Čech cohomology of the module
with Čech cohomology of its underlying abelian sheaf, is natural in the module. -/
lemma H_map_cechComplexHomologyLinearEquivH_symm_apply {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    {ℱ 𝒢 : X.Modules} [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢] (φ : ℱ ⟶ 𝒢) (q : ℕ)
    (x : (TopCat.Sheaf.cechCohomologyFunctor U q).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ)) :
    H.map φ q (cechComplexHomologyLinearEquivH U hU hU' ℱ q
        ((cechComplexHomologyAddEquiv U ℱ q).symm x)) =
      cechComplexHomologyLinearEquivH U hU hU' 𝒢 q ((cechComplexHomologyAddEquiv U 𝒢 q).symm
        ((TopCat.Sheaf.cechCohomologyFunctor U q).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) x)) := by
  obtain ⟨y, rfl⟩ := (cechComplexHomologyAddEquiv U ℱ q).surjective x
  rw [AddEquiv.symm_apply_apply, ← cechComplexHomologyLinearEquivH_map,
    ← cechComplexHomologyAddEquiv_map, AddEquiv.symm_apply_apply]

/-- Let `φ₁ : ℱ ⟶ 𝒢₁`, `φ₂ : ℱ ⟶ 𝒢₂` be morphisms of quasi-coherent modules and `U` a covering
all of whose nonempty finite intersections are affine. If `(φ₁, φ₂)` induces a bijection
`Ȟ^q(U, ℱ) → Ȟ^q(U, 𝒢₁) × Ȟ^q(U, 𝒢₂)`, it induces a bijection
`H^q(ℱ) → H^q(𝒢₁) × H^q(𝒢₂)`. -/
lemma bijective_H_map_prod_of_bijective_cechCohomologyFunctor_map {ι : Type u}
    (U : ι → X.Opens) (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i))
    (hU' : iSup U = ⊤) {ℱ 𝒢₁ 𝒢₂ : X.Modules}
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢₁]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢₂] (φ₁ : ℱ ⟶ 𝒢₁) (φ₂ : ℱ ⟶ 𝒢₂)
    (q : ℕ)
    (h : Function.Bijective fun x : (TopCat.Sheaf.cechCohomologyFunctor U q).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ) ↦
      ((TopCat.Sheaf.cechCohomologyFunctor U q).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map φ₁) x,
        (TopCat.Sheaf.cechCohomologyFunctor U q).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map φ₂) x)) :
    Function.Bijective fun c : ℱ.H q ↦ (H.map φ₁ q c, H.map φ₂ q c) := by
  let E (𝒢 : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢] :=
    (cechComplexHomologyAddEquiv U 𝒢 q).symm.toEquiv.trans
      (cechComplexHomologyLinearEquivH U hU hU' 𝒢 q).toEquiv
  have hE : (fun c : ℱ.H q ↦ (H.map φ₁ q c, H.map φ₂ q c)) =
      ((E 𝒢₁).prodCongr (E 𝒢₂)) ∘ (fun x ↦ ((TopCat.Sheaf.cechCohomologyFunctor U q).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map φ₁) x,
        (TopCat.Sheaf.cechCohomologyFunctor U q).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map φ₂) x)) ∘ (E ℱ).symm := by
    funext c
    obtain ⟨x, rfl⟩ := (E ℱ).surjective c
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact Prod.ext (H_map_cechComplexHomologyLinearEquivH_symm_apply U hU hU' φ₁ q x)
      (H_map_cechComplexHomologyLinearEquivH_symm_apply U hU hU' φ₂ q x)
  rw [hE]
  exact ((E 𝒢₁).prodCongr (E 𝒢₂)).bijective.comp (h.comp (E ℱ).symm.bijective)

end AlgebraicGeometry.Scheme.Modules
