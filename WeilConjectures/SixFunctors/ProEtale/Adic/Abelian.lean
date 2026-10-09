/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix

/-!
# Kernels and cokernels of constructible `ℓ`-adic sheaves

A morphism `ψ : ℚ̄_ℓ,Tⁿ ⟶ ℚ̄_ℓ,Tᵐ` of finite free modules is a matrix of locally finite continuous
functions on `T` (`AlgebraicGeometry.ProEtale.AdicSheaf.unitMatrix`). If its rank at the points
of `T` is constant, then locally on `T` it is equivalent to `[[1, 0], [0, 0]]`, so its kernel and
cokernel are lisse (`AlgebraicGeometry.ProEtale.AdicSheaf.isAdicLisseSheaf_kernel_cokernel_of_rank_eq`).
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T : Scheme.{u}}

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AdicSheaf

variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A finite free module over a finite index type is a free module over `Fin n`. -/
noncomputable def freeFinIso (ι : Type) [Fintype ι] (V : Scheme.{u}) :
    (⨁ fun _ : ι ↦ unit l V) ≅ ⨁ fun _ : Fin (Fintype.card ι) ↦ unit l V :=
  biproduct.whiskerEquiv (g := fun _ : Fin (Fintype.card ι) ↦ unit l V) (Fintype.equivFin ι)
    fun _ ↦ Iso.refl (unit l V)

/-- **Kernels and cokernels of constant rank are lisse.** A morphism of finite free
`ℚ̄_ℓ,T`-modules whose matrix of functions has the same rank at every point of `T` has lisse
kernel and cokernel. -/
theorem isAdicLisseSheaf_kernel_cokernel_of_rank_eq
    (ψ : (⨁ fun _ : ι ↦ unit l T) ⟶ ⨁ fun _ : κ ↦ unit l T) (r : ℕ)
    (hr : ∀ t, ((unitMatrix ψ).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank = r) :
    IsAdicLisseSheaf (kernel ψ) ∧ IsAdicLisseSheaf (cokernel ψ) := by
  classical
  choose U ρ γ hρ hγ hU ht hfac using
    fun t ↦ PadicAlgCl.exists_isOpen_eq_mul (unitMatrix ψ) r hr t
  let O (t : T) : T.Opens := ⟨U t, hU t⟩
  have hR : Presieve.ofArrows (fun t ↦ (O t).toScheme) (fun t ↦ (O t).ι) ∈
      Scheme.proetalePrecoverage T :=
    Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff (P := @IsOpenImmersion)).2 ⟨fun x ↦ ⟨x, by simpa [O] using ht x⟩,
        fun _ ↦ inferInstance⟩)
  have key (t : T) : ∃ (P : Matrix κ κ _) (Q : Matrix ι ι _), IsUnit P.det ∧ IsUnit Q.det ∧
      unitMatrix ((freeUpperStarIso l ι (O t).ι).inv ≫ ((O t).ι)^*ᵃ[l].map ψ ≫
        (freeUpperStarIso l κ (O t).ι).hom) = P * (Matrix.fromBlocks 1 0 0 0 :
          Matrix (Fin r ⊕ {i // i ∉ Set.range (ρ t)}) (Fin r ⊕ {j // j ∉ Set.range (γ t)}) _).reindex
            (PadicAlgCl.sumComplEquiv (ρ t) (hρ t)).symm
            (PadicAlgCl.sumComplEquiv (γ t) (hγ t)).symm * Q := by
    obtain ⟨P, Q, hP, hQ, h⟩ := hfac t (O t).ι.base.hom (by simp [O])
    exact ⟨P, Q, hP, hQ, (unitMatrix_adicUpperStar _ ψ).trans h⟩
  refine ⟨⟨_, hR, ?_⟩, ⟨_, hR, ?_⟩⟩ <;> rintro _ _ ⟨t⟩ <;>
    obtain ⟨P, Q, hP, hQ, h⟩ := key t <;>
    have hconj := eq_blockMap_of_unitMatrix_eq _ P Q h <;>
    have := isIso_ofUnitMatrix P hP <;> have := isIso_ofUnitMatrix Q hQ
  · exact ⟨_, ⟨PreservesKernel.iso ((O t).ι)^*ᵃ[l] ψ ≪≫
      (kernelIsIsoComp (freeUpperStarIso l ι (O t).ι).inv _ ≪≫ kernelCompMono _
        (freeUpperStarIso l κ (O t).ι).hom).symm ≪≫ kernelIsoOfEq hconj ≪≫
      kernelIsIsoComp _ _ ≪≫ kernelCompMono _ _ ≪≫ kernelBlockMapIso _ _ _ _ ≪≫
      freeFinIso _ _⟩⟩
  · exact ⟨_, ⟨PreservesCokernel.iso ((O t).ι)^*ᵃ[l] ψ ≪≫
      (cokernelEpiComp (freeUpperStarIso l ι (O t).ι).inv _ ≪≫ cokernelCompIsIso _
        (freeUpperStarIso l κ (O t).ι).hom).symm ≪≫ cokernelIsoOfEq hconj ≪≫
      cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫ cokernelBlockMapIso _ _ _ _ ≪≫
      freeFinIso _ _⟩⟩

end AdicSheaf

end AlgebraicGeometry.ProEtale
