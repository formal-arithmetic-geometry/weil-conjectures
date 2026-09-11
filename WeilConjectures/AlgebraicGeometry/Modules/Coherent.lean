/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Coherent sheaves form an abelian subcategory

Over a locally Noetherian scheme, kernels, cokernels, images and extensions of coherent sheaves
of modules are coherent: the coherent sheaves of modules form an abelian subcategory of
`X.Modules`.

## Hypotheses

`SheafOfModules.IsCoherent` is "quasi-coherent of finite type" (see the design note in
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`), not the notion of
[Stacks, 01BV]. The two agree over a locally Noetherian scheme, but not in general, and the
statements below record exactly the hypotheses their proofs need:

* the kernel and the image require `[IsLocallyNoetherian X]`: they are computed on an affine
  chart as a submodule of a finitely generated module, and this is finitely generated only over
  a Noetherian ring;
* the cokernel and extensions need no Noetherian hypothesis, since there the module of sections
  is a quotient, respectively an extension, of finitely generated modules;
* the quasi-coherence of the middle term of an extension is *not* proved here — over an affine
  scheme it amounts to the vanishing of `H¹` of a quasi-coherent sheaf — so
  `AlgebraicGeometry.Scheme.Modules.isCoherent_of_shortExact` assumes it.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isCoherent_kernel`
* `AlgebraicGeometry.Scheme.Modules.isCoherent_cokernel`
* `AlgebraicGeometry.Scheme.Modules.isCoherent_image`
* `AlgebraicGeometry.Scheme.Modules.isCoherent_of_shortExact`

together with the two corollaries `isCoherent_of_mono` and `isCoherent_of_epi` which say that a
quasi-coherent subsheaf, respectively quotient, of a coherent sheaf is coherent.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite SheafOfModules TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- **The kernel of a morphism of coherent sheaves of modules is coherent.** -/
theorem isCoherent_kernel [IsLocallyNoetherian X] (φ : M ⟶ N) (hM : M.IsCoherent)
    (hN : N.IsQuasicoherent) : (kernel φ).IsCoherent := by
  obtain ⟨hMq, -⟩ := (SheafOfModules.isCoherent_iff M).mp hM
  have := hN
  obtain ⟨ι, U, hU', hU, hfin⟩ := exists_isOpenCover_finite M hM
  refine isCoherent_of_isOpenCover _ U hU hU' (fun i ↦ ?_) (fun i ↦ ?_)
  · exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U i)).ringCatSheaf).prop_of_iso
      (PreservesKernel.iso (restrictFunctor (hU' i).fromSpec) φ).symm inferInstance
  · have hnoeth : IsNoetherianRing Γ(X, U i) :=
      IsLocallyNoetherian.component_noetherian ⟨U i, hU' i⟩
    have := hfin i
    have h := finite_moduleSpecΓ_kernel ((restrictFunctor (hU' i).fromSpec).map φ)
    exact h.equiv (moduleSpecΓFunctor.mapIso
      (PreservesKernel.iso (restrictFunctor (hU' i).fromSpec) φ)).symm.toLinearEquiv

/-- **The cokernel of a morphism of coherent sheaves of modules is coherent.** -/
theorem isCoherent_cokernel (φ : M ⟶ N) (hM : M.IsQuasicoherent) (hN : N.IsCoherent) :
    (cokernel φ).IsCoherent := by
  obtain ⟨hNq, -⟩ := (SheafOfModules.isCoherent_iff N).mp hN
  have := hM
  obtain ⟨ι, U, hU', hU, hfin⟩ := exists_isOpenCover_finite N hN
  refine isCoherent_of_isOpenCover _ U hU hU' (fun i ↦ ?_) (fun i ↦ ?_)
  · exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U i)).ringCatSheaf).prop_of_iso
      (PreservesCokernel.iso (restrictFunctor (hU' i).fromSpec) φ).symm inferInstance
  · have := hfin i
    have h := finite_moduleSpecΓ_cokernel ((restrictFunctor (hU' i).fromSpec).map φ)
    exact h.equiv (moduleSpecΓFunctor.mapIso
      (PreservesCokernel.iso (restrictFunctor (hU' i).fromSpec) φ)).symm.toLinearEquiv

/-- **The image of a morphism of coherent sheaves of modules is coherent.** -/
theorem isCoherent_image [IsLocallyNoetherian X] (φ : M ⟶ N) (hM : M.IsQuasicoherent)
    (hN : N.IsCoherent) : (Limits.image φ).IsCoherent := by
  obtain ⟨hCq, -⟩ := (SheafOfModules.isCoherent_iff (cokernel φ)).mp (isCoherent_cokernel φ hM hN)
  exact (SheafOfModules.isCoherent X.ringCatSheaf).prop_of_iso (Abelian.imageIsoImage φ)
    (isCoherent_kernel (cokernel.π φ) hN hCq)

/-- **Coherence is stable under extensions**: if the outer terms of a short exact sequence of
sheaves of modules are coherent and the middle term is quasi-coherent, then the middle term is
coherent. -/
theorem isCoherent_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : S.X₁.IsCoherent) (h₃ : S.X₃.IsCoherent) (h₂ : S.X₂.IsQuasicoherent) :
    S.X₂.IsCoherent := by
  obtain ⟨h₁q, -⟩ := (SheafOfModules.isCoherent_iff S.X₁).mp h₁
  obtain ⟨h₃q, -⟩ := (SheafOfModules.isCoherent_iff S.X₃).mp h₃
  have := h₂
  obtain ⟨ι, U, hU', hU, hf₁, hf₃⟩ := exists_isOpenCover_finite₂ S.X₁ S.X₃ h₁ h₃
  refine isCoherent_of_isOpenCover _ U hU hU' (fun i ↦ inferInstance) (fun i ↦ ?_)
  have q₁ : ((S.map (restrictFunctor (hU' i).fromSpec)).X₁).IsQuasicoherent :=
    (inferInstance : (S.X₁.restrict (hU' i).fromSpec).IsQuasicoherent)
  have q₂ : ((S.map (restrictFunctor (hU' i).fromSpec)).X₂).IsQuasicoherent :=
    (inferInstance : (S.X₂.restrict (hU' i).fromSpec).IsQuasicoherent)
  have q₃ : ((S.map (restrictFunctor (hU' i).fromSpec)).X₃).IsQuasicoherent :=
    (inferInstance : (S.X₃.restrict (hU' i).fromSpec).IsQuasicoherent)
  exact finite_moduleSpecΓ_of_shortExact (R := Γ(X, U i))
    (S := S.map (restrictFunctor (hU' i).fromSpec))
    (hS.map_of_exact (restrictFunctor (hU' i).fromSpec)) (hf₁ i) (hf₃ i)

/-- **A quasi-coherent subsheaf of a coherent sheaf of modules is coherent.** -/
theorem isCoherent_of_mono [IsLocallyNoetherian X] (φ : M ⟶ N) [Mono φ] (hM : M.IsQuasicoherent)
    (hN : N.IsCoherent) : M.IsCoherent :=
  (SheafOfModules.isCoherent X.ringCatSheaf).prop_of_iso (Limits.imageMonoIsoSource φ)
    (isCoherent_image φ hM hN)

/-- **A quasi-coherent quotient of a coherent sheaf of modules is coherent.** -/
theorem isCoherent_of_epi [IsLocallyNoetherian X] (φ : M ⟶ N) [Epi φ] (hM : M.IsCoherent)
    (hN : N.IsQuasicoherent) : N.IsCoherent := by
  obtain ⟨hMq, -⟩ := (SheafOfModules.isCoherent_iff M).mp hM
  obtain ⟨hkq, -⟩ := (SheafOfModules.isCoherent_iff (kernel φ)).mp (isCoherent_kernel φ hM hN)
  have hepi : Epi (Limits.image.ι φ) := epi_of_epi_fac (Limits.image.fac φ)
  exact (SheafOfModules.isCoherent X.ringCatSheaf).prop_of_iso
    (Abelian.coimageIsoImage' φ ≪≫
      @asIso _ _ _ _ (Limits.image.ι φ) (isIso_of_mono_of_epi (Limits.image.ι φ)))
    (isCoherent_cokernel (kernel.ι φ) hkq hM)

end AlgebraicGeometry.Scheme.Modules
