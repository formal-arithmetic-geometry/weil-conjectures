/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.WeilSheaf.ArtinSchreierTrace
public import WeilConjectures.WeilSheaf.StalkUpperStar

/-!
# The local Frobenius of the Artin–Schreier sheaves

Let `k₀` be a finite field and `ψ` an additive character of `k₀` with values in `ℚ̄_ℓ`. The
Artin–Schreier sheaf `ℒ_{ψ(a x)}` (`AlgebraicGeometry.artinSchreier`) has one-dimensional
stalks: after pullback along the Artin–Schreier cover `ĀS` the `ψ`-isotypic component `ℒ_ψ` of
`AS_* ℚ̄_ℓ` becomes `ℚ̄_ℓ`, and every geometric point of the line lifts through the étale
surjection `ĀS`. Its local Frobenius at a closed point `x` is therefore the scalar given by its
trace, the value `ψ(Tr(a x))` of the trace function
(`AlgebraicGeometry.WeilSheaf.traceFunction_artinSchreier`), a root of unity. In particular
`ℒ_{ψ(a x)}` is punctually `ι`-pure of weight zero, and so is the Fourier kernel `μ^* ℒ_ψ`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.finrank_stalk_artinSchreier`: the stalks of `ℒ_{ψ(a x)}` are
  lines.
- `AlgebraicGeometry.WeilSheaf.exists_frobeniusEnd_stalk_artinSchreier`: at a closed point `x`
  the local Frobenius of `ℒ_{ψ(a x)}` is multiplication by `ψ(c)` for some `c ∈ k₀` which does
  not depend on `ψ`.
- `AlgebraicGeometry.isPunctuallyPureOfWeight_artinSchreier` (blueprint: `lem-fd-as-purity`):
  `ℒ_{ψ(a x)}` is punctually `ι`-pure of weight zero.
- `AlgebraicGeometry.isPunctuallyPureOfWeight_fourierKernel`: so is the Fourier kernel.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

open scoped ProEtale

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- The global sections of a free `ℓ`-adic sheaf `ℚ̄_ℓⁿ` on the spectrum of a field form an
`n`-dimensional `ℚ̄_ℓ`-vector space. -/
lemma finrank_globalSections_of_iso_biproduct {K : Type u} [Field K]
    {M : AdicSheaf l (Spec (.of K))} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of K))) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).obj M.X)) =
      n := by
  have : (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l)).Additive :=
    Functor.additive_of_preserves_binary_products _
  let G := Sheaf.Γ (Scheme.ProEt.topology (Spec (.of K))) (WeilCoefficients.{u} l) ⋙
    WeilCoefficients.toModuleCat l
  let e' : G.obj M.X ≅ ModuleCat.of _ (Fin n → G.obj (adicConstantSheaf l (Spec (.of K)))) :=
    G.mapIso ((AdicSheaf.forget _).mapIso e ≪≫
      (AdicSheaf.forget _).mapBiproduct (fun _ : Fin n ↦ AdicSheaf.unit l (Spec (.of K)))) ≪≫
      G.mapBiproduct (fun _ : Fin n ↦ adicConstantSheaf l (Spec (.of K))) ≪≫
      ModuleCat.biproductIsoPi (fun _ : Fin n ↦ G.obj (adicConstantSheaf l (Spec (.of K))))
  have : FiniteDimensional (PadicAlgCl l) (G.obj (adicConstantSheaf l (Spec (.of K)))) :=
    finiteDimensional_globalSections_adicConstantSheaf K
  have h1 : Module.finrank (PadicAlgCl l) (G.obj (adicConstantSheaf l (Spec (.of K)))) = 1 :=
    finrank_globalSections_adicConstantSheaf _
  refine e'.toLinearEquiv.finrank_eq.trans ?_
  simp [Module.finrank_pi_fintype, h1]

end ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

set_option synthInstance.maxHeartbeats 200000 in
-- Instance search for the (co)kernels in the category of sheaves of modules is slow.
/-- After pullback along the Artin–Schreier cover `ĀS`, the `ψ`-isotypic component `ℒ_ψ` of
`AS_* ℚ̄_ℓ` becomes the constant sheaf `ℚ̄_ℓ`: the projector `e_ψ` factors there as averaging
followed by splitting (see `AlgebraicGeometry.WeilSheaf.isLisse_image_artinSchreierIdempotent`).
-/
lemma affineLine.nonempty_adicUpperStar_image_artinSchreierIdempotent_iso
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty ((ĀS)^*ᵃ[l].obj (image (WeilSheaf.artinSchreierIdempotent ψ)).obj.carrier ≅
      ⨁ fun _ : Fin 1 ↦ ProEtale.AdicSheaf.unit l
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  let Φ := ObjectProperty.ι (WeilSheaf.objectProperty k₀ l (affineLine k₀)) ⋙
    IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l (affineLine k₀))
  have := ObjectProperty.preservesKernels_ι _ (cokernel.π (WeilSheaf.artinSchreierIdempotent ψ))
  have := ObjectProperty.preservesCokernels_ι _ (WeilSheaf.artinSchreierIdempotent ψ)
  have : HasColimitsOfShape WalkingParallelPair
      (ProEtale.AdicSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    inferInstance
  have : HasLimitsOfShape WalkingParallelPair
      (ProEtale.AdicSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
    inferInstance
  have hfac := affineLine.artinSchreierAverageModHom_splitModHom_of_restriction ψ
    (Φ.map (WeilSheaf.artinSchreierIdempotent ψ))
    (affineLine.restriction_map_artinSchreierIdempotent ψ)
  have hab := affineLine.artinSchreierSplitModHom_averageModHom (l := l) ψ
  have : IsSplitEpi (affineLine.artinSchreierAverageModHom l ψ) := ⟨⟨_, hab⟩⟩
  have : IsSplitMono (affineLine.artinSchreierSplitModHom l ψ) := ⟨⟨_, hab⟩⟩
  exact ⟨(ĀS)^*ᵃ[l].mapIso (Φ.mapIso (Abelian.imageIsoImage _).symm ≪≫
    Abelian.PreservesImage.iso Φ _ ≪≫ Abelian.imageIsoImage _) ≪≫
    ((ĀS)^*ᵃ[l].mapIso (Abelian.imageIsoImage _).symm ≪≫
    Abelian.PreservesImage.iso _ _ ≪≫ Abelian.imageIsoImage _) ≪≫
      (image.isoStrongEpiMono _ _ hfac).symm ≪≫
      (biproduct.isoProduct (fun _ : Fin 1 ↦ ProEtale.AdicSheaf.unit l
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≪≫ productUniqueIso _).symm⟩

namespace WeilSheaf

/-- The stalks of the `ψ`-isotypic component `ℒ_ψ` of `AS_* ℚ̄_ℓ` at all geometric points are
lines: the geometric point lifts through the étale surjection `ĀS`, after pullback along which
`ℒ_ψ` becomes `ℚ̄_ℓ`. -/
lemma finrank_stalkObj_image_artinSchreierIdempotent (ψ : AddChar k₀ (PadicAlgCl l))
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((image (artinSchreierIdempotent ψ)).stalkObj s)) = 1 := by
  obtain ⟨t, rfl⟩ := ProEtale.exists_comp_eq_of_weaklyEtale ĀS s
    ((affineLine.geometricArtinSchreierMap k₀).surjective _)
  obtain ⟨e⟩ := affineLine.nonempty_adicUpperStar_image_artinSchreierIdempotent_iso (l := l) ψ
  obtain ⟨e'⟩ := ProEtale.nonempty_upperStar_iso_biproduct t
    ⟨ProEtale.adicUpperStarUnitIso l t⟩ e
  refine ((WeilCoefficients.linearEquivOfIso ((Sheaf.Γ _ _).mapIso
    ((ProEtale.upperStarComp _ t ĀS).app _))).finrank_eq).trans ?_
  exact ProEtale.finrank_globalSections_of_iso_biproduct e'

end WeilSheaf

end AlgebraicGeometry
