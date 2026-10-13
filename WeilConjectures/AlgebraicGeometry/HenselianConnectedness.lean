/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian
public import Mathlib.Topology.Spectral.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Connectedness of closed fibres of proper schemes over a henselian pair

Let `(A, I)` be a henselian pair and `p : Y ⟶ Spec A` a proper morphism, with closed fibre
`Y₀ = p⁻¹(V(I))`. This file records the two classical inputs of the degree-zero comparison
`Γ(Y, F) ≅ Γ(Y₀, F|_{Y₀})`:

* (i) *finiteness*: in the Stein factorization `Y ⟶ Spec Γ(Y, 𝒪_Y) ⟶ Spec A`, the second map is
  finite. This is stated for a noetherian `A`, where it is the coherence of `p_* 𝒪_Y`;
* (ii) *connectedness*: every irreducible closed subset `C ⊆ Y` meets `Y₀` in a nonempty
  connected subset.

Together with the spectrality of `Y` and the closedness of `Y₀`, input (ii) is exactly the
hypothesis of the Zariski restriction criterion
`TopCat.Sheaf.bijective_unit_app_top` for the pair `(Y, Y₀)`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isFinite_steinFactorizationBase`: input (i).
- `AlgebraicGeometry.Scheme.Hom.isConnected_inter_preimage_zeroLocus`: input (ii).
- `AlgebraicGeometry.Scheme.Hom.spectralSpace_and_isClosed_and_isConnected_inter`: the
  hypotheses of the Zariski restriction criterion for `(Y, Y₀)`.

## References

- Stacks Project, Lemma 59.91.1, <https://stacks.math.columbia.edu/tag/0A0B>
- Stacks Project, Theorem 37.53.5, <https://stacks.math.columbia.edu/tag/03H2>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **Finiteness of the Stein factorization** (input (i) of the two classical inputs of
Stein connectedness): for a proper morphism `p : Y ⟶ Spec A` with `A` noetherian, the ring
`Γ(Y, 𝒪_Y)` is a finite `A`-algebra, i.e. the second map `Spec Γ(Y, 𝒪_Y) ⟶ Spec A` of the Stein
factorization is finite. For a general affine base this is not proved in the blueprint.
(blueprint: `thm-weil-pbc-stein-inputs`) -/
@[stacks 02O5]
theorem Scheme.Hom.isFinite_steinFactorizationBase {A : Type u} [CommRing A]
    [IsNoetherianRing A] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [IsProper p] :
    IsFinite p.steinFactorizationBase := by
  have := Modules.isGrothendieckAbelian Y
  have : IsNoetherianRing Γ(Spec (.of A), ⊤) :=
    isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  have : (SheafOfModules.unit Y.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  obtain ⟨e, he⟩ := Modules.exists_bijective_semilinearMap_sections_higherDirectImage_H p O 0
  have := Modules.finite_sections_higherDirectImage p O 0
  let := p.appTop.hom.toAlgebra
  let e' : Γ((Modules.higherDirectImage p 0).obj O, ⊤) →ₗ[Γ(Spec (.of A), ⊤)] Γ(Y, ⊤) :=
    { toFun x := Modules.H.zeroLinearEquiv O (e x)
      map_add' x y := by simp
      map_smul' a x := by
        rw [e.map_smulₛₗ, LinearEquiv.map_smul]
        rfl }
  have hp : p.appTop.hom.Finite :=
    Module.Finite.of_surjective e' ((Modules.H.zeroLinearEquiv O).surjective.comp he.2)
  rw [Scheme.Hom.steinFactorizationBase, IsFinite.SpecMap_iff, CommRingCat.hom_comp]
  exact hp.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2)

/-- Every nonempty closed subset `C` of a scheme proper over `Spec A` meets the
closed fibre over `V(I)` when `I` lies in the Jacobson radical: the image of `C` is closed, so
it contains a closed point of `Spec A`, i.e. a maximal ideal, which contains `I`. This is the
nonemptiness half of `AlgebraicGeometry.Scheme.Hom.isConnected_inter_preimage_zeroLocus`. -/
theorem Scheme.Hom.nonempty_inter_preimage_zeroLocus {A : Type u} [CommRing A]
    (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥) {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A))
    [IsProper p] {C : Set Y} (hC : IsClosed C) (hne : C.Nonempty) :
    (C ∩ p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)).Nonempty := by
  obtain ⟨x, ⟨y, hy, rfl⟩, hx⟩ :=
    (p.isClosedMap C hC).exists_closed_singleton (hne.image p)
  have hmax : (p y : PrimeSpectrum A).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 hx
  refine ⟨y, hy, ?_⟩
  change (I : Set A) ⊆ (p y : PrimeSpectrum A).asIdeal
  exact fun a ha ↦ Ideal.mem_sInf.mp (hI ha) ⟨bot_le, hmax⟩

/-- **Connectedness of the closed fibre** (input (ii) of the two classical inputs of Stein
connectedness): let `(A, I)` be a henselian pair and `p : Y ⟶ Spec A` proper. Every
irreducible closed subset `C ⊆ Y` meets the closed fibre `Y₀ = p⁻¹(V(I))` in a nonempty
connected subset. This is the Stein-factorization step of the henselian-pair comparison
[Stacks 0A0B].
(blueprint: `thm-weil-pbc-stein-inputs`) -/
@[stacks 0A0B]
theorem Scheme.Hom.isConnected_inter_preimage_zeroLocus {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [IsProper p]
    {C : Set Y} (hC : IsClosed C) (hC' : IsIrreducible C) :
    IsConnected (C ∩ p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) := by
  refine ⟨p.nonempty_inter_preimage_zeroLocus I HenselianRing.jac hC hC'.nonempty, ?_⟩
  -- The preconnectedness is the Stein-factorization step of Stacks 0A0B.
  sorry

/-- **Stein connectedness.** Let `(A, I)` be a henselian pair and `p : Y ⟶ Spec A` proper, with
closed fibre `Y₀ = p⁻¹(V(I))`. Then `Y` is a spectral space, `Y₀` is closed in `Y`, and every
irreducible closed subset of `Y` meets `Y₀` in a nonempty connected subset. These are the
hypotheses of the Zariski restriction criterion
`TopCat.Sheaf.bijective_unit_app_top` for the pair `(Y, Y₀)`. The
spectrality holds because `Y` is quasi-compact and quasi-separated, the closedness because
`V(I)` is closed, and the connectedness is the classical input
`AlgebraicGeometry.Scheme.Hom.isConnected_inter_preimage_zeroLocus`.
(blueprint: `lemma-weil-pbc-stein-connectedness`) -/
theorem Scheme.Hom.spectralSpace_and_isClosed_and_isConnected_inter {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [IsProper p] :
    SpectralSpace Y ∧ IsClosed (p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) ∧
      ∀ C : Set Y, IsClosed C → IsIrreducible C →
        IsConnected (C ∩ p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
  exact ⟨{}, (PrimeSpectrum.isClosed_zeroLocus _).preimage p.continuous,
    fun C hC hC' ↦ p.isConnected_inter_preimage_zeroLocus I hC hC'⟩

/-- **An open containing the closed fibre of a proper scheme over a complete base is
everything.** Let `A` be `I`-adically complete, `f : Y ⟶ Spec A` and `g : X ⟶ Y` with
`g ≫ f` proper. An open `W ⊆ X` containing the preimage under `g` of the image of the closed
fibre `Y ×_A A/I ⟶ Y` is all of `X`: otherwise its closed complement would contain a point
over a maximal ideal, which contains `I ⊆ jac(A)`.
(blueprint: `lem-weil-pbc-etale-infinitesimal-restrictions-proper-open`) -/
@[stacks 0GS2]
theorem Scheme.Hom.eq_top_of_preimage_range_subset_of_isAdicComplete {A : Type u} [CommRing A]
    (I : Ideal A) [IsAdicComplete I A] {X Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) (g : X ⟶ Y)
    [IsProper (g ≫ f)] (W : X.Opens)
    (hW : g ⁻¹' Set.range
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⊆ W) :
    W = ⊤ := by
  by_contra hne
  have hne' : ((W : Set X)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    exact fun h' ↦ hne (SetLike.coe_injective (h'.trans TopologicalSpace.Opens.coe_top.symm))
  obtain ⟨x, hxW, hx⟩ := (g ≫ f).nonempty_inter_preimage_zeroLocus I
    (IsAdicComplete.le_jacobson_bot I) W.isOpen.isClosed_compl hne'
  refine hxW (hW ?_)
  have hq : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
      PrimeSpectrum.zeroLocus (I : Set A) := by
    have := range_comap_of_surjective (A ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker] at this
    exact this
  change g x ∈ Set.range (Limits.pullback.fst f _)
  rw [Scheme.Pullback.range_fst, hq]
  exact hx

end AlgebraicGeometry
