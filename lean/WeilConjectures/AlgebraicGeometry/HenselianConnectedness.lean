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
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction

import Sheaf.AlgebraicGeometry.SteinFactorizationAffine
import Sheaf.RingTheory.HenselianPairPrimeConnected
import Sheaf.RingTheory.IntegralOverHenselianPair

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
  let J := Scheme.IdealSheafData.vanishingIdeal (⟨C, hC⟩ : TopologicalSpace.Closeds Y)
  let Z := J.subscheme
  let i : Z ⟶ Y := J.subschemeι
  have hi : Set.range i = C := J.range_subschemeι
  have hZi : IsIrreducible (Set.range i) := hi.symm ▸ hC'
  let : IrreducibleSpace (Set.range i) := isIrreducible_iff_irreducibleSpace.mp hZi
  let e : Z ≃ₜ Set.range i := i.isClosedEmbedding.isEmbedding.toHomeomorph
  let : IrreducibleSpace Z := e.irreducibleSpace_iff.mpr inferInstance
  let f := i ≫ p
  obtain ⟨hint, hproper, _, hfib⟩ := f.steinFactorization_affine
  let : IsProper Z.toSpecΓ := hproper
  have hsurj : Function.Surjective Z.toSpecΓ := by
    intro t
    obtain ⟨z, hz⟩ := (hfib t).2.nonempty
    exact ⟨z, hz⟩
  let : IrreducibleSpace (Spec Γ(Z, ⊤)) :=
    hsurj.irreducibleSpace Z.toSpecΓ.continuous
  let φ := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom
  let : Algebra A Γ(Z, ⊤) := φ.toAlgebra
  let : Algebra.IsIntegral A Γ(Z, ⊤) := algebraMap_isIntegral_iff.mp hint
  let K := I.map φ
  let : HenselianRing Γ(Z, ⊤) K := henselianRing_of_isIntegral A I Γ(Z, ⊤)
  have hbirr : IrreducibleSpace (PrimeSpectrum (Γ(Z, ⊤) : Type u)) := by
    change IrreducibleSpace (Spec Γ(Z, ⊤))
    infer_instance
  let : (_root_.nilradical (Γ(Z, ⊤) : Type u)).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hbirr
  have hK : _root_.IsConnected (PrimeSpectrum.zeroLocus (K : Set Γ(Z, ⊤))) := by
    have := PrimeSpectrum.connectedSpace_zeroLocus_sup_of_henselian K
      (_root_.nilradical (Γ(Z, ⊤) : Type u))
    have hconn := isConnected_iff_connectedSpace.mpr this
    simpa only [PrimeSpectrum.zeroLocus_sup, PrimeSpectrum.zeroLocus_nilradical,
      Set.univ_inter] using hconn
  have hfconn : _root_.IsConnected (Z.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus (K : Set Γ(Z, ⊤))) :=
    (Z.toSpecΓ.isClosedMap.isQuotientMap Z.toSpecΓ.continuous hsurj).isCoinducing
      |>.isConnected_preimage_of_isClosed (fun t ↦ (hfib t).2)
        (PrimeSpectrum.isClosed_zeroLocus _) hK
  have hfzero : f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) =
      Z.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus (K : Set Γ(Z, ⊤)) := by
    rw [← Scheme.toSpecΓ_steinFactorizationBase f, Scheme.Hom.comp_base, TopCat.coe_comp]
    rw [Set.preimage_comp]
    change Z.toSpecΓ ⁻¹' (PrimeSpectrum.comap φ ⁻¹' _) = _
    rw [PrimeSpectrum.preimage_comap_zeroLocus]
    rw [← PrimeSpectrum.zeroLocus_span, ← Ideal.map]
  rw [← hfzero] at hfconn
  have himage : i '' (f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) =
      C ∩ p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
    change i '' (i ⁻¹' (p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A))) = _
    rw [Set.image_preimage_eq_inter_range, hi, Set.inter_comm]
  rw [← himage]
  exact hfconn.image i i.continuous.continuousOn

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

end AlgebraicGeometry
