/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
import Sheaf.AlgebraicGeometry.CoherentSerreVanishing
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import WeilConjectures.AlgebraicGeometry.TensorPowerSectionOpenRestrictionN
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison

/-!
# Relative Serre vanishing

Source: Stacks Project, Cohomology of Schemes, Tag 02O1, lemma-kill-by-twisting
(blueprint: lem-pc-relative-kill-by-twisting).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Higher direct images of a coherent quasi-coherent module vanish after sufficiently
large twists by an invertible module ample over every affine open of the Noetherian base.
The witness in `hL` supplies the invertibility instance required by `IsAmple` for the
restriction; it adds no geometric condition beyond invertibility of that restriction.
The degree-zero tensor power is the structure module, and a nonnegative threshold suffices.
Source: Stacks Project, Cohomology of Schemes, Tag 02O1, lemma-kill-by-twisting
(blueprint: lem-pc-relative-kill-by-twisting).

Proof:
1. Restrict to an affine open V of S. Properness survives this base change
   (lem-pc-proper-base-change); the restricted morphism is separated and finite type
   (def-weil-proper-morphism). Its base is affine Noetherian, its module coherent, and
   its invertible module ample, so lem-weil-pbc-coherent-serre-vanishing applies.
2. This gives a bound n_V for all positive cohomological degrees. The affine-base
   comparison (lem-pc-cohomology-sections-affine-base) identifies these cohomology groups
   with sections of the higher direct images. Those images are quasi-coherent
   (lem-pc-finite-support-hi), hence zero when their affine global sections vanish
   (lem-weil-pbc-affine-tilde-gamma-adjunction).
3. The ordinary open base-change comparison (lem-pc-sections-open-base-change) identifies
   the restriction of each higher direct image with the higher direct image on X_V.
   Thus each restriction vanishes above its bound n_V, in every positive degree.
4. Take a finite affine cover of the Noetherian base and the maximum of its bounds
   (zero for an empty cover). Vanishing on this cover gives vanishing of the sheaf. -/
theorem exists_isZero_higherDirectImage_tensorPow_of_relatively_ample
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (L : X.Modules) [L.IsInvertible]
    (hL : ∀ V : S.Opens, IsAffineOpen V →
      ∃ h : (L.restrict (f ⁻¹ᵁ V).ι).IsInvertible,
        @IsAmple (f ⁻¹ᵁ V).toScheme (L.restrict (f ⁻¹ᵁ V).ι) h) :
    letI : EnoughInjectives X.Modules :=
      (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
      IsZero ((higherDirectImage f p).obj (F ⊗ L.tensorPow n)) := by
  classical
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  have key (t : S) : ∃ U : S.Opens, ∃ n₀ : ℕ, t ∈ U ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
        IsZero (((higherDirectImage f p).obj (F ⊗ L.tensorPow n)).restrict U.ι) := by
    obtain ⟨V, hV, htV, -⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens)
        (show t ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨hInv, hAmp⟩ := hL V hV
    let := hInv
    let A := Γ(S, V)
    let : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    let g : (f ⁻¹ᵁ V).toScheme ⟶ Spec (.of A) := (f ∣_ V) ≫ hV.isoSpec.hom
    let : IsProper g := inferInstance
    have := isGrothendieckAbelian (f ⁻¹ᵁ V).toScheme
    have hFr : RingedSpace.IsCoherent (f ⁻¹ᵁ V).toScheme.toRingedSpace
        (F.restrict (f ⁻¹ᵁ V).ι) :=
      (coherent_module_local_on_open_cover X F PUnit (fun _ ↦ ⊤) (by simp)).1 hF _
    obtain ⟨n₀, hn₀⟩ := exists_isZero_moduleCohomology_tensorPow_of_ample A g
      (F.restrict (f ⁻¹ᵁ V).ι) hFr (L.restrict (f ⁻¹ᵁ V).ι) hAmp
    refine ⟨V, n₀, htV, ?_⟩
    intro n hn p hp
    have hz := (hn₀ p n hp hn).of_iso
      ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).mapIso
        (openRestrictionNumeratorIso (f ⁻¹ᵁ V).ι F L n))
    let : Subsingleton ((RingedSpace.moduleCohomology
        (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
          ((F ⊗ L.tensorPow n).restrict (f ⁻¹ᵁ V).ι)) :=
      ModuleCat.subsingleton_of_isZero hz
    obtain ⟨a, _⟩ := exists_moduleCohomology_source_comparison (f ⁻¹ᵁ V).toScheme p
    let : Subsingleton (((F ⊗ L.tensorPow n).restrict (f ⁻¹ᵁ V).ι).H p) :=
      (a _).symm.toEquiv.injective.subsingleton
    have : (F ⊗ L.tensorPow n).IsQuasicoherent := isQuasicoherent_tensorObj _ _
    have hzg := isZero_higherDirectImage_of_subsingleton_H g
      ((F ⊗ L.tensorPow n).restrict (f ⁻¹ᵁ V).ι) p inferInstance
    have sq : IsPullback (f ⁻¹ᵁ V).ι g f hV.fromSpec := by
      refine (isPullback_morphismRestrict f V).flip.of_iso (Iso.refl _) (Iso.refl _)
        hV.isoSpec (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · simp [g]
      · simp
      · simp [IsAffineOpen.isoSpec_hom_fromSpec]
    obtain ⟨e⟩ := nonempty_higherDirectImage_iso_restrict f (F ⊗ L.tensorPow n)
      hV.fromSpec (f ⁻¹ᵁ V).ι g sq p
    have hzpb : IsZero ((higherDirectImage g p).obj
        ((pullback (f ⁻¹ᵁ V).ι).obj (F ⊗ L.tensorPow n))) :=
      hzg.of_iso ((higherDirectImage g p).mapIso
        ((restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app (F ⊗ L.tensorPow n))).symm
    have hr := isZero_restrict_opensRange_of_isZero_restrict hV.fromSpec
      (hzpb.of_iso e.symm)
    rwa [hV.opensRange_fromSpec] at hr
  choose U nU htU hvan using key
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun t ↦ (U t : Set S))
    (fun t ↦ (U t).isOpen) (by
      intro t ht
      exact Set.mem_iUnion.2 ⟨t, htU t⟩)
  refine ⟨s.sup nU, ?_⟩
  intro n hn p hp
  apply isZero_of_forall_exists_isZero_restrict
  intro t
  obtain ⟨t', ht', htt'⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ t))
  refine ⟨U t', htt', hvan t' n ?_ p hp⟩
  exact (Finset.le_sup ht').trans hn

end AlgebraicGeometry.Scheme.Modules
