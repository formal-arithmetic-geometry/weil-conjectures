/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.AffineScheme

import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.Modules.QcqsSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs

/-!
# Quasi-coherent sections supported on a closed subset

Source: Stacks Project, Properties, Tag 07ZP,
lemma-sections-supported-on-closed-subset, (1)--(3)
(blueprint: lem-trf-supported-sections-quasi-coherent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private theorem res_zero_congr {X : Scheme.{u}} (F : X.Modules) {W A B : X.Opens}
    (hA : A ≤ W) (hB : B ≤ W) (h : A = B) (s : Γ(F, W)) :
    F.presheaf.map (homOfLE hA).op s = 0 ↔ F.presheaf.map (homOfLE hB).op s = 0 := by
  subst B
  rfl

private theorem res_res {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
    (hUV : V ≤ U) (hVW : W ≤ V) (s : Γ(F, U)) :
    F.presheaf.map (homOfLE hVW).op (F.presheaf.map (homOfLE hUV).op s) =
      F.presheaf.map (homOfLE (hVW.trans hUV)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private theorem supportedSections_exists {X : Scheme.{u}} (V : X.Opens) (F : X.Modules)
    [F.IsQuasicoherent]
    (hc : ∀ U : X.Opens, IsAffineOpen U → IsCompact ((U : Set X) ∩ (V : Set X))) :
    ∃ (K : X.Modules) (ι : K ⟶ F),
      (∀ W : X.Opens, Function.Injective (ι.app W) ∧ Set.range (ι.app W) =
        {s : Γ(F, W) | F.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op s = 0}) ∧
      K.IsQuasicoherent := by
  have : QuasiCompact V.ι := quasiCompact_iff_forall_isAffineOpen.mpr fun U hU ↦ by
    rw [Subtype.isCompact_iff]
    have he : (Subtype.val : V → X) '' (V.ι ⁻¹ᵁ U : Set V) =
        (U : Set X) ∩ (V : Set X) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨hy, y.2⟩
      · intro hx
        exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
    exact he.symm ▸ hc U hU
  have : ((pushforward V.ι).obj (F.restrict V.ι)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated V.ι (F.restrict V.ι)
  let φ : F ⟶ (pushforward V.ι).obj (F.restrict V.ι) :=
    (restrictAdjunction V.ι).unit.app F
  let K : X.Modules := kernel (C := SheafOfModules.{u} X.ringCatSheaf) φ
  let ι : K ⟶ F := kernel.ι (C := SheafOfModules.{u} X.ringCatSheaf) φ
  refine ⟨K, ι, ?_, isQuasicoherent_kernel φ⟩
  intro W
  refine ⟨injective_map_kernelι W φ, ?_⟩
  have hr := range_map_kernelι W φ
  change Set.range ((kernel.ι φ).app W) = {s | φ.app W s = 0} at hr
  refine hr.trans ?_
  ext s
  change F.presheaf.map (homOfLE (V.ι.image_preimage_le W)).op s = 0 ↔ _
  exact res_zero_congr F _ _ (by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]) s

private theorem exists_definingIdeal {X : Scheme.{u}} (Z : Closeds X) {U : X.Opens}
    (hU : IsAffineOpen U) (hc : IsCompact ((U : Set X) ∩ (Z : Set X)ᶜ)) :
    ∃ J : Ideal Γ(X, U), J.FG ∧
      ∀ x : U, (x.1 ∈ Z ↔ J ≤ (hU.isoSpec.hom x).asIdeal) := by
  let V : Set U := {x | x.1 ∉ Z}
  have hV : IsCompact V := by
    rw [Subtype.isCompact_iff]
    have he : (Subtype.val : U → X) '' V = (U : Set X) ∩ (Z : Set X)ᶜ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · intro hx
        exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
    exact he.symm ▸ hc
  let e := hU.isoSpec.hom.homeomorph
  obtain ⟨J, hJ, he⟩ := PrimeSpectrum.isCompact_isOpen_iff_ideal.mp
    ⟨hV.image e.continuous, e.isOpenMap _ (Z.isClosed.isOpen_compl.preimage
      continuous_subtype_val)⟩
  refine ⟨J, hJ, fun x ↦ ?_⟩
  have hx : e x ∈ e '' V ↔ x ∈ V := e.injective.mem_set_image
  rw [← he] at hx
  change ¬ J ≤ (hU.isoSpec.hom x).asIdeal ↔ ¬ x.1 ∈ Z at hx
  exact (not_iff_not.mp hx).symm

private theorem affine_mem_basicOpen_iff {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (a : Γ(X, U)) (x : U) :
    x.1 ∈ X.basicOpen a ↔ a ∉ (hU.isoSpec.hom x).asIdeal := by
  exact (congrArg (fun T : Opens U ↦ x ∈ T)
    (Scheme.Opens.toSpecΓ_preimage_basicOpen U a)).to_iff.symm

private theorem affine_supported_iff_ideal_power {X : Scheme.{u}} (Z : Closeds X)
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (J : Ideal Γ(X, U)) (hJ : J.FG)
    (hZ : ∀ x : U, (x.1 ∈ Z ↔ J ≤ (hU.isoSpec.hom x).asIdeal)) (m : Γ(F, U)) :
    F.presheaf.map (homOfLE (inf_le_left :
      U ⊓ ⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩ ≤ U)).op m = 0 ↔
      ∃ n : ℕ, ∀ a : Γ(X, U), a ∈ J ^ n → a • m = 0 := by
  let V : X.Opens := ⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩
  have hD (a : Γ(X, U)) (ha : a ∈ J) : X.basicOpen a ≤ U ⊓ V := by
    intro x hx
    have hxU := X.basicOpen_le a hx
    refine ⟨hxU, fun hxZ ↦ ?_⟩
    exact (affine_mem_basicOpen_iff hU a ⟨x, hxU⟩).mp hx ((hZ ⟨x, hxU⟩).mp hxZ ha)
  constructor
  · intro hm
    let I : Ideal Γ(X, U) := (Submodule.span Γ(X, U) ({m} : Set Γ(F, U))).annihilator
    have hrad : J ≤ I.radical := by
      intro a ha
      have hz : F.presheaf.map (homOfLE (X.basicOpen_le a)).op m = 0 := by
        rw [← res_res F inf_le_left (hD a ha), hm, map_zero]
      obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isCompact F hU.isCompact a m hz
      exact ⟨n, (Submodule.mem_annihilator_span_singleton m (a ^ n)).mpr hn⟩
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hJ
    exact ⟨n, fun a ha ↦ (Submodule.mem_annihilator_span_singleton m a).mp (hn ha)⟩
  · rintro ⟨n, hn⟩
    have hzero (a : J) : F.presheaf.map (homOfLE (X.basicOpen_le a.1)).op m = 0 := by
      have hk := congrArg (F.presheaf.map (homOfLE (X.basicOpen_le a.1)).op)
        (hn (a.1 ^ n) (Ideal.pow_mem_pow a.2 n))
      rw [map_smul, map_pow, map_zero] at hk
      have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a.1)).op a.1) :=
        X.toRingedSpace.isUnit_res_basicOpen a.1
      exact (hu.pow n).smul_eq_zero.mp hk
    let G : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
    refine G.eq_of_locally_eq' (fun a : J ↦ X.basicOpen a.1) (U ⊓ V)
      (fun a ↦ homOfLE (hD a.1 a.2)) ?_ _ _ (fun a ↦ ?_)
    · intro x hx
      have hnot : ¬ J ≤ (hU.isoSpec.hom ⟨x, hx.1⟩).asIdeal :=
        (hZ ⟨x, hx.1⟩).not.mp hx.2
      obtain ⟨a, ha, hpa⟩ := Set.not_subset.mp hnot
      exact Opens.mem_iSup.mpr ⟨⟨a, ha⟩,
        (affine_mem_basicOpen_iff hU a ⟨x, hx.1⟩).mpr hpa⟩
    · change F.presheaf.map _ (F.presheaf.map _ m) = F.presheaf.map _ 0
      rw [res_res, hzero a, map_zero]

/-- Sections supported on a closed subset with retrocompact complement form a quasi-coherent
subsheaf. On every affine open there is a finitely generated defining ideal, and for every such
ideal the supported sections are precisely the elements annihilated by some ideal power.

The subsheaf is specified by its injective inclusion and its image on every open, so the
existential presentation fixes the actual submodule of sections, not merely its isomorphism type.

Source: Stacks Project, Properties, Tag 07ZP,
lemma-sections-supported-on-closed-subset, (1)--(3)
(blueprint: lem-trf-supported-sections-quasi-coherent).

Proof following the node's five steps:
1. Vanishing off Z is preserved by restriction, addition and scalar multiplication. Gluing in F
   and uniqueness off Z construct the subsheaf K and its sectionwise injective inclusion.
2. On an affine U, retrocompactness gives a finite cover of U minus Z by basic opens D(f_i).
   The basic-open basis (lem-weil-pbc-spec-localization-away-basic-open) supplies this cover.
   The ideal generated by the f_i defines Z on U; the empty cover gives the zero ideal.
3. For any finitely generated defining ideal, apply the compact-section power-torsion lemma
   (pqf-lem-qcoh-compact-section-power-torsion) on U, compact by
   lem-weil-pbc-affine-scheme-qcqs, to obtain f_i^{n_i} m = 0 with positive n_i.
   Every monomial of degree sum n_i contains one of these powers, so J^{sum n_i} kills m.
   With no generators use exponent 1. Conversely J^n m = 0 implies vanishing on each D(f_i),
   where f_i is invertible, and hence off Z. Exponent 0 forces m = 0.
4. For the extension condition of pqf-lem-qcoh-principal-open-criterion, extend a supported
   section on D_W(a) to t on the affine W after multiplying by a power, using
   pqf-lem-qcoh-qcqs-section-power-extension and lem-weil-pbc-affine-scheme-qcqs.
   Its restriction off Z vanishes on D(a). The compact-section power-torsion lemma on the
   compact W minus Z supplies a further power making t supported on Z.
5. For the vanishing condition of that criterion, a supported section vanishing on D_W(a)
   is killed in F(W) by a power of a by the compact-section power-torsion lemma. Injectivity
   of K(W) into F(W) gives the same equality in K(W). The criterion proves quasi-coherence;
   steps 2 and 3 give the two affine assertions. -/
theorem exists_supportedSections_isQuasicoherent
    {X : Scheme.{u}} (Z : Closeds X) (F : X.Modules) [F.IsQuasicoherent]
    (hretro : ∀ (U : X.Opens), IsAffineOpen U →
      IsCompact ((U : Set X) ∩ (Z : Set X)ᶜ)) :
    ∃ (K : X.Modules) (ι : K ⟶ F),
      (∀ (W : X.Opens), Function.Injective (ι.app W) ∧
        Set.range (ι.app W) = {s : Γ(F, W) |
          F.presheaf.map
            (homOfLE (inf_le_left :
              W ⊓ ⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩ ≤ W)).op s = 0}) ∧
      K.IsQuasicoherent ∧
      (∀ (U : X.Opens) (hU : IsAffineOpen U),
        (∃ (J : Ideal Γ(X, U)), J.FG ∧
          ∀ (x : U), (x.1 ∈ Z ↔ J ≤ (hU.isoSpec.hom x).asIdeal)) ∧
        (∀ (J : Ideal Γ(X, U)), J.FG →
          (∀ (x : U), (x.1 ∈ Z ↔ J ≤ (hU.isoSpec.hom x).asIdeal)) →
          ∀ (m : Γ(F, U)), m ∈ Set.range (ι.app U) ↔
            ∃ (n : ℕ), ∀ (a : Γ(X, U)), a ∈ J ^ n → a • m = 0)) := by
  obtain ⟨K, ι, hι, hK⟩ := supportedSections_exists
    ⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩ F hretro
  refine ⟨K, ι, hι, hK, fun U hU ↦ ⟨exists_definingIdeal Z hU (hretro U hU), ?_⟩⟩
  intro J hJ hZ m
  rw [(hι U).2]
  exact affine_supported_iff_ideal_power Z F hU J hJ hZ m

end AlgebraicGeometry.Scheme.Modules
