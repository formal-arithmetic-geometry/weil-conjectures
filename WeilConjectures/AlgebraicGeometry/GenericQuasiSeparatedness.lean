/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Properties

import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Module
import WeilConjectures.RingTheory.FinitelyPresentedSupportComplement
import WeilConjectures.RingTheory.GenericFiniteModulePresentation

/-! # Generic quasi-separatedness

Source: Stacks Project, Tag 052A, proof of generic flatness, last paragraph
(blueprint: lem-pur-generic-quasi-separatedness).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Localization of a quotient, expressed over the localized ring, transfers a finite
presentation of the module of fractions to the quotient by the extended ideal. -/
private theorem quotient_localized_finitePresentation
    {B : Type u} [CommRing B] (I : Ideal B) (s : B)
    [Module.FinitePresentation (Localization.Away s)
      (LocalizedModule.Away s (B ⧸ I))] :
    Module.FinitePresentation (Localization.Away s)
      ((Localization.Away s) ⧸ I.map (algebraMap B (Localization.Away s))) := by
  let S := Submonoid.powers s
  let L := Localization.Away s
  have heq : I.localized' L S (Algebra.linearMap B L) = I.map (algebraMap B L) := by
    rw [Submodule.localized'_eq_span, Ideal.map, Ideal.span, Algebra.coe_linearMap]
  let e := IsLocalizedModule.linearEquiv S
    (I.toLocalizedQuotient' L S (Algebra.linearMap B L))
    (LocalizedModule.mkLinearMap S (B ⧸ I))
  have ef : Module.FinitePresentation L (L ⧸ I.localized' L S (Algebra.linearMap B L)) :=
    Module.FinitePresentation.of_equiv (e.extendScalarsOfIsLocalization S L).symm
  rw [heq] at ef
  exact ef

/-- Any open subset of the spectrum of a finite type algebra over a domain becomes compact
on a principal shrinking of the base. Compactness persists on further principal shrinkings.

Source: Stacks Project, Tag 052A, chart-complement modules in the proof of generic flatness.
(blueprint: lem-pur-generic-quasi-separatedness)

Proof: write the closed complement as V(I), apply generic finite module presentation to
B/I, and identify its localization with the quotient by the extended ideal. The support
of that quotient is V(I B_a), whose complement is compact by finite presentation. Its
image under localization is U intersect D(a). Further principal shrinking intersects
this compact open with another compact basic open in the quasi-separated spectrum. -/
private theorem exists_isCompact_inter_basicOpen
    (R B : Type u) [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] (U : TopologicalSpace.Opens (PrimeSpectrum B)) :
    ∃ a : R, a ≠ 0 ∧ ∀ b : R, a ∣ b →
      IsCompact (U ⊓ PrimeSpectrum.basicOpen (algebraMap R B b) : Set (PrimeSpectrum B)) := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
    (U : Set (PrimeSpectrum B))ᶜ).mp U.isOpen.isClosed_compl
  obtain ⟨a, ha, hfp⟩ :=
    Module.Finite.exists_finitePresentation_localizedModule_powers R B (B ⧸ I)
  let s := algebraMap R B a
  let L := Localization.Away s
  let J := I.map (algebraMap B L)
  have : Module.FinitePresentation L (L ⧸ J) := quotient_localized_finitePresentation I s
  have hc := (Module.isClosed_support_and_isCompact_compl L (L ⧸ J)).2
  rw [Module.support_of_algebra] at hc
  change IsCompact (PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk J) : Set L))ᶜ at hc
  rw [Ideal.mk_ker] at hc
  have hpre : PrimeSpectrum.comap (algebraMap B L) ⁻¹' (U : Set (PrimeSpectrum B)) =
      (PrimeSpectrum.zeroLocus (J : Set L))ᶜ := by
    rw [← compl_compl (U : Set (PrimeSpectrum B)), hI, Set.preimage_compl,
      PrimeSpectrum.preimage_comap_zeroLocus]
    change _ = (PrimeSpectrum.zeroLocus (Ideal.span ((algebraMap B L) '' (I : Set B)) : Set L))ᶜ
    rw [PrimeSpectrum.zeroLocus_span]
  have hca : IsCompact
      (U ⊓ PrimeSpectrum.basicOpen (algebraMap R B a) : Set (PrimeSpectrum B)) := by
    have h := hc.image (PrimeSpectrum.continuous_comap (algebraMap B L))
    rw [← hpre, Set.image_preimage_eq_inter_range,
      PrimeSpectrum.localization_away_comap_range L s] at h
    exact h
  refine ⟨a, ha, fun b hab ↦ ?_⟩
  obtain ⟨c, rfl⟩ := hab
  simpa only [map_mul, PrimeSpectrum.basicOpen_mul, TopologicalSpace.Opens.coe_inf,
    Set.inf_eq_inter, Set.inter_assoc] using
    QuasiSeparatedSpace.inter_isCompact _ _
      (U ⊓ PrimeSpectrum.basicOpen (algebraMap R B a)).isOpen hca
      (PrimeSpectrum.basicOpen (algebraMap R B c)).isOpen
      (PrimeSpectrum.isCompact_basicOpen _)

/-- Transfer generic compactness from spectra of coordinate rings to affine schemes. -/
private theorem generic_compact_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsIntegral Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (U : X.Opens) :
    ∃ a : Γ(Y, ⊤), a ≠ 0 ∧ ∀ b : Γ(Y, ⊤), a ∣ b →
      IsCompact (U ⊓ f ⁻¹ᵁ Y.basicOpen b : Set X) := by
  let φ := f.appTop.hom
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := φ.toAlgebra
  have : Algebra.FiniteType Γ(Y, ⊤) Γ(X, ⊤) :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  obtain ⟨a, ha, hc⟩ := exists_isCompact_inter_basicOpen Γ(Y, ⊤) Γ(X, ⊤)
    (X.isoSpec.inv ⁻¹ᵁ U)
  refine ⟨a, ha, fun b hab ↦ ?_⟩
  have h := X.isoSpec.hom.homeomorph.isCompact_preimage.mpr (hc b hab)
  change IsCompact (X.isoSpec.hom ⁻¹ᵁ
    ((X.isoSpec.inv ⁻¹ᵁ U) ⊓ PrimeSpectrum.basicOpen (φ b)) : Set X) at h
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, X.isoSpec.hom_inv_id,
    Scheme.Hom.id_preimage, Scheme.map_PrimeSpectrum_basicOpen_of_affine] at h
  simpa only [Scheme.preimage_basicOpen_top, TopologicalSpace.Opens.coe_inf,
    Set.inf_eq_inter] using h

/-- On an affine integral base, shrink simultaneously for the finitely many intersections
of a finite affine cover, then apply the affine-cover criterion for quasi-separatedness. -/
private theorem exists_generic_qs_affine
    {X Y : Scheme.{u}} [IsAffine Y] [IsIntegral Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ W : Y.Opens, (W : Set Y).Nonempty ∧ QuasiSeparated (morphismRestrict f W) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let C := X.affineCover.finiteSubcover
  have hgen (i j : C.I₀) := generic_compact_affine (C.f i ≫ f)
    (C.f i ⁻¹ᵁ (C.f j).opensRange)
  choose a ha hc using hgen
  let b : Γ(Y, ⊤) := ∏ p : C.I₀ × C.I₀, a p.1 p.2
  have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p _ ↦ ha p.1 p.2)
  let W := Y.basicOpen b
  have hW : (W : Set Y).Nonempty := by
    rw [← TopologicalSpace.Opens.ne_bot_iff_nonempty, ne_eq, basicOpen_eq_bot_iff]
    exact hb
  let V : C.I₀ → (f ⁻¹ᵁ W).toScheme.Opens :=
    fun i ↦ (f ⁻¹ᵁ W).ι ⁻¹ᵁ (C.f i).opensRange
  have hcov : TopologicalSpace.IsOpenCover V :=
    .mk ((f ⁻¹ᵁ W).ι.iSup_preimage_eq_top C.iSup_opensRange)
  have hAff (i : C.I₀) : IsAffineOpen (V i) := by
    change IsAffineOpen ((f ⁻¹ᵁ Y.basicOpen b).ι ⁻¹ᵁ (C.f i).opensRange)
    rw [Scheme.preimage_basicOpen_top]
    exact (isAffineOpen_opensRange (C.f i)).ι_basicOpen_preimage (f.appTop b)
  have hComp (i j : C.I₀) : IsCompact (V i ∩ V j : Set (f ⁻¹ᵁ W).toScheme) := by
    have hd : a i j ∣ b := Finset.dvd_prod_of_mem _ (Finset.mem_univ (i, j))
    have h := (hc i j b hd).image (C.f i).continuous
    apply (f ⁻¹ᵁ W).ι.isOpenEmbedding.isCompact_iff.mpr
    convert h using 1
    ext x
    constructor
    · rintro ⟨z, ⟨hi, hj⟩, rfl⟩
      obtain ⟨y, hy⟩ := hi
      refine ⟨y, ⟨?_, ?_⟩, hy⟩
      · change C.f i y ∈ (C.f j).opensRange
        rw [hy]
        exact hj
      · change f (C.f i y) ∈ W
        rw [hy]
        exact z.prop
    · rintro ⟨y, ⟨hj, hw⟩, rfl⟩
      exact ⟨⟨C.f i y, hw⟩, ⟨⟨y, rfl⟩, hj⟩, rfl⟩
  have : QuasiSeparatedSpace (f ⁻¹ᵁ W).toScheme :=
    Scheme.quasiSeparatedSpace_of_isOpenCover V hcov hAff hComp
  exact ⟨W, hW, inferInstance⟩

/-- A finite type morphism to an integral scheme is quasi-separated over a nonempty open.
No Noetherianity or separatedness assumption is imposed on either scheme or the morphism.

Source: Stacks Project, Tag 052A, proof of generic flatness, last paragraph.
(blueprint: lem-pur-generic-quasi-separatedness)

Proof:
1. Choose a nonempty affine open Spec A in T. Integrality makes A a domain
   (def-pc-integral-scheme). Finite type (def-weil-finite-type-morphism) supplies a finite
   affine cover Spec B_i of its inverse image. For each pair i,j choose an ideal I_ij
   cutting out the complement of the intersection inside Spec B_i, and set M_ij = B_i/I_ij.
   These modules are cyclic; no finite generation of I_ij is required.
2. Apply lem-pur-generic-finite-module-presentation to each M_ij. Identify its
   localization with the quotient by the extended ideal, using the universal property of
   localized modules. Its support is the zero locus of that ideal. Thus
   lem-pur-finitely-presented-support-complement makes the chart intersection compact
   after a principal shrinking of the base. It stays compact on any further principal
   shrinking: intersect with another compact basic open in the affine chart.
3. Take the product a of the finitely many nonzero base elements from step 2. It is
   nonzero, so D(a) is nonempty; the empty product is 1. Each restricted chart is affine
   because its preimage of D(a) is a basic open. Step 2 makes each pairwise intersection
   compact, and open embeddings transfer this compactness to the restricted source.
4. Apply lem-weil-pbc-quasi-separated-affine-cover-criterion to this affine cover, including
   the empty source case, to obtain a quasi-separated source. Then clause (1) of
   lem-weil-pbc-qcqs-morphism-permanence makes the restricted morphism quasi-separated. -/
theorem exists_nonempty_open_quasiSeparated_restrict {Z T : Scheme.{u}}
    (h : Z ⟶ T) [LocallyOfFiniteType h] [QuasiCompact h] [IsIntegral T] :
    ∃ W : T.Opens, (W : Set T).Nonempty ∧ QuasiSeparated (morphismRestrict h W) := by
  classical
  let x : T := Classical.arbitrary T
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : IsAffine U.toScheme := hU
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨V, hV, hqs⟩ := exists_generic_qs_affine (h ∣_ U)
  refine ⟨U.ι ''ᵁ V, hV.image U.ι, ?_⟩
  exact (MorphismProperty.arrow_mk_iso_iff @QuasiSeparated
    (morphismRestrictRestrict h U V)).mp hqs

end AlgebraicGeometry
