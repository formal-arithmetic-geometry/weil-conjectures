/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
import all WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
public import WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
public import WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
import all WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
public import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.AlgebraicGeometry.SmoothSectionCentredCoordinates.SmoothSectionAffineCoordinates
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionReesMapComposition
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Section.SectionEtaleOpenCancellation
import all WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionEtaleFunctorial
import all WeilConjectures.AlgebraicGeometry.Section.SectionLocalityBaseChange

/-! # Naturality of the normalized DNC comparison

Source: latest blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-the-orientation-from-the-diagonal/sk-lem-lem-sp-dnc-naturality.{md,proof.md}
(blueprint: sk-lem-lem-sp-dnc-naturality).

Finite coefficients are read on the small etale site, as permitted by sk-def-sf-categories.
The family is the actual extended-Rees family, and all exceptional maps are the existing
counit mates or counit-normalized composite-adjunction isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Scheme
open Scheme.AffineZariskiSite Opposite

namespace AlgebraicGeometry.Etale.DncNaturality

/-- A smooth section pair in the standing separated finite-type field setting.
This record contains only geometry, with the closed section and its retraction equation.
Source: sk-lem-lem-sp-dnc-naturality, standing hypotheses
(blueprint: sk-lem-lem-sp-dnc-naturality). -/
structure Pair (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (S : Over (Spec (.of D.k))) where
  total : Over (Spec (.of D.k))
  map : total ⟶ S
  sect : S ⟶ total
  retraction : sect ≫ map = 𝟙 S
  [total_finite_type : LocallyOfFiniteType total.hom]
  [total_quasi_compact : QuasiCompact total.hom]
  [total_separated : IsSeparated total.hom]
  [smooth : SmoothOfRelativeDimension d map.left]
  [separated : IsSeparated map.left]
  [quasi_compact : QuasiCompact map.left]
  [closed : IsClosedImmersion sect.left]

attribute [instance] Pair.total_finite_type Pair.total_quasi_compact Pair.total_separated
  Pair.smooth Pair.separated Pair.quasi_compact Pair.closed

variable {D : WeilConjectures.FiniteFieldDatum.{u}} {d : ℕ}
  {S S' S'' : Over (Spec (.of D.k))}
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
  [LocallyOfFiniteType S'.hom] [QuasiCompact S'.hom] [IsSeparated S'.hom]
  [LocallyOfFiniteType S''.hom] [QuasiCompact S''.hom] [IsSeparated S''.hom]

/-- The standing geometry as the existing exceptional-section-pair record.
All Noetherian and compactifiability instances follow from finite type and separatedness.
Source: sk-lem-lem-sp-dnc-naturality, standing hypotheses
(blueprint: sk-lem-lem-sp-dnc-naturality). -/
def Pair.exceptional (P : Pair D d S) : ExceptionalSectionPair S.left d := by
  letI := SmoothOfRelativeDimension.smooth d P.map.left
  letI : IsNoetherian S.left := isNoetherian_of_locallyOfFiniteType S.hom
  letI : IsNoetherian P.total.left := isNoetherian_of_locallyOfFiniteType P.total.hom
  letI : HasCompactification P.map.left :=
    (NagataCompactification P.map.left).hasCompactification
  exact { total := P.total.left, map := P.map.left, sect := P.sect.left
          section_map := congrArg Over.Hom.left P.retraction }

/-- The existing actual Rees family with its canonical zero and one fibres.
Source: sk-lem-lem-sp-dnc-naturality, the geometry and the two fibre restrictions
(blueprint: sk-lem-lem-sp-dnc-naturality). -/
def Pair.family (P : Pair D d S) : ExceptionalSectionFamily S.left d := by
  let Q := P.exceptional
  letI : QuasiCompact Q.map := P.quasi_compact
  letI := Q.base_noetherian
  letI := Q.total_noetherian
  letI := Scheme.Hom.hasCompactification_deformationSpaceProj Q.map Q.sect d Q.section_map
  letI := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d Q.map Q.sect
    Q.section_map
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj Q.map Q.sect) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      (Scheme.Hom.isPullback_normalConeToDeformationSpace Q.map Q.sect) inferInstance
  letI := SmoothOfRelativeDimension.smooth d (Scheme.Hom.normalConeProj Q.map Q.sect)
  letI : IsSeparated (Scheme.Hom.normalConeProj Q.map Q.sect) :=
    MorphismProperty.of_isPullback (P := @IsSeparated)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace Q.map Q.sect) inferInstance
  letI : QuasiCompact (Scheme.Hom.normalConeProj Q.map Q.sect) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace Q.map Q.sect) inferInstance
  letI : HasCompactification (Scheme.Hom.normalConeProj Q.map Q.sect) :=
    (NagataCompactification _).hasCompactification
  exact NoetherianSectionSpecialization.reesFamily d Q.map Q.sect Q.section_map

/-- A Cartesian change of a smooth pair. The section equation fixes the induced centre map.
Source: sk-lem-lem-sp-dnc-naturality (1)
(blueprint: sk-lem-lem-sp-dnc-naturality). -/
structure Change (P : Pair D d S) (P' : Pair D d S') (b : S' ⟶ S) where
  upper : P'.total ⟶ P.total
  square : IsPullback upper.left P'.map.left P.map.left b.left
  section_comm : P'.sect ≫ upper = b ≫ P.sect

/-- An etale map of pairs with scheme-theoretically Cartesian centres.
Source: sk-lem-lem-sp-dnc-naturality (2)
(blueprint: sk-lem-lem-sp-dnc-naturality). -/
structure EtaleChange (P P' : Pair D d S) where
  upper : P'.total ⟶ P.total
  map_comm : upper ≫ P.map = P'.map
  section_comm : P'.sect ≫ upper = P.sect
  centres : IsPullback P'.sect.left (𝟙 S.left) upper.left P.sect.left
  [etale : AlgebraicGeometry.Etale upper.left]

attribute [instance] EtaleChange.etale

private theorem sectionChange_ext {B B' : Scheme.{u}} {r : ℕ}
    {Q : ExceptionalSectionPair B r} {Q' : ExceptionalSectionPair B' r} {b : B' ⟶ B}
    (a a' : ExceptionalSectionChange Q Q' b) (h : a.upper = a'.upper) : a = a' := by
  cases a
  cases a'
  congr 1

private theorem familyChange_ext {B B' : Scheme.{u}} {r : ℕ}
    {Q : ExceptionalSectionFamily B r} {Q' : ExceptionalSectionFamily B' r} {b : B' ⟶ B}
    (a a' : ExceptionalFamilyBaseChange Q Q' b)
    (ha : a.ambient = a'.ambient) (hf : a.fibre = a'.fibre) : a = a' := by
  cases a
  cases a'
  congr 1

/-- The induced Rees and normal maps, including the canonical Cartesian identifications.
Proof: in centred smooth coordinates the Rees map is x_i=t*u_i, commuting with every
base change; quotient by t gives the associated-graded map. These affine formulas glue.
The three upper maps determine every field of the family change, proving uniqueness.
Source: sk-lem-lem-sp-dnc-naturality, proof, The geometry
(blueprint: sk-lem-lem-sp-dnc-naturality). -/
theorem Change.family_existsUnique {P : Pair D d S} {P' : Pair D d S'}
    {b : S' ⟶ S} (e : Change P P' b) :
    ∃! E : ExceptionalFamilyBaseChange P.family P'.family b.left,
      E.ambient.upper = SectionReesBaseChange.pairMap P.sect.left P'.sect.left
        e.upper.left b.left (congrArg Over.Hom.left e.section_comm) ∧
      (E.fibre true).upper = e.upper.left ∧
      (E.fibre false).upper ≫ P.sect.left.ker.normalConeToDeformationSpace =
        P'.sect.left.ker.normalConeToDeformationSpace ≫
          SectionReesBaseChange.pairMap P.sect.left P'.sect.left e.upper.left b.left
            (congrArg Over.Hom.left e.section_comm) := by
  have : IsNoetherian S.left := P.exceptional.base_noetherian
  have : IsNoetherian S'.left := P'.exceptional.base_noetherian
  have := SmoothOfRelativeDimension.smooth d P.map.left
  obtain ⟨s₀, hs₀closed, w₀, hs₀, hp₀, hc₀, _, _⟩ :=
    SectionReesBaseChange.base_change d P.map.left P.sect.left
      (congrArg Over.Hom.left P.retraction) b.left
  let i := e.square.isoPullback
  have hi : P'.sect.left ≫ i.hom = s₀ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, i, IsPullback.isoPullback_hom_fst]
      exact (congrArg Over.Hom.left e.section_comm).trans w₀.symm
    · simp only [Category.assoc, i, IsPullback.isoPullback_hom_snd]
      rw [hs₀, Scheme.Hom.baseChangeSection_snd]
      exact congrArg Over.Hom.left P'.retraction
  have hmap : i.hom ≫ pullback.snd P.map.left b.left = P'.map.left :=
    e.square.isoPullback_hom_snd
  have hsect : P'.sect.left ≫ (i.hom ≫ pullback.snd P.map.left b.left) = 𝟙 S'.left := by
    rw [hmap]
    exact congrArg Over.Hom.left P'.retraction
  have hcentres : IsPullback P'.sect.left (𝟙 S'.left) i.hom s₀ :=
    IsPullback.of_vert_isIso ⟨by simpa only [Category.id_comp] using hi⟩
  obtain ⟨hpᵢ, _, hcᵢ, _, _⟩ := SectionReesBaseChange.etale d
    (pullback.snd P.map.left b.left) s₀
    (by rw [hs₀]; exact Scheme.Hom.baseChangeSection_snd _ _ _ _)
    i.hom P'.sect.left hsect
    (hi.trans (Category.id_comp _).symm) hcentres
  let φ₀ := SectionReesBaseChange.pairMap P.sect.left s₀
    (pullback.fst P.map.left b.left) b.left w₀
  let φᵢ := SectionReesBaseChange.pairMap s₀ P'.sect.left i.hom (𝟙 S'.left)
    (hi.trans (Category.id_comp _).symm)
  let φ := SectionReesBaseChange.pairMap P.sect.left P'.sect.left
    e.upper.left b.left (congrArg Over.Hom.left e.section_comm)
  have hφ : φ = φᵢ ≫ φ₀ := by
    have h := WeilConjectures.PurityFiniteSetting.SectionRestriction.rees_pairMap_comp
      P.sect.left s₀ P'.sect.left (pullback.fst P.map.left b.left) i.hom
      b.left (𝟙 S'.left) w₀ (hi.trans (Category.id_comp _).symm)
    simpa only [i, IsPullback.isoPullback_hom_fst, Category.id_comp] using h
  have hc := SectionReesBaseChange.pairMap_compatible P.map.left P'.map.left
    P.sect.left P'.sect.left e.upper.left b.left
    (congrArg Over.Hom.left e.section_comm) e.square.w
  have hq₀ : IsPullback φ₀ (Scheme.Hom.deformationSpaceProj
      (pullback.snd P.map.left b.left) s₀)
      (Scheme.Hom.deformationSpaceProj P.map.left P.sect.left)
      (AffineSpace.map (ULift.{u} (Fin 1)) b.left) := by
    apply IsPullback.of_bot ?_ hc₀.1 (AffineSpace.isPullback_map b.left)
    simpa only [Scheme.Hom.deformationSpaceProj_over] using hp₀
  have : IsIso φᵢ := hpᵢ.isIso_fst_of_isIso
  have hφᵢ : φᵢ ≫ Scheme.Hom.deformationSpaceProj (pullback.snd P.map.left b.left) s₀ =
      Scheme.Hom.deformationSpaceProj P'.map.left P'.sect.left := by
    simpa only [AffineSpace.map_id, Category.comp_id, hmap] using hcᵢ.1
  have hqᵢ : IsPullback φᵢ (Scheme.Hom.deformationSpaceProj P'.map.left P'.sect.left)
      (Scheme.Hom.deformationSpaceProj (pullback.snd P.map.left b.left) s₀) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using hφᵢ⟩
  have hq : IsPullback φ P'.family.ambient.map P.family.ambient.map
      (AffineSpace.map (ULift.{u} (Fin 1)) b.left) := by
    have h := hqᵢ.paste_horiz hq₀
    simpa only [Pair.family, Pair.exceptional, NoetherianSectionSpecialization.reesFamily,
      ← hφ, Category.id_comp] using h
  obtain ⟨ν, _, _, hν, hπ, hz, _⟩ := hc.2.2.2
  have hqN : IsPullback ν (P'.family.fibre false).map (P.family.fibre false).map b.left := by
    have outer := (Scheme.Hom.isPullback_normalConeToDeformationSpace
      P'.map.left P'.sect.left).paste_horiz hq
    rw [AffineSpace.zeroSection_comp_map, ← hν] at outer
    exact IsPullback.of_right outer hπ
      (Scheme.Hom.isPullback_normalConeToDeformationSpace P.map.left P.sect.left)
  let E : ExceptionalFamilyBaseChange P.family P'.family b.left :=
    { ambient := { upper := φ, square := hq, section_comm := hc.2.1 }
      fibre := fun t ↦ match t with
        | false => { upper := ν, square := hqN, section_comm := hz }
        | true => { upper := e.upper.left, square := e.square
                    section_comm := congrArg Over.Hom.left e.section_comm }
      point_comm := by
        intro t
        cases t
        · exact (AffineSpace.zeroSection_comp_map b.left).symm
        · exact (AffineSpace.oneSection_comp_map b.left).symm
      fibre_comm := by
        intro t
        cases t
        · exact hν
        · exact hc.2.2.1.symm }
  refine ⟨E, ⟨rfl, rfl, hν⟩, ?_⟩
  intro F hF
  apply familyChange_ext
  · exact sectionChange_ext F.ambient E.ambient hF.1
  · funext t
    apply sectionChange_ext
    cases t
    · have : IsClosedImmersion P.sect.left.ker.normalConeToDeformationSpace :=
        MorphismProperty.of_isPullback (P := @IsClosedImmersion)
          (Scheme.Hom.isPullback_normalConeToDeformationSpace P.map.left P.sect.left).flip
          inferInstance
      exact (cancel_mono P.sect.left.ker.normalConeToDeformationSpace).mp
        (hF.2.2.trans hν.symm)
    · exact hF.2.1

/-- The canonical family change, selected from the uniquely specified Rees and graded maps.
Source: sk-lem-lem-sp-dnc-naturality (1)
(blueprint: sk-lem-lem-sp-dnc-naturality). -/
def Change.family {P : Pair D d S} {P' : Pair D d S'} {b : S' ⟶ S}
    (e : Change P P' b) : ExceptionalFamilyBaseChange P.family P'.family b.left :=
  (e.family_existsUnique).choose

private theorem etaleMap_ext {B : Scheme.{u}} {r : ℕ}
    {Q Q' : ExceptionalSectionPair B r} (a b : ExceptionalSectionEtaleMap Q Q')
    (h : a.upper = b.upper) : a = b := by
  cases a
  cases b
  congr 1

private theorem etaleFamily_ext {B : Scheme.{u}} {r : ℕ}
    {Q Q' : ExceptionalSectionFamily B r} (a b : ExceptionalFamilyEtaleMap Q Q')
    (ha : a.ambient = b.ambient) (hf : a.fibre = b.fibre) : a = b := by
  cases a
  cases b
  congr 1

/-- The etale Rees map and its normal-fibre map give the uniquely specified family map.
Proof: flat base change of Rees algebras gives the Cartesian etale deformation map.
On the zero fibre its degree-one map is the conormal isomorphism; hence the induced
linear normal-bundle map is an isomorphism. The fixed three maps determine the record.
Source: sk-lem-lem-sp-dnc-naturality, proof, The geometry
(blueprint: sk-lem-lem-sp-dnc-naturality). -/
theorem EtaleChange.family_existsUnique {P P' : Pair D d S} (e : EtaleChange P P') :
    ∃! E : ExceptionalFamilyEtaleMap P.family P'.family,
      E.ambient.upper = SectionReesBaseChange.pairMap P.sect.left P'.sect.left
        e.upper.left (𝟙 S.left)
          ((congrArg Over.Hom.left e.section_comm).trans (Category.id_comp _).symm) ∧
      (E.fibre true).upper = e.upper.left ∧
      (E.fibre false).upper ≫ P.sect.left.ker.normalConeToDeformationSpace =
        P'.sect.left.ker.normalConeToDeformationSpace ≫
          SectionReesBaseChange.pairMap P.sect.left P'.sect.left e.upper.left (𝟙 S.left)
            ((congrArg Over.Hom.left e.section_comm).trans (Category.id_comp _).symm) := by
  have : IsNoetherian S.left := P.exceptional.base_noetherian
  have : IsNoetherian P'.total.left := P'.exceptional.total_noetherian
  have := SmoothOfRelativeDimension.smooth d P.map.left
  have hm : e.upper.left ≫ P.map.left = P'.map.left :=
    congrArg Over.Hom.left e.map_comm
  have : IsSeparated (e.upper.left ≫ P.map.left) := hm ▸ P'.separated
  have : IsSeparated e.upper.left := IsSeparated.of_comp _ P.map.left
  have hw : P'.sect.left ≫ e.upper.left = (𝟙 S.left) ≫ P.sect.left :=
    (congrArg Over.Hom.left e.section_comm).trans (Category.id_comp _).symm
  have hs : P'.sect.left ≫ (e.upper.left ≫ P.map.left) = 𝟙 S.left := by
    rw [hm]
    exact congrArg Over.Hom.left P'.retraction
  obtain ⟨hp, he, hc, _, ν, hν, hνiso⟩ := SectionReesBaseChange.etale d
    P.map.left P.sect.left (congrArg Over.Hom.left P.retraction)
    e.upper.left P'.sect.left hs hw e.centres
  let φ := SectionReesBaseChange.pairMap P.sect.left P'.sect.left
    e.upper.left (𝟙 S.left) hw
  have hφ : φ ≫ P.family.ambient.map = P'.family.ambient.map := by
    simpa only [φ, Pair.family, NoetherianSectionSpecialization.reesFamily,
      Pair.exceptional, AffineSpace.map_id, Category.comp_id, hm] using hc.1
  have hσ : P'.family.ambient.sect ≫ φ = P.family.ambient.sect := by
    simpa only [φ, Pair.family, NoetherianSectionSpecialization.reesFamily,
      Pair.exceptional, AffineSpace.map_id, Category.id_comp] using hc.2.1
  have : IsClosedImmersion P.sect.left.ker.normalConeToDeformationSpace :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace P.map.left P.sect.left).flip
      inferInstance
  obtain ⟨μ, _, _, hμ, hπ, hz, _⟩ := hc.2.2.2
  have hμν : μ = ν :=
    (cancel_mono P.sect.left.ker.normalConeToDeformationSpace).mp (hμ.trans hν.symm)
  have hνπ : ν ≫ (P.family.fibre false).map = (P'.family.fibre false).map := by
    change ν ≫ Scheme.Hom.normalConeProj P.map.left P.sect.left =
      Scheme.Hom.normalConeProj P'.map.left P'.sect.left
    simpa only [hμν, Category.comp_id, hm] using hπ
  have hνσ : (P'.family.fibre false).sect ≫ ν = (P.family.fibre false).sect := by
    change P'.sect.left.normalConeZeroSection ≫ ν = P.sect.left.normalConeZeroSection
    simpa only [hμν, Category.id_comp] using hz
  have hcentres : IsPullback (𝟙 _) P'.family.ambient.sect P.family.ambient.sect φ := by
    have ht : IsPullback (𝟙 (AffineSpace (ULift.{u} (Fin 1)) S.left))
        (AffineSpace (ULift.{u} (Fin 1)) S.left ↘ S.left)
        (AffineSpace (ULift.{u} (Fin 1)) S.left ↘ S.left) (𝟙 S.left) :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    have ho := ht.paste_vert e.centres.flip
    rw [← Scheme.Hom.deformationSpaceSection_toBase,
      ← Scheme.Hom.deformationSpaceSection_toBase] at ho
    apply ho.of_bot ?_ hp
    change (𝟙 _) ≫ P.sect.left.deformationSpaceSection =
      P'.sect.left.deformationSpaceSection ≫ φ
    rw [Category.id_comp]
    exact hσ.symm
  have : IsSeparated φ := MorphismProperty.of_isPullback (P := @IsSeparated)
    hp.flip inferInstance
  have : QuasiCompact φ := MorphismProperty.of_isPullback (P := @QuasiCompact)
    hp.flip inferInstance
  let E : ExceptionalFamilyEtaleMap P.family P'.family :=
    { ambient := { upper := φ, map_comm := hφ, section_comm := hσ, centres := hcentres }
      fibre := fun t ↦ match t with
        | false => { upper := ν, map_comm := hνπ, section_comm := hνσ
                     centres := IsPullback.of_horiz_isIso ⟨by
                       simpa only [Category.id_comp] using hνσ.symm⟩ }
        | true => { upper := e.upper.left, map_comm := hm
                    section_comm := congrArg Over.Hom.left e.section_comm
                    centres := e.centres.flip }
      fibre_comm := by
        intro t
        cases t
        · exact hν
        · change e.upper.left ≫ Scheme.Hom.deformationSpaceOneFibre
            P.map.left P.sect.left =
              Scheme.Hom.deformationSpaceOneFibre P'.map.left P'.sect.left ≫ φ
          simpa only [hm] using hc.2.2.1.symm }
  refine ⟨E, ⟨rfl, rfl, hν⟩, ?_⟩
  intro F hF
  apply etaleFamily_ext
  · exact etaleMap_ext F.ambient E.ambient hF.1
  · funext t
    apply etaleMap_ext
    cases t
    · exact (cancel_mono P.sect.left.ker.normalConeToDeformationSpace).mp
        (hF.2.2.trans hν.symm)
    · exact hF.2.1

/-- The canonical etale map of the actual families, with all three geometric maps fixed.
Source: sk-lem-lem-sp-dnc-naturality (2)
(blueprint: sk-lem-lem-sp-dnc-naturality). -/
def EtaleChange.family {P P' : Pair D d S} (e : EtaleChange P P') :
    ExceptionalFamilyEtaleMap P.family P'.family := e.family_existsUnique.choose

private theorem coefficient_isUnit (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (X : Over (Spec (.of D.k))) (x : X.left) :
    IsUnit (ell : X.left.presheaf.stalk x) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have hchar : CharP D.k₀ D.p := by
    let : Fact D.p.Prime := ⟨D.prime⟩
    exact charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
  have := hchar
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hbase : IsUnit (ell : D.k) :=
    (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : ell.Prime)
      (by simpa only [ringChar.eq D.k D.p] using hell.symm)).isUnit
  simpa only [map_natCast] using hbase.map
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫ X.hom.appTop ≫
      X.left.presheaf.germ ⊤ x (by trivial)).hom

/-- The comparison kappa normalized by the canonical fibre map at one exists uniquely.
Proof: apply family constancy to the actual Rees family. In centred etale coordinates
it is constant; normalize by its one-fibre map and glue. The rank-one sheaf-Hom
calculation makes the one-fibre restriction faithful and proves uniqueness.
Source: sk-thm-dnc, normalized family comparison, used by sk-lem-lem-sp-dnc-naturality
(blueprint: sk-lem-lem-sp-dnc-naturality). -/
theorem Pair.normalized_existsUnique (P : Pair D d S) (ell n : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p) (hn : 1 ≤ n) :
    ∃! κ : sectionInvariant (NoetherianSectionSpecialization.Coeff ell n)
        P.family.ambient.map P.family.ambient.sect ≅
      (upperStar (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n))
        (AffineSpace (ULift.{u} (Fin 1)) S.left ↘ S.left)).leftDerivedFunctor.obj
        (sectionInvariant (NoetherianSectionSpecialization.Coeff ell n)
          (P.family.fibre true).map (P.family.fibre true).sect),
      P.family.IsNormalized (NoetherianSectionSpecialization.Coeff ell n) κ := by
  let Q := P.exceptional
  have : IsNoetherian S.left := Q.base_noetherian
  have : IsNoetherian P.total.left := Q.total_noetherian
  have : HasCompactification P.map.left := Q.compactifiable
  have := Scheme.Hom.hasCompactification_deformationSpaceProj
    P.map.left P.sect.left d (congrArg Over.Hom.left P.retraction)
  have : HasCompactification (Scheme.Hom.normalConeProj P.map.left P.sect.left) :=
    (P.family.fibre false).compactifiable
  have hS := coefficient_isUnit ell hell S
  have hV := coefficient_isUnit ell hell P.total
  have hregular : ∀ x : S.left, ∃ U : P.total.left.affineOpens,
      P.sect.left x ∈ U.1 ∧ ∃ r : Fin d → Γ(P.total.left, U.1),
        RingTheory.Sequence.IsWeaklyRegular Γ(P.total.left, U.1) (List.ofFn r) ∧
          Ideal.span (Set.range r) = P.sect.left.ker.ideal U := by
    intro x
    obtain ⟨c, hc⟩ := SmoothSectionCentredCoordinates.exists_affineChart d
      P.map.left P.sect.left (congrArg Over.Hom.left P.retraction) x
    refine ⟨c.U, c.sectionInto hc, c.x, c.regular.toIsWeaklyRegular, ?_⟩
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def,
      MvPolynomial.eval₂Hom_X'] using c.sectionIdeal
  have h := NoetherianSectionSpecialization.existsUnique_normalized ell n hn hS hV d
    P.map.left P.sect.left (congrArg Over.Hom.left P.retraction) hregular
  have hmap : P.family.fibreMap (NoetherianSectionSpecialization.Coeff ell n) true =
      NoetherianSectionSpecialization.atOne (NoetherianSectionSpecialization.Coeff ell n)
        P.map.left P.sect.left (congrArg Over.Hom.left P.retraction) :=
    NoetherianSectionSpecialization.comparison_eq
      (NoetherianSectionSpecialization.Coeff ell n) (P.family.restriction true)
  refine ⟨h.choose, ?_, ?_⟩
  · unfold ExceptionalSectionFamily.IsNormalized
    rw [hmap]
    exact h.choose_spec.1
  · intro κ hκ
    apply h.choose_spec.2 κ
    unfold ExceptionalSectionFamily.IsNormalized at hκ
    rw [hmap] at hκ
    exact hκ

/-- The uniquely normalized family comparison, rather than a choice of arbitrary trivialization.
Source: sk-thm-dnc, normalization at one (blueprint: sk-lem-lem-sp-dnc-naturality). -/
def Pair.kappa (P : Pair D d S) (ell n : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p) (hn : 1 ≤ n) :=
  (P.normalized_existsUnique ell n hell hn).choose

/-- The comparison alpha is the inverse zero restriction of the normalized family comparison.
Source: sk-thm-dnc, final specialization (blueprint: sk-lem-lem-sp-dnc-naturality). -/
def Pair.alpha (P : Pair D d S) (ell n : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p) (hn : 1 ≤ n) :=
  P.family.specialization (NoetherianSectionSpecialization.Coeff ell n)
    (P.kappa ell n hell hn)

/-- The prescribed exceptional base-change map, evaluated at either endpoint.
Source: sk-lem-lem-sp-dnc-naturality (1)
(blueprint: sk-lem-lem-sp-dnc-naturality). -/
def Change.endpoint (A : Type (u + 1)) [CommRing A] [Finite A]
    {P : Pair D d S} {P' : Pair D d S'} {b : S' ⟶ S}
    (e : Change P P' b) (t : Bool) := sectionExceptionalComparison A (e.family.fibre t)

/-- The prescribed endpoint identification obtained by composing the etale and structural
adjunctions, retaining the normalization by their composite counit.
Source: sk-lem-lem-sp-dnc-naturality (2)
(blueprint: sk-lem-lem-sp-dnc-naturality). -/
def EtaleChange.endpoint (A : Type (u + 1)) [CommRing A] [Finite A]
    {P P' : Pair D d S} (e : EtaleChange P P') (t : Bool) :=
  sectionExceptionalLocalityIso A (e.family.fibre t)

private theorem rees_id {V B : Scheme.{u}} (s : B ⟶ V) [IsClosedImmersion s]
    (w : s ≫ 𝟙 V = (𝟙 B) ≫ s) :
    SectionReesBaseChange.pairMap s s (𝟙 V) (𝟙 B) w = 𝟙 _ := by
  apply colimit.hom_ext
  intro U
  dsimp only [SectionReesBaseChange.pairMap, Scheme.IdealSheafData.deformationSpaceMap]
  rw [PullbackData.ι_comparison _ _ _ (le_refl U.1)]
  have he : (𝟙 V : V ⟶ V).appLE U.1 U.1 (le_refl U.1) = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    exact V.presheaf.map_id _
  simp only [Scheme.IdealSheafData.extendedReesPullbackData_map, he,
    CommRingCat.hom_id, Ideal.extendedReesAlgebraMap_id, CommRingCat.ofHom_id]
  rw [show Spec.map (𝟙 (CommRingCat.of (s.ker.siteIdeal U).extendedReesAlgebra)) =
    𝟙 _ from Scheme.Spec.map_id (.op _)]
  exact (Category.id_comp (colimit.ι
    (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U)).trans
      (Category.comp_id _).symm

omit [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom] in
private theorem normal_mono (P : Pair D d S) :
    Mono P.sect.left.ker.normalConeToDeformationSpace := by
  have : IsClosedImmersion P.sect.left.ker.normalConeToDeformationSpace :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace P.map.left P.sect.left).flip
      inferInstance
  infer_instance

private theorem commuting_comp {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}}
    (i₀ : X₀ ⟶ Y₀) (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂)
    (a : X₁ ⟶ X₀) (b : X₂ ⟶ X₁) (φ : Y₁ ⟶ Y₀) (ψ : Y₂ ⟶ Y₁)
    (ha : a ≫ i₀ = i₁ ≫ φ) (hb : b ≫ i₁ = i₂ ≫ ψ) :
    (b ≫ a) ≫ i₀ = i₂ ≫ (ψ ≫ φ) := by
  rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc]

private theorem base_fibre_id (P : Pair D d S) (e : Change P P (𝟙 S))
    (h : e.upper = 𝟙 P.total) (t : Bool) : (e.family.fibre t).upper = 𝟙 _ := by
  have hh := e.family_existsUnique.choose_spec.1
  have hu : e.upper.left = 𝟙 P.total.left := congrArg Over.Hom.left h
  cases t
  · have := normal_mono P
    apply (cancel_mono P.sect.left.ker.normalConeToDeformationSpace).mp
    erw [hh.2.2]
    simp only [hu, Over.id_left, rees_id, Category.comp_id, Category.id_comp]
  · exact hh.2.1.trans hu

private theorem etale_fibre_id (P : Pair D d S) (e : EtaleChange P P)
    (h : e.upper = 𝟙 P.total) (t : Bool) : (e.family.fibre t).upper = 𝟙 _ := by
  have hh := e.family_existsUnique.choose_spec.1
  have hu : e.upper.left = 𝟙 P.total.left := congrArg Over.Hom.left h
  cases t
  · have := normal_mono P
    apply (cancel_mono P.sect.left.ker.normalConeToDeformationSpace).mp
    erw [hh.2.2]
    simp only [hu, rees_id, Category.comp_id, Category.id_comp]
  · exact hh.2.1.trans hu

private theorem base_fibre_comp (P : Pair D d S) (P' : Pair D d S')
    (P'' : Pair D d S'') (b : S' ⟶ S) (c : S'' ⟶ S')
    (e : Change P P' b) (f : Change P' P'' c) (ef : Change P P'' (c ≫ b))
    (h : ef.upper = f.upper ≫ e.upper) (t : Bool) :
    (ef.family.fibre t).upper = (f.family.fibre t).upper ≫ (e.family.fibre t).upper := by
  have he := e.family_existsUnique.choose_spec.1
  have hf := f.family_existsUnique.choose_spec.1
  have hef := ef.family_existsUnique.choose_spec.1
  have hu : ef.upper.left = f.upper.left ≫ e.upper.left := congrArg Over.Hom.left h
  cases t
  · have := normal_mono P
    have hφ := WeilConjectures.PurityFiniteSetting.SectionRestriction.rees_pairMap_comp
      P.sect.left P'.sect.left P''.sect.left e.upper.left f.upper.left b.left c.left
      (congrArg Over.Hom.left e.section_comm) (congrArg Over.Hom.left f.section_comm)
    have hφ' :
        SectionReesBaseChange.pairMap P.sect.left P''.sect.left ef.upper.left (c ≫ b).left
            (congrArg Over.Hom.left ef.section_comm) =
          SectionReesBaseChange.pairMap P'.sect.left P''.sect.left f.upper.left c.left
              (congrArg Over.Hom.left f.section_comm) ≫
            SectionReesBaseChange.pairMap P.sect.left P'.sect.left e.upper.left b.left
              (congrArg Over.Hom.left e.section_comm) := by
      simpa only [Over.comp_left, ← hu] using hφ
    have hs := commuting_comp P.sect.left.ker.normalConeToDeformationSpace
      P'.sect.left.ker.normalConeToDeformationSpace P''.sect.left.ker.normalConeToDeformationSpace
      (e.family.fibre false).upper (f.family.fibre false).upper _ _ he.2.2 hf.2.2
    apply (cancel_mono P.sect.left.ker.normalConeToDeformationSpace).mp
    exact hef.2.2.trans
      ((congrArg (fun z ↦ P''.sect.left.ker.normalConeToDeformationSpace ≫ z) hφ').trans hs.symm)
  · erw [hef.2.1, he.2.1, hf.2.1, hu]

private theorem etale_fibre_comp (P P' P'' : Pair D d S)
    (e : EtaleChange P P') (f : EtaleChange P' P'') (ef : EtaleChange P P'')
    (h : ef.upper = f.upper ≫ e.upper) (t : Bool) :
    (ef.family.fibre t).upper = (f.family.fibre t).upper ≫ (e.family.fibre t).upper := by
  have he := e.family_existsUnique.choose_spec.1
  have hf := f.family_existsUnique.choose_spec.1
  have hef := ef.family_existsUnique.choose_spec.1
  have hu : ef.upper.left = f.upper.left ≫ e.upper.left := congrArg Over.Hom.left h
  cases t
  · have := normal_mono P
    have hφ := WeilConjectures.PurityFiniteSetting.SectionRestriction.rees_pairMap_comp
      P.sect.left P'.sect.left P''.sect.left e.upper.left f.upper.left
      (𝟙 S.left) (𝟙 S.left)
      ((congrArg Over.Hom.left e.section_comm).trans (Category.id_comp _).symm)
      ((congrArg Over.Hom.left f.section_comm).trans (Category.id_comp _).symm)
    have hφ' :
        SectionReesBaseChange.pairMap P.sect.left P''.sect.left ef.upper.left (𝟙 S.left)
            ((congrArg Over.Hom.left ef.section_comm).trans (Category.id_comp _).symm) =
          SectionReesBaseChange.pairMap P'.sect.left P''.sect.left f.upper.left (𝟙 S.left)
              ((congrArg Over.Hom.left f.section_comm).trans (Category.id_comp _).symm) ≫
            SectionReesBaseChange.pairMap P.sect.left P'.sect.left e.upper.left (𝟙 S.left)
              ((congrArg Over.Hom.left e.section_comm).trans (Category.id_comp _).symm) := by
      simpa only [← hu, Category.id_comp] using hφ
    have hs := commuting_comp P.sect.left.ker.normalConeToDeformationSpace
      P'.sect.left.ker.normalConeToDeformationSpace P''.sect.left.ker.normalConeToDeformationSpace
      (e.family.fibre false).upper (f.family.fibre false).upper _ _ he.2.2 hf.2.2
    apply (cancel_mono P.sect.left.ker.normalConeToDeformationSpace).mp
    exact hef.2.2.trans
      ((congrArg (fun z ↦ P''.sect.left.ker.normalConeToDeformationSpace ≫ z) hφ').trans hs.symm)
  · erw [hef.2.1, he.2.1, hf.2.1, hu]

private theorem mixed_fibre (P Q : Pair D d S) (P' Q' : Pair D d S') (b : S' ⟶ S)
    (e : Change P P' b) (f : Change Q Q' b)
    (h : EtaleChange P Q) (h' : EtaleChange P' Q')
    (w : f.upper ≫ h.upper = h'.upper ≫ e.upper) (t : Bool) :
    (f.family.fibre t).upper ≫ (h.family.fibre t).upper =
      (h'.family.fibre t).upper ≫ (e.family.fibre t).upper := by
  have he := e.family_existsUnique.choose_spec.1
  have hf := f.family_existsUnique.choose_spec.1
  have hh := h.family_existsUnique.choose_spec.1
  have hh' := h'.family_existsUnique.choose_spec.1
  have hw : f.upper.left ≫ h.upper.left = h'.upper.left ≫ e.upper.left :=
    congrArg Over.Hom.left w
  cases t
  · have := normal_mono P
    have ha := WeilConjectures.PurityFiniteSetting.SectionRestriction.rees_pairMap_comp
      P.sect.left Q.sect.left Q'.sect.left h.upper.left f.upper.left (𝟙 S.left) b.left
      ((congrArg Over.Hom.left h.section_comm).trans (Category.id_comp _).symm)
      (congrArg Over.Hom.left f.section_comm)
    have hb := WeilConjectures.PurityFiniteSetting.SectionRestriction.rees_pairMap_comp
      P.sect.left P'.sect.left Q'.sect.left e.upper.left h'.upper.left b.left (𝟙 S'.left)
      (congrArg Over.Hom.left e.section_comm)
      ((congrArg Over.Hom.left h'.section_comm).trans (Category.id_comp _).symm)
    have hleft :
        (f.family.fibre false).upper ≫ (h.family.fibre false).upper ≫
            P.sect.left.ker.normalConeToDeformationSpace =
          Q'.sect.left.ker.normalConeToDeformationSpace ≫
            SectionReesBaseChange.pairMap Q.sect.left Q'.sect.left f.upper.left b.left
              (congrArg Over.Hom.left f.section_comm) ≫
            SectionReesBaseChange.pairMap P.sect.left Q.sect.left h.upper.left (𝟙 S.left)
              ((congrArg Over.Hom.left h.section_comm).trans (Category.id_comp _).symm) := by
      erw [hh.2.2, ← Category.assoc, hf.2.2, Category.assoc]
    have hright :
        (h'.family.fibre false).upper ≫ (e.family.fibre false).upper ≫
            P.sect.left.ker.normalConeToDeformationSpace =
          Q'.sect.left.ker.normalConeToDeformationSpace ≫
            SectionReesBaseChange.pairMap P'.sect.left Q'.sect.left h'.upper.left (𝟙 S'.left)
              ((congrArg Over.Hom.left h'.section_comm).trans (Category.id_comp _).symm) ≫
            SectionReesBaseChange.pairMap P.sect.left P'.sect.left e.upper.left b.left
              (congrArg Over.Hom.left e.section_comm) := by
      erw [he.2.2, ← Category.assoc, hh'.2.2, Category.assoc]
    apply (cancel_mono P.sect.left.ker.normalConeToDeformationSpace).mp
    simp only [Category.assoc]
    erw [hleft, hright]
    congr 1
    erw [← ha, ← hb]
    simp only [hw, Category.id_comp, Category.comp_id]
  · erw [he.2.1, hf.2.1, hh.2.1, hh'.2.1, hw]

private theorem comparison_id
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {B : Scheme.{u}} {r : ℕ} (Q : ExceptionalSectionPair B r)
    (hInv : ∀ x : B, IsUnit (N : B.presheaf.stalk x))
    [HasInvertibleExponent A Q.total]
    (e : ExceptionalSectionChange Q Q (𝟙 B)) (h : e.upper = 𝟙 Q.total) :
    sectionExceptionalComparison A e =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).hom.app
        (sectionInvariant A Q.map Q.sect) := by
  have := section_comparison_isIso A Q Q (𝟙 B) e
  let a := sectionExceptionalComparison A e
  let I := (upperStar (ModuleCat.{u + 1} A) (𝟙 B)).leftDerivedFunctor
  let J := leftDerivedUpperStarId (ModuleCat.{u + 1} A) B
  let C := leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 B) (𝟙 B) (𝟙 B)
    (Category.id_comp _).symm
  have hp : a = C.hom.app _ ≫ I.map a ≫ a := by
    exact section_comparison_comp_at A N hN hA Q Q Q hInv (𝟙 B) (𝟙 B) (𝟙 B)
      (Category.id_comp _).symm e e e (by simp only [h, Category.id_comp])
  have hc : 𝟙 _ = C.hom.app _ ≫ I.map a := by
    apply (cancel_mono a).mp
    simpa only [Category.id_comp, Category.assoc] using hp
  have hn := J.hom.naturality a
  change I.map a ≫ J.hom.app _ = J.hom.app _ ≫ a at hn
  have hu := leftDerivedUpperStarComp_id_left_hom_app
    (ModuleCat.{u + 1} A) (𝟙 B) (sectionInvariant A Q.map Q.sect)
  change C.hom.app _ ≫ J.hom.app _ = 𝟙 _ at hu
  have hh : C.hom.app _ ≫ I.map a ≫ J.hom.app _ = a := by
    rw [hn, ← Category.assoc, hu, Category.id_comp]
  change a = J.hom.app _
  rw [← hh, ← Category.assoc, ← hc, Category.id_comp]

-- Generic structural locality laws, from the composite-adjunction counit equations of
-- lem-pur-section-etale-open-cancellation (copied from the private helpers of
-- Sheaf.Paper.FiniteSectionEtaleIntegration; that later module is not imported).
open WeilConjectures.PurityFiniteSetting CategoryTheory.MonoidalCategory in
private theorem source_locality_congr
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V B : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] [IsNoetherian B]
    (a : U ⟶ V) [Etale a] [IsSeparated a] [QuasiCompact a]
    (f : V ⟶ B) (f' : U ⟶ B)
    [HasCompactification a] [HasCompactification f] [HasCompactification f']
    [HasCompactification (a ≫ f)] (w : f' = a ≫ f) :
    (OpenCancellation.congr A w).app (𝟙_ _) ≪≫ OpenCancellation.source A a f =
      (sectionStructuralLocalityIso A a f f' w.symm).symm := by
  subst f'
  rw [OpenCancellation.congr_refl]
  have hi : (Iso.refl (OpenCancellation.exc A (a ≫ f))).app (𝟙_ _) =
      Iso.refl _ := rfl
  rw [hi, Iso.refl_trans]
  exact OpenCancellation.source_locality A a f

open WeilConjectures.PurityFiniteSetting CategoryTheory.MonoidalCategory in
private theorem structural_locality_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W X Y Z : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (h' : X ⟶ Z) (h'' : W ⟶ Z)
    [Etale f] [IsSeparated f] [QuasiCompact f]
    [Etale g] [IsSeparated g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    [IsSeparated h''] [LocallyOfFiniteType h''] [QuasiCompact h'']
    (w : h' = g ≫ h) (w' : h'' = f ≫ h') :
    (ordinaryFinitePullback A f).mapIso
        (sectionStructuralLocalityIso A g h h' w.symm) ≪≫
      sectionStructuralLocalityIso A f h' h'' w'.symm =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).symm.app
        (dualizingComplex A h) ≪≫
      sectionStructuralLocalityIso A (f ≫ g) h h''
        (by rw [Category.assoc, ← w, ← w']) := by
  have hs := OpenCancellation.source_comp_eq A f g h h' h'' w w'
  rw [source_locality_congr A (f ≫ g) h h'',
    source_locality_congr A f h' h'', source_locality_congr A g h h'] at hs
  have hi := congrArg Iso.symm hs
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Functor.mapIso_symm] at hi
  exact hi.symm

private theorem structural_locality_id
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    sectionStructuralLocalityIso A (𝟙 X) f f (Category.id_comp f) =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) X).app (dualizingComplex A f) := by
  let E := sectionStructuralLocalityIso A (𝟙 X) f f (Category.id_comp f)
  let C := ModuleCat.{u + 1} A
  let K := dualizingComplex A f
  have aux (c : X ⟶ X) [Etale c] [IsSeparated c] [QuasiCompact c]
      (hc : c = 𝟙 X ≫ 𝟙 X) :
      (ordinaryFinitePullback A (𝟙 X)).mapIso E ≪≫ E =
        (leftDerivedUpperStarComp C (𝟙 X) (𝟙 X) c hc).symm.app K ≪≫
          sectionStructuralLocalityIso A c f f
            (by rw [hc, Category.assoc, Category.id_comp, Category.id_comp]) := by
    subst c
    exact structural_locality_comp A (𝟙 X) (𝟙 X) f f f
      (Category.id_comp f).symm (Category.id_comp f).symm
  have hs := aux (𝟙 X) (Category.id_comp (𝟙 X)).symm
  have hh : (ordinaryFinitePullback A (𝟙 X)).map E.hom ≫ E.hom =
      (leftDerivedUpperStarComp C (𝟙 X) (𝟙 X) (𝟙 X)
        (Category.id_comp _).symm).inv.app K ≫ E.hom := congrArg Iso.hom hs
  have he := (cancel_mono E.hom).mp hh
  have hu := leftDerivedUpperStarComp_id_left_hom_app C (𝟙 X) K
  have hu' : (leftDerivedUpperStarComp C (𝟙 X) (𝟙 X) (𝟙 X)
        (Category.id_comp _).symm).inv.app K =
      (leftDerivedUpperStarId C X).hom.app
        ((ordinaryFinitePullback A (𝟙 X)).obj K) := by
    apply (cancel_epi ((leftDerivedUpperStarComp C (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.id_comp _).symm).hom.app K)).mp
    simpa only [C, K, ordinaryFinitePullback, Iso.hom_inv_id_app] using hu.symm
  have hn := (leftDerivedUpperStarId C X).hom.naturality E.hom
  simp only [Functor.id_map] at hn
  dsimp only [C, K, ordinaryFinitePullback] at he hu' hn
  rw [he, hu'] at hn
  apply Iso.ext
  exact ((cancel_epi ((leftDerivedUpperStarId C X).hom.app
    ((ordinaryFinitePullback A (𝟙 X)).obj K))).mp hn).symm

private theorem structural_section_locality_id
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (g : X ⟶ S) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (s : S ⟶ X) :
    FiniteRingSectionDeformation.etaleSectionMap A (𝟙 X) g g
      (Category.id_comp g) s s (Category.comp_id s) = 𝟙 _ := by
  rw [← FiniteRingSectionDeformation.sectionLocality_eq, structural_locality_id]
  exact leftDerivedUpperStarComp_id_right_hom_app (ModuleCat.{u + 1} A) s _

private theorem locality_id
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B : Scheme.{u}} {r : ℕ} (Q : ExceptionalSectionPair B r)
    [QuasiCompact Q.map]
    (e : ExceptionalSectionEtaleMap Q Q) (h : e.upper = 𝟙 Q.total) :
    (sectionExceptionalLocalityIso A e).hom = 𝟙 _ := by
  have := Q.base_noetherian
  have := SmoothOfRelativeDimension.smooth r Q.map
  rw [FiniteRingSectionDeformation.sectionExceptionalLocality_eq]
  cases e
  dsimp only at h
  subst h
  exact structural_section_locality_id A Q.map Q.sect

private theorem locality_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B : Scheme.{u}} {r : ℕ} (Q Q' Q'' : ExceptionalSectionPair B r)
    [QuasiCompact Q.map] [QuasiCompact Q'.map] [QuasiCompact Q''.map]
    (e : ExceptionalSectionEtaleMap Q Q') (f : ExceptionalSectionEtaleMap Q' Q'')
    (ef : ExceptionalSectionEtaleMap Q Q'') (h : ef.upper = f.upper ≫ e.upper) :
    (sectionExceptionalLocalityIso A ef).hom =
      (sectionExceptionalLocalityIso A e).hom ≫ (sectionExceptionalLocalityIso A f).hom := by
  have := Q.base_noetherian
  have := SmoothOfRelativeDimension.smooth r Q.map
  have := SmoothOfRelativeDimension.smooth r Q'.map
  have := SmoothOfRelativeDimension.smooth r Q''.map
  have hc := structural_locality_comp A f.upper e.upper Q.map Q'.map Q''.map
    e.map_comm.symm f.map_comm.symm
  have hi := congrArg Iso.symm hc
  simp only [Iso.trans_symm] at hi
  have hs := WeilConjectures.PurityFiniteSetting.SectionRestriction.section_comp
    A e.upper f.upper Q.sect Q'.sect Q''.sect e.section_comm.symm f.section_comm.symm
    (dualizingComplex A Q.map) (dualizingComplex A Q'.map) (dualizingComplex A Q''.map)
    (sectionStructuralLocalityIso A e.upper Q.map Q'.map e.map_comm).symm
    (sectionStructuralLocalityIso A f.upper Q'.map Q''.map f.map_comm).symm
    (sectionStructuralLocalityIso A (f.upper ≫ e.upper) Q.map Q''.map
      (by rw [Category.assoc, e.map_comm, f.map_comm])).symm hi.symm
  have hh := congrArg (fun z ↦ z.symm.hom) hs
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Functor.mapIso_symm,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hh
  cases ef
  dsimp only at h
  subst h
  simpa only [sectionExceptionalLocalityIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc] using hh

private theorem locality_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B B' : Scheme.{u}} {r : ℕ}
    (Q R : ExceptionalSectionPair B r) (Q' R' : ExceptionalSectionPair B' r)
    (b : B' ⟶ B) (e : ExceptionalSectionChange Q Q' b)
    (f : ExceptionalSectionChange R R' b)
    (h : ExceptionalSectionEtaleMap Q R) (h' : ExceptionalSectionEtaleMap Q' R')
    (w : f.upper ≫ h.upper = h'.upper ≫ e.upper) :
    (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.map
        (sectionExceptionalLocalityIso A h).hom ≫ sectionExceptionalComparison A f =
      sectionExceptionalComparison A e ≫ (sectionExceptionalLocalityIso A h').hom := by
  have := Q.base_noetherian
  have := Q'.base_noetherian
  have := SmoothOfRelativeDimension.smooth r Q.map
  have := SmoothOfRelativeDimension.smooth r R.map
  have := SmoothOfRelativeDimension.smooth r Q'.map
  have := SmoothOfRelativeDimension.smooth r R'.map
  have outer : IsPullback f.upper (h'.upper ≫ Q'.map) (h.upper ≫ Q.map) b := by
    simpa only [h.map_comm, h'.map_comm] using f.square
  have sq := IsPullback.of_bot outer w e.square
  have hc := sectionLocality_baseChange A h.upper Q.map h'.upper Q'.map
    R.map h.map_comm R'.map h'.map_comm b e.upper f.upper e.square sq f.square
    Q.sect Q'.sect R.sect R'.sect e.section_comm f.section_comm
    h.section_comm h'.section_comm
  simpa only [sectionLocality_formula, sectionExceptionalComparison,
    sectionExceptionalLocalityIso, SectionComparisonArrows.sectionMap,
    sectionCoherencePullbackIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, ordinaryFinitePullback, Category.assoc] using hc

/-- The full naturality squares, together with the geometric identifications.
Proof: the Rees and graded maps give the geometry, including nonflat base changes.
Smooth exceptional base change identifies the canonical counit mates at both endpoints.
Transport kappa along the family map; the one-fibre square makes it normalized, so
uniqueness identifies it with kappa prime. Restrict to zero and invert to get the square.
For etale pairs use composite-adjunction counits in place of the base-change mates;
the same one-fibre normalization and uniqueness give the second square.
Source: sk-lem-lem-sp-dnc-naturality (1), (2)
(blueprint: sk-lem-lem-sp-dnc-naturality). -/
theorem dncComparison_naturality (ell n : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p) (hn : 1 ≤ n) (P : Pair D d S) :
    IsIso (P.alpha ell n hell hn) ∧
    (∀ (P' : Pair D d S') (b : S' ⟶ S) (e : Change P P' b),
      IsIso (e.endpoint (NoetherianSectionSpecialization.Coeff ell n) true) ∧
      IsIso (e.endpoint (NoetherianSectionSpecialization.Coeff ell n) false) ∧
      e.endpoint (NoetherianSectionSpecialization.Coeff ell n) true ≫
          P'.alpha ell n hell hn =
        (upperStar (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n))
          b.left).leftDerivedFunctor.map (P.alpha ell n hell hn) ≫
          e.endpoint (NoetherianSectionSpecialization.Coeff ell n) false) ∧
    (∀ (P' : Pair D d S) (e : EtaleChange P P'),
      IsIso ((e.family.fibre false).upper) ∧
      IsIso (SectionReesBaseChange.conormalMap P.sect.left P'.sect.left e.upper.left
        (𝟙 S.left)
          ((congrArg Over.Hom.left e.section_comm).trans (Category.id_comp _).symm)) ∧
      (e.endpoint (NoetherianSectionSpecialization.Coeff ell n) true).hom ≫
          P'.alpha ell n hell hn =
        P.alpha ell n hell hn ≫
          (e.endpoint (NoetherianSectionSpecialization.Coeff ell n) false).hom) := by
  let A := NoetherianSectionSpecialization.Coeff.{u} ell n
  have hN : 0 < ell ^ n := pow_pos (Nat.Prime.pos Fact.out) n
  have hA : ((ell ^ n : ℕ) : A) = 0 := by
    apply ULift.ext
    exact ZMod.natCast_self _
  have hInv : ∀ x : S.left, IsUnit ((ell ^ n : ℕ) : S.left.presheaf.stalk x) := by
    intro x
    simpa only [Nat.cast_pow] using (coefficient_isUnit ell hell S x).pow n
  have hNS : IsUnit ((ell ^ n : ℕ) : Γ(S.left, ⊤)) := by
    apply S.left.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using hInv x
  have : HasInvertibleExponent A S.left := ⟨ell ^ n, hN, hA, hNS⟩
  have : HasInvertibleExponent A P.family.ambient.total :=
    .of_hom (P.family.ambient.map ≫ (AffineSpace (ULift.{u} (Fin 1)) S.left ↘ S.left))
  have hfibre : IsIso (P.family.fibreMap A false) :=
    section_comparison_isIso A P.family.ambient (P.family.fibre false)
      (exceptionalFamilyPoint S.left false) (P.family.restriction false)
  have halpha : IsIso (P.alpha ell n hell hn) := by
    unfold Pair.alpha ExceptionalSectionFamily.specialization
    infer_instance
  refine ⟨halpha, ?_, ?_⟩
  · intro P' b e
    have hc := sectionExceptional_fibre_coherence A (ell ^ n) hN hA
      P.family P'.family hInv b.left e.family
    exact ⟨(hc.2 true).2.2.1, (hc.2 false).2.2.1,
      (sectionExceptional_normalized_baseChange A (ell ^ n) hN hA
        P.family P'.family hInv b.left e.family
        (P.kappa ell n hell hn) (P'.kappa ell n hell hn)
        (P.normalized_existsUnique ell n hell hn).choose_spec
        (P'.normalized_existsUnique ell n hell hn).choose_spec).2⟩
  · intro P' e
    have : IsNoetherian S.left := P.exceptional.base_noetherian
    have : IsNoetherian P'.total.left := P'.exceptional.total_noetherian
    have := SmoothOfRelativeDimension.smooth d P.map.left
    have hm : e.upper.left ≫ P.map.left = P'.map.left :=
      congrArg Over.Hom.left e.map_comm
    have : IsSeparated (e.upper.left ≫ P.map.left) := hm ▸ P'.separated
    have : IsSeparated e.upper.left := IsSeparated.of_comp _ P.map.left
    have hw : P'.sect.left ≫ e.upper.left = (𝟙 S.left) ≫ P.sect.left :=
      (congrArg Over.Hom.left e.section_comm).trans (Category.id_comp _).symm
    have hs : P'.sect.left ≫ (e.upper.left ≫ P.map.left) = 𝟙 S.left := by
      rw [hm]
      exact congrArg Over.Hom.left P'.retraction
    obtain ⟨_, _, _, hcon, ν, hν, hνiso⟩ := SectionReesBaseChange.etale d
      P.map.left P.sect.left (congrArg Over.Hom.left P.retraction)
      e.upper.left P'.sect.left hs hw e.centres
    have : IsClosedImmersion P.sect.left.ker.normalConeToDeformationSpace :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (Scheme.Hom.isPullback_normalConeToDeformationSpace P.map.left P.sect.left).flip
        inferInstance
    have hupper : (e.family.fibre false).upper = ν := by
      apply (cancel_mono P.sect.left.ker.normalConeToDeformationSpace).mp
      exact e.family_existsUnique.choose_spec.1.2.2.trans hν.symm
    refine ⟨?_, hcon, ?_⟩
    · rw [hupper]
      exact hνiso
    · exact (sectionExceptional_normalized_etale A (ell ^ n) hN hA
        P.family P'.family hInv e.family
        (P.kappa ell n hell hn) (P'.kappa ell n hell hn)
        (P.normalized_existsUnique ell n hell hn).choose_spec
        (P'.normalized_existsUnique ell n hell hn).choose_spec).2

/-- Identity, composition and base-change/etale interchange for the specified endpoint maps.
Each equation is required at both endpoints; hence it applies to both vertical arrows of
both naturality squares. The pullback compositor is written in the base-composition law.
Proof: geometric Rees and associated-graded maps preserve identities and composition.
Transpose the identity and composite compact-support counits. The mate-pasting identities
identify these transposes, proving the base-change laws. The etale laws follow from the
unique counit-normalized adjoint comparisons. In the mixed rectangle compact-support
exchange commutes with composition; transposing gives the same map in both orders.
Together with uniqueness of kappa normalized at one these are the asserted coherence laws.
Source: sk-lem-lem-sp-dnc-naturality, final paragraph
(blueprint: sk-lem-lem-sp-dnc-naturality). -/
theorem dncComparison_coherence (ell n : ℕ) [Fact ell.Prime]
    (_hell : ell ≠ D.p) (_hn : 1 ≤ n) (P : Pair D d S) :
    (∀ (e : Change P P (𝟙 S)), e.upper = 𝟙 P.total → ∀ t : Bool,
      e.endpoint (NoetherianSectionSpecialization.Coeff ell n) t =
        (leftDerivedUpperStarId
          (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n)) S.left).hom.app
            (sectionInvariant (NoetherianSectionSpecialization.Coeff ell n)
              (P.family.fibre t).map (P.family.fibre t).sect)) ∧
    (∀ (e : EtaleChange P P), e.upper = 𝟙 P.total → ∀ t : Bool,
      (e.endpoint (NoetherianSectionSpecialization.Coeff ell n) t).hom = 𝟙 _) ∧
    (∀ (P' : Pair D d S') (P'' : Pair D d S'')
      (b : S' ⟶ S) (c : S'' ⟶ S')
      (e : Change P P' b) (f : Change P' P'' c) (ef : Change P P'' (c ≫ b)),
      ef.upper = f.upper ≫ e.upper → ∀ t : Bool,
        ef.endpoint (NoetherianSectionSpecialization.Coeff ell n) t =
          (leftDerivedUpperStarComp
            (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n))
            c.left b.left).hom.app
              (sectionInvariant (NoetherianSectionSpecialization.Coeff ell n)
                (P.family.fibre t).map (P.family.fibre t).sect) ≫
            (upperStar (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n))
              c.left).leftDerivedFunctor.map
                (e.endpoint (NoetherianSectionSpecialization.Coeff ell n) t) ≫
            f.endpoint (NoetherianSectionSpecialization.Coeff ell n) t) ∧
    (∀ (P' P'' : Pair D d S) (e : EtaleChange P P') (f : EtaleChange P' P'')
      (ef : EtaleChange P P''), ef.upper = f.upper ≫ e.upper → ∀ t : Bool,
        (ef.endpoint (NoetherianSectionSpecialization.Coeff ell n) t).hom =
          (e.endpoint (NoetherianSectionSpecialization.Coeff ell n) t).hom ≫
            (f.endpoint (NoetherianSectionSpecialization.Coeff ell n) t).hom) ∧
    (∀ (Q : Pair D d S) (P' Q' : Pair D d S') (b : S' ⟶ S)
      (e : Change P P' b) (f : Change Q Q' b)
      (h : EtaleChange P Q) (h' : EtaleChange P' Q'),
      f.upper ≫ h.upper = h'.upper ≫ e.upper → ∀ t : Bool,
        (upperStar (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n))
          b.left).leftDerivedFunctor.map
            (h.endpoint (NoetherianSectionSpecialization.Coeff ell n) t).hom ≫
            f.endpoint (NoetherianSectionSpecialization.Coeff ell n) t =
          e.endpoint (NoetherianSectionSpecialization.Coeff ell n) t ≫
            (h'.endpoint (NoetherianSectionSpecialization.Coeff ell n) t).hom) := by
  let A := NoetherianSectionSpecialization.Coeff.{u} ell n
  have hN : 0 < ell ^ n := pow_pos (Nat.Prime.pos Fact.out) n
  have hA : ((ell ^ n : ℕ) : A) = 0 := by
    apply ULift.ext
    exact ZMod.natCast_self _
  have hInv : ∀ x : S.left, IsUnit ((ell ^ n : ℕ) : S.left.presheaf.stalk x) := by
    intro x
    simpa only [Nat.cast_pow] using (coefficient_isUnit ell _hell S x).pow n
  have hNS : IsUnit ((ell ^ n : ℕ) : Γ(S.left, ⊤)) := by
    apply S.left.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    simpa only [map_natCast] using hInv x
  have : HasInvertibleExponent A S.left := ⟨ell ^ n, hN, hA, hNS⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he t
    have : HasInvertibleExponent A (P.family.fibre t).total :=
      .of_hom (P.family.fibre t).map
    exact comparison_id A (ell ^ n) hN hA (P.family.fibre t) hInv
      (e.family.fibre t) (base_fibre_id P e he t)
  · intro e he t
    exact locality_id A (P.family.fibre t) (e.family.fibre t)
      (etale_fibre_id P e he t)
  · intro P' P'' b c e f ef he t
    exact sectionExceptional_comparison_comp A (ell ^ n) hN hA
      (P.family.fibre t) (P'.family.fibre t) (P''.family.fibre t) hInv b.left c.left
      (e.family.fibre t) (f.family.fibre t) (ef.family.fibre t)
      (base_fibre_comp P P' P'' b c e f ef he t)
  · intro P' P'' e f ef he t
    exact locality_comp A (P.family.fibre t) (P'.family.fibre t) (P''.family.fibre t)
      (e.family.fibre t) (f.family.fibre t) (ef.family.fibre t)
      (etale_fibre_comp P P' P'' e f ef he t)
  · intro Q P' Q' b e f h h' hw t
    exact locality_baseChange A (P.family.fibre t) (Q.family.fibre t)
      (P'.family.fibre t) (Q'.family.fibre t) b.left
      (e.family.fibre t) (f.family.fibre t) (h.family.fibre t) (h'.family.fibre t)
      (mixed_fibre P Q P' Q' b e f h h' hw t)


end AlgebraicGeometry.Etale.DncNaturality
