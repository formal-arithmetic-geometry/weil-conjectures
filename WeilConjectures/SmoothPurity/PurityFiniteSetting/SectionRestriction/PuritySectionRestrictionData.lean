/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Section.PuritySectionInvariantIntrinsic
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Section.PuritySectionInvariant
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.AlgebraicGeometry.Purity.PurityNormalProjection
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncComparisons
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
public import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalComposition
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncInvariance
public import WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
import all WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale

/-! # Counit-normalized restriction of smooth section invariants

Source: blueprint sec-smooth-purity, orientation charts Step 3 and composition
coherence Step 1 (blueprint: lem-pur-section-etale-restriction-coherence).

Section objects, families and endpoint maps are the published actual constructions.
The ordinary-etale coordinates below are transported by the canonical comparison
pullback to the small pro-etale category. No orientation is selected.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.SectionRestriction

/-- A smooth section pair, bundling exactly the geometric hypotheses over the given base.
Source: orientation charts Step 3
(blueprint: lem-pur-section-etale-restriction-coherence). -/
structure Pair (B : Scheme.{u}) (d : ℕ) where
  V : Scheme.{u}
  g : V ⟶ B
  s : B ⟶ V
  smooth : SmoothOfRelativeDimension d g
  separated : IsSeparated g
  quasiCompact : QuasiCompact g
  closed : IsClosedImmersion s
  section_eq : s ≫ g = 𝟙 B

attribute [instance] Pair.smooth Pair.separated Pair.quasiCompact Pair.closed

/-- A map of section pairs with Cartesian centres; the direction is source to target.
Source: orientation charts Steps 1--3
(blueprint: lem-pur-section-etale-restriction-coherence). -/
structure EtaleMap {B : Scheme.{u}} {d : ℕ} (X' X : Pair B d) where
  map : X'.V ⟶ X.V
  etale : Etale map
  separated : IsSeparated map
  quasiCompact : QuasiCompact map
  over_eq : map ≫ X.g = X'.g
  section_eq : X'.s ≫ map = X.s
  centres : IsPullback X'.s (𝟙 B) map X.s

attribute [instance] EtaleMap.etale EtaleMap.separated EtaleMap.quasiCompact

/-- Identity map of a section pair, including its Cartesian centre square.
Source: composition coherence Step 1
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def EtaleMap.id {B : Scheme.{u}} {d : ℕ} (X : Pair B d) : EtaleMap X X where
  map := 𝟙 X.V
  etale := inferInstance
  separated := inferInstance
  quasiCompact := inferInstance
  over_eq := Category.id_comp _
  section_eq := Category.comp_id _
  centres := IsPullback.of_id_snd

/-- Composition of maps of section pairs; centre squares paste.
Source: composition coherence Step 1
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def EtaleMap.comp {B : Scheme.{u}} {d : ℕ} {X'' X' X : Pair B d}
    (b : EtaleMap X'' X') (a : EtaleMap X' X) : EtaleMap X'' X where
  map := b.map ≫ a.map
  etale := inferInstance
  separated := inferInstance
  quasiCompact := inferInstance
  over_eq := by rw [Category.assoc, a.over_eq, b.over_eq]
  section_eq := by rw [← Category.assoc, b.section_eq, a.section_eq]
  centres := by simpa only [Category.comp_id] using b.centres.paste_vert a.centres

/-- The actual source section invariant, using the recorded finite realization.
Source: C(g,s) in the statement and the canonical DNC comparison module
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def invariant (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (X : Pair B d) :=
  Dnc.sourceSection P d X.g aB X.s

/-- Ordinary-etale coordinates for the same section object.
Source: finite-coefficient comparison in orientation charts Step 3
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def sectionEtale (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (X : Pair B d) :=
  Dnc.sourceEtale P d X.g aB X.s

/-- The formula Ls'*(rho_a c_{g,a}) followed by the pullback-composition constraint.
`sourceEtale` is the specified conjugate compositor followed by the counit-normalized rho.
Source: orientation charts Step 3; finite etale dualizing normalization clause (3)
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def restrictionEtale (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    {X' X : Pair B d} (a : EtaleMap X' X) :
    sectionEtale P aB X' ≅ sectionEtale P aB X :=
  letI := SmoothOfRelativeDimension.smooth d X.g
  letI := SmoothOfRelativeDimension.smooth d X'.g
  letI : B.Over (Spec (.of P.field.k)) := ⟨aB⟩
  letI : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aB)
  letI : QuasiCompact (B ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aB)
  letI : X.V.Over (Spec (.of P.field.k)) := ⟨X.g ≫ aB⟩
  letI : X'.V.Over (Spec (.of P.field.k)) := ⟨X'.g ≫ aB⟩
  letI : X.g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : X'.g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : a.map.IsOver (Spec (.of P.field.k)) := ⟨by
    change a.map ≫ (X.g ≫ aB) = X'.g ≫ aB
    rw [← Category.assoc, a.over_eq]⟩
  letI : LocallyOfFiniteType (X.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X.g ≫ aB))
  letI : QuasiCompact (X.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (X.g ≫ aB))
  letI : LocallyOfFiniteType (X'.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X'.g ≫ aB))
  letI : QuasiCompact (X'.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (X'.g ≫ aB))
  letI := Dnc.compactifiable P X.g aB
  letI := Dnc.compactifiable P X'.g aB
  (AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.pull P X'.s).mapIso
      ((AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.congr P X'.g
          (a.map ≫ X.g) a.over_eq.symm).app (𝟙_ _) ≪≫
        AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.sourceEtale P a.map X.g) ≪≫
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      X'.s a.map X.s a.section_eq.symm).app _).symm

/-- The actual pro-etale restriction, transported through the canonical nu* comparisons.
Source: orientation charts Step 3; no coefficient-line identification
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def restriction (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    {X' X : Pair B d} (a : EtaleMap X' X) : invariant P aB X' ≅ invariant P aB X :=
  Dnc.sourceComparison P d X'.g aB X'.s ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
        (restrictionEtale P aB a) ≪≫ (Dnc.sourceComparison P d X.g aB X.s).symm

/-- The actual normal pair, with its associated-graded cone and zero section.
Source: DNC geometry, zero fibre
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def normalPair (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (X : Pair B d) : Pair B d :=
  letI := Dnc.normalCompactifiable P d X.g aB X.s X.section_eq
  { V := X.s.ker.normalCone
    g := Scheme.Hom.normalConeProj X.g X.s
    s := X.s.normalConeZeroSection
    smooth := (Scheme.Hom.normalConeData d X.section_eq).smoothOfRelativeDimension_proj
    separated := inferInstance
    quasiCompact := Dnc.normalQuasiCompact d X.g X.s X.section_eq
    closed := inferInstance
    section_eq := Scheme.Hom.normalConeZeroSection_normalConeProj X.section_eq }

/-- The actual extended-Rees deformation pair over the affine line.
Source: DNC section family and its augmentation
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def familyPair {B : Scheme.{u}} {d : ℕ} (X : Pair B d) :
    Pair (AffineSpace (ULift.{u} (Fin 1)) B) d :=
  { V := X.s.ker.deformationSpace
    g := Scheme.Hom.deformationSpaceProj X.g X.s
    s := X.s.deformationSpaceSection
    smooth := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj
      d X.g X.s X.section_eq
    separated := inferInstance
    quasiCompact := inferInstance
    closed := by
      have : IsClosedImmersion (X.s.deformationSpaceSection ≫
          Scheme.Hom.deformationSpaceProj X.g X.s) := by
        rw [Scheme.Hom.deformationSpaceSection_deformationSpaceProj X.section_eq]
        infer_instance
      exact IsClosedImmersion.of_comp _ (Scheme.Hom.deformationSpaceProj X.g X.s)
    section_eq := Scheme.Hom.deformationSpaceSection_deformationSpaceProj X.section_eq }

/-- The coefficientwise Rees map, fixing t and sending f/t to a*(f)/t.
Source: orientation charts Step 3; section Rees base change, etale clause
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def deformationMap {B : Scheme.{u}} {d : ℕ} {X' X : Pair B d}
    (a : EtaleMap X' X) : (familyPair X').V ⟶ (familyPair X).V :=
  SectionReesBaseChange.pairMap X.s X'.s a.map (𝟙 B)
    (a.section_eq.trans (Category.id_comp X.s).symm)

/-- The actual induced normal map, uniquely determined by its composite with the
closed zero-fibre inclusion. The existing Rees theorem supplies this determined map;
its affine description is the associated-graded map of a*, not a chosen frame.
Source: orientation charts Step 2; section Rees base change, etale clause
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def normalMap (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    {X' X : Pair B d} (a : EtaleMap X' X) :
    (normalPair P aB X').V ⟶ (normalPair P aB X).V :=
  letI := P.noetherian aB
  letI := SmoothOfRelativeDimension.smooth d X.g
  Classical.choose (SectionReesBaseChange.etale d X.g X.s X.section_eq a.map X'.s
    (by rw [a.over_eq]; exact X'.section_eq)
    (a.section_eq.trans (Category.id_comp X.s).symm) a.centres).2.2.2.2

/-- Geometry of the specified Rees and associated-graded maps, including augmented
sections and the two endpoint maps. The two centre squares are Cartesian.
Source: orientation charts Steps 1--3
(blueprint: lem-pur-section-etale-restriction-coherence).
Proof: finite type over k makes the base Noetherian. Cartesian centres identify
I' with a*I. Flatness of the etale coefficient map gives the extended-Rees pushout
R[t,I/t] tensor_R R' = R'[t,I'/t], so deformationMap is etale. Its augmentation
and one-fibre equations follow on r,t,f/t. Quotient by t gives normalMap and its
zero-section equation. Flat conormal base change identifies this normal map with
the induced vector-bundle isomorphism. The augmentation centre square follows
by base-changing the original centre square. Etaleness and finite type of both
pairs supply separatedness and quasi-compactness of the family map. -/
theorem geometry (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    {X' X : Pair B d} (a : EtaleMap X' X) :
    Etale (deformationMap a) ∧ IsSeparated (deformationMap a) ∧
    QuasiCompact (deformationMap a) ∧
    deformationMap a ≫ (familyPair X).g = (familyPair X').g ∧
    (familyPair X').s ≫ deformationMap a = (familyPair X).s ∧
    IsPullback (familyPair X').s (𝟙 _) (deformationMap a) (familyPair X).s ∧
    IsIso (normalMap P aB a) ∧
    normalMap P aB a ≫ (normalPair P aB X).g = (normalPair P aB X').g ∧
    (normalPair P aB X').s ≫ normalMap P aB a = (normalPair P aB X).s ∧
    IsPullback (normalPair P aB X').s (𝟙 _) (normalMap P aB a)
      (normalPair P aB X).s ∧
    Scheme.Hom.deformationSpaceOneFibre X'.g X'.s ≫ deformationMap a =
      a.map ≫ Scheme.Hom.deformationSpaceOneFibre X.g X.s ∧
    X'.s.ker.normalConeToDeformationSpace ≫ deformationMap a =
      normalMap P aB a ≫ X.s.ker.normalConeToDeformationSpace := by
  let := P.noetherian aB
  let := SmoothOfRelativeDimension.smooth d X.g
  have H := SectionReesBaseChange.etale d X.g X.s X.section_eq a.map X'.s
    (by rw [a.over_eq]; exact X'.section_eq)
    (a.section_eq.trans (Category.id_comp X.s).symm) a.centres
  have hc := H.2.2.1
  have hover : deformationMap a ≫ (familyPair X).g = (familyPair X').g := by
    simpa only [deformationMap, familyPair, Category.comp_id, AffineSpace.map_id,
      Category.id_comp, a.over_eq] using hc.1
  have hsection : (familyPair X').s ≫ deformationMap a = (familyPair X).s := by
    simpa only [deformationMap, familyPair, AffineSpace.map_id, Category.id_comp]
      using hc.2.1
  have hnormal := Classical.choose_spec H.2.2.2.2
  have hz := Scheme.Hom.isPullback_normalConeToDeformationSpace X.g X.s
  have : IsClosedImmersion X.s.ker.normalConeToDeformationSpace :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hz.flip inferInstance
  obtain ⟨ν, l, _, hν, hπ, hs, _⟩ := hc.2.2.2
  have he : ν = normalMap P aB a := by
    apply (cancel_mono X.s.ker.normalConeToDeformationSpace).mp
    exact hν.trans hnormal.1.symm
  have hnπ : normalMap P aB a ≫ (normalPair P aB X).g =
      (normalPair P aB X').g := by
    simpa only [normalPair, he, Category.comp_id, a.over_eq] using hπ
  have hns : (normalPair P aB X').s ≫ normalMap P aB a =
      (normalPair P aB X).s := by
    simpa only [normalPair, he, Category.id_comp] using hs
  have : IsIso (normalMap P aB a) := hnormal.2
  have hsep : IsSeparated (deformationMap a) := by
    have : IsSeparated (deformationMap a ≫ (familyPair X).g) := by
      rw [hover]
      exact (familyPair X').separated
    exact IsSeparated.of_comp _ (familyPair X).g
  have hqc : QuasiCompact (deformationMap a) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) H.1.flip inferInstance
  refine ⟨H.2.1, hsep, hqc, hover, hsection, ?_, hnormal.2, hnπ, hns, ?_, ?_,
    hnormal.1.symm⟩
  · have hline : IsPullback
        (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) (𝟙 _) (𝟙 B)
        (AffineSpace (ULift.{u} (Fin 1)) B ↘ B) :=
      IsPullback.of_vert_isIso ⟨by simp⟩
    have hout := hline.paste_horiz a.centres
    rw [← Scheme.Hom.deformationSpaceSection_toBase,
      ← Scheme.Hom.deformationSpaceSection_toBase] at hout
    have hpb := hout.of_right
      (by simpa only [familyPair, deformationMap, Category.id_comp] using hsection) H.1.flip
    simpa only [familyPair, deformationMap] using hpb
  · exact IsPullback.of_vert_isIso ⟨by simpa only [Category.id_comp] using hns⟩
  · simpa only [deformationMap, a.over_eq] using hc.2.2.1

/-- The etale map of augmented deformation pairs, with exactly the coefficientwise map.
Source: orientation charts Step 3
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def familyMap (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    {X' X : Pair B d} (a : EtaleMap X' X) : EtaleMap (familyPair X') (familyPair X) :=
  { map := deformationMap a
    etale := (geometry P aB a).1
    separated := (geometry P aB a).2.1
    quasiCompact := (geometry P aB a).2.2.1
    over_eq := (geometry P aB a).2.2.2.1
    section_eq := (geometry P aB a).2.2.2.2.1
    centres := (geometry P aB a).2.2.2.2.2.1 }

/-- The normal-bundle isomorphism as an etale map of zero-section pairs.
Source: orientation charts Step 2
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def normalEtaleMap (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    {X' X : Pair B d} (a : EtaleMap X' X) :
    EtaleMap (normalPair P aB X') (normalPair P aB X) :=
  letI := (geometry P aB a).2.2.2.2.2.2.1
  { map := normalMap P aB a
    etale := inferInstance
    separated := inferInstance
    quasiCompact := inferInstance
    over_eq := (geometry P aB a).2.2.2.2.2.2.2.1
    section_eq := (geometry P aB a).2.2.2.2.2.2.2.2.1
    centres := (geometry P aB a).2.2.2.2.2.2.2.2.2.1 }

/-- The family restriction is the very same restriction formula on the Rees pair.
Source: orientation charts Step 3
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def familyRestriction (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    {X' X : Pair B d} (a : EtaleMap X' X) :=
  restriction P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) (familyMap P aB a)

/-- A base-change square of smooth section pairs. No flatness condition is imposed on b.
Source: smooth base-change coherence in composition Step 1
(blueprint: lem-pur-section-etale-restriction-coherence). -/
structure BaseChange {B' B : Scheme.{u}} {d : ℕ} (b : B' ⟶ B)
    (X' : Pair B' d) (X : Pair B d) where
  map : X'.V ⟶ X.V
  square : IsPullback map X'.g X.g b
  section_eq : X'.s ≫ map = b ≫ X.s

/-- Identity Cartesian square of a smooth section pair.
Source: base-change identity constraint
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def BaseChange.id {B : Scheme.{u}} {d : ℕ} (X : Pair B d) : BaseChange (𝟙 B) X X :=
  ⟨𝟙 X.V, IsPullback.of_id_fst, by simp⟩

/-- Pasting of Cartesian base changes of section pairs.
Source: base-change composition constraint
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def BaseChange.comp {B₂ B₁ B : Scheme.{u}} {d : ℕ} {b₂ : B₂ ⟶ B₁} {b₁ : B₁ ⟶ B}
    {X₂ : Pair B₂ d} {X₁ : Pair B₁ d} {X : Pair B d}
    (sq₂ : BaseChange b₂ X₂ X₁) (sq₁ : BaseChange b₁ X₁ X) :
    BaseChange (b₂ ≫ b₁) X₂ X :=
  ⟨sq₂.map ≫ sq₁.map, sq₂.square.paste_horiz sq₁.square, by
    rw [← Category.assoc, sq₂.section_eq, Category.assoc, sq₁.section_eq, Category.assoc]⟩

/-- The canonical smooth base-change map on actual section invariants, constructed
from the adjunction-mate dualizing map, not chosen from an existence assertion.
Source: smooth base-change coherence, DNC geometry clause (1)
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def baseComparison (P : PurityFiniteSetting.{u}) {B' B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB' : B' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB'] [QuasiCompact aB']
    {b : B' ⟶ B} {X' : Pair B' d} {X : Pair B d} (sq : BaseChange b X' X) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.obj
      (invariant P aB X) ≅ invariant P aB' X' :=
  letI := SmoothOfRelativeDimension.smooth d X.g
  letI := SmoothOfRelativeDimension.smooth d X'.g
  letI := Dnc.compactifiable P X.g aB
  letI := Dnc.compactifiable P X'.g aB'
  letI := Dnc.invertibleExponent P (X.g ≫ aB)
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
      (Dnc.sourceComparison P d X.g aB X.s) ≪≫
    Dnc.pullComparison P b (sectionEtale P aB X) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B').mapDerivedCategory.mapIso
        (Dnc.sectionBaseChange P.Coefficient d X.g sq.square X.s X'.s sq.section_eq) ≪≫
      (Dnc.sourceComparison P d X'.g aB' X'.s).symm

/-- The canonical one-fibre comparison, through the published smooth base-change mate.
Source: DNC geometry clause (1)
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def endpointOne (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (X : Pair B d) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.obj
        (invariant P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) (familyPair X)) ≅
      invariant P aB X :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso
        (Dnc.sourceComparison P d (familyPair X).g
          ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) (familyPair X).s) ≪≫
    Dnc.pullComparison P _ (Dnc.familyEtale P d X.g aB X.s X.section_eq) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
        (Dnc.fibreOne P d X.g aB X.s X.section_eq) ≪≫
      (Dnc.sourceComparison P d X.g aB X.s).symm

/-- The canonical zero-fibre comparison to the actual normal pair.
Source: DNC geometry clause (1)
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def endpointZero (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (X : Pair B d) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.obj
        (invariant P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) (familyPair X)) ≅
      invariant P aB (normalPair P aB X) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso
        (Dnc.sourceComparison P d (familyPair X).g
          ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) (familyPair X).s) ≪≫
    Dnc.pullComparison P _ (Dnc.familyEtale P d X.g aB X.s X.section_eq) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
        (Dnc.fibreZero P d X.g aB X.s X.section_eq) ≪≫
      (Dnc.normalComparison P d X.g aB X.s X.section_eq).symm

/-- The unique coordinate-normalized deformation isomorphism already specified by
DNC invariance. Its unique characterization fixes the choice; no orientation is chosen.
Source: DNC invariance, uniqueness clause
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def delta (P : PurityFiniteSetting.{u}) {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB] (X : Pair B d) :
    invariant P aB X ≅ invariant P aB (normalPair P aB X) :=
  Classical.choose (Dnc.existsUnique_dncInvariance P d X.g aB X.s X.section_eq)

/-- The actual coefficientwise Rees comparison under a base-change square.
Source: DNC geometry, arbitrary base change
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def reesBaseMap {B' B : Scheme.{u}} {d : ℕ} {b : B' ⟶ B}
    {X' : Pair B' d} {X : Pair B d} (sq : BaseChange b X' X) :
    (familyPair X').V ⟶ (familyPair X).V :=
  SectionReesBaseChange.pairMap X.s X'.s sq.map b sq.section_eq

/-- Affine cover on which a Cartesian change of a smooth section is a Rees pushout.
Near the section, use centred etale coordinates and base change of the polynomial
origin ideal; away from it, the ideal is the unit ideal. This is the local argument of
`WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeCover`, applied to the
given Cartesian square instead of a chosen pullback object. -/
private theorem reesBaseCover {B' B : Scheme.{u}} {d : ℕ} {b : B' ⟶ B}
    {X' : Pair B' d} {X : Pair B d} (sq : BaseChange b X' X) (x : X'.V) :
    ∃ (U' : X'.V.AffineZariskiSite) (U : X.V.AffineZariskiSite)
      (hU : U'.1 ≤ sq.map ⁻¹ᵁ U.1), x ∈ U'.1 ∧
      ∃ hle : (X.s.ker.siteIdeal U).map (sq.map.appLE U.1 U'.1 hU).hom ≤
          X'.s.ker.siteIdeal U',
        IsPushout (sq.map.appLE U.1 U'.1 hU) (X.s.ker.toReesPresheaf.app (.op U))
          (X'.s.ker.toReesPresheaf.app (.op U'))
          (CommRingCat.ofHom ((X.s.ker.siteIdeal U).extendedReesAlgebraMap
            (sq.map.appLE U.1 U'.1 hU).hom (X'.s.ker.siteIdeal U') hle)) := by
  classical
  let := SmoothOfRelativeDimension.smooth d X.g
  have centres : IsPullback X'.s b sq.map X.s := by
    apply IsPullback.of_right (h₁₂ := X'.g) (h₂₂ := X.g) (v₁₃ := b)
      (t := sq.square.flip) ?_ sq.section_eq
    rw [X'.section_eq, X.section_eq]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hker : X'.s.ker = X.s.ker.comap sq.map := by
    rw [← centres.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hideal (U' : X'.V.AffineZariskiSite) (U : X.V.AffineZariskiSite)
      (hU : U'.1 ≤ sq.map ⁻¹ᵁ U.1) :
      X'.s.ker.siteIdeal U' = (X.s.ker.siteIdeal U).map (sq.map.appLE U.1 U'.1 hU).hom := by
    rw [Scheme.IdealSheafData.siteIdeal, hker,
      Scheme.IdealSheafData.ideal_comap_appLE X.s.ker sq.map ⟨U.1, U.2⟩ ⟨U'.1, U'.2⟩ hU]
  by_cases hx : sq.map x ∈ Set.range X.s
  · obtain ⟨b₀, hb₀⟩ := hx
    obtain ⟨W, hW, U, hUW, hb₀W, hsU, ψ, hψ, hψf, hI⟩ :=
      Scheme.Hom.exists_etale_coordinates_of_mem_range X.g X.s d X.section_eq b₀
    have hxU : sq.map x ∈ U.1 := by
      rw [← hb₀, ← Scheme.Hom.mem_preimage, hsU]
      exact hb₀W
    have hxW : X'.g x ∈ b ⁻¹ᵁ W := by
      rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← sq.square.w,
        Scheme.Hom.comp_apply, ← hb₀,
        ← Scheme.Hom.comp_apply, X.section_eq]
      exact hb₀W
    obtain ⟨W', hW', hxW', hW'W⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      B'.isBasis_affineOpens hxW
    have H := sq.square
    have hT := H.isAffineOpen_inf_preimage hW U.2 hUW hW' hW'W
    have P₁ := H.isPushout_appLE_inf_preimage hW U.2 hUW hW' hW'W
    set T := sq.map ⁻¹ᵁ U.1 ⊓ X'.g ⁻¹ᵁ W'
    set κ := (b.appLE W W' hW'W).hom
    set a := ((sq.map).appLE U.1 T inf_le_left).hom
    set ψ' : MvPolynomial (Fin d) Γ(B', W') →+* Γ(X'.V, T) :=
      MvPolynomial.eval₂Hom ((X'.g).appLE W' T inf_le_right).hom
        fun i ↦ a (ψ (MvPolynomial.X i))
    have hcomp : a.comp ψ = ψ'.comp (MvPolynomial.map κ) := by
      refine MvPolynomial.ringHom_ext (fun c ↦ ?_) fun i ↦ ?_
      · have := congr($(P₁.w).hom c)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
        rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.map_C, ← RingHom.comp_apply ψ,
          hψf]
        simpa [ψ'] using this
      · simp [ψ']
    -- `C' ⊗_C C[X_i] = C'[X_i]`
    have t : IsPushout (CommRingCat.ofHom MvPolynomial.C) (CommRingCat.ofHom κ)
        (CommRingCat.ofHom (MvPolynomial.map κ)) (CommRingCat.ofHom (MvPolynomial.C (σ := Fin d)))
        := by
      let := κ.toAlgebra
      let := MvPolynomial.algebraMvPolynomial (σ := Fin d) (R := Γ(B, W)) (S := Γ(B', W'))
      exact (CommRingCat.isPushout_of_isPushout Γ(B, W) Γ(B', W') (MvPolynomial (Fin d) Γ(B, W))
        (MvPolynomial (Fin d) Γ(B', W'))).flip
    have outer : IsPushout (CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom ψ)
        (CommRingCat.ofHom κ) (CommRingCat.ofHom a)
        (CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom ψ') := by
      have e₁ : CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom ψ = X.g.appLE W U.1 hUW := by
        ext1
        exact hψf
      have e₂ : CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom ψ' =
          (X'.g).appLE W' T inf_le_right := by
        ext1
        exact MvPolynomial.eval₂Hom_comp_C _ _
      rw [e₁, e₂]
      exact P₁
    have Q := outer.of_left (CommRingCat.hom_ext hcomp) t
    have hψ' : ψ'.Flat := RingHom.Flat.isStableUnderBaseChange.of_isPushout
      RingHom.Flat.respectsIso Q (RingHom.Etale.iff_flat_and_formallyUnramified.mp hψ).1
    have hJ := hideal ⟨T, hT⟩ U inf_le_left
    refine ⟨⟨T, hT⟩, U, inf_le_left, ⟨hxU, hxW'⟩, hJ.ge, ?_⟩
    refine Ideal.isPushout_extendedReesAlgebraMap_of_eq_map_mvPolynomialOrigin κ ψ ψ' a
      (RingHom.Etale.iff_flat_and_formallyUnramified.mp hψ).1 hψ' hcomp _ _ hI ?_ _
    rw [hJ, hI]
    exact Ideal.map_map_mvPolynomialOrigin κ ψ ψ' a hcomp
  · let O : X.V.Opens :=
      ⟨(Set.range X.s)ᶜ, X.s.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    obtain ⟨U, hU, hxU, hUO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X.V.isBasis_affineOpens (U := O) hx
    obtain ⟨U', hU', hxU', hU'U⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      X'.V.isBasis_affineOpens (U := sq.map ⁻¹ᵁ U) hxU
    have hI : X.s.ker.siteIdeal ⟨U, hU⟩ = ⊤ := by
      rw [Scheme.IdealSheafData.siteIdeal, Scheme.Hom.ker_apply,
        Ideal.eq_top_iff_one, RingHom.mem_ker]
      have he : X.s ⁻¹ᵁ U = ⊥ := eq_bot_iff.mpr fun b hb ↦ hUO hb ⟨b, rfl⟩
      have : Subsingleton Γ(B, X.s ⁻¹ᵁ U) := by rw [he]; infer_instance
      exact Subsingleton.elim _ _
    have hJ := hideal ⟨U', hU'⟩ ⟨U, hU⟩ hU'U
    refine ⟨⟨U', hU'⟩, ⟨U, hU⟩, hU'U, hxU', hJ.ge, ?_⟩
    apply Ideal.isPushout_extendedReesAlgebraMap_of_eq_top _ _ _ hI
    rw [hJ, hI, Ideal.map_top]

/-- The Rees comparison commutes with every allowed base change, including nonflat
ones, and with etale maps of pairs. The centre and augmentation are the actual ones.
Source: composition coherence Step 1, DNC geometry base-change clause
(blueprint: lem-pur-section-etale-restriction-coherence).
Proof: centred etale coordinates present the source ideal by the coordinate variables.
The corresponding extended-Rees algebra is the polynomial algebra in t and x_i/t.
Its coefficientwise comparison is a pushout under arbitrary coefficient base change.
Glue these pushouts and their augmentation equations. On every affine restriction,
two etale/base composites fix t and send f/t to the same pulled-back coefficient/t,
so they agree. This also proves the one-fibre comparison equation. -/
theorem reesBaseGeometry (P : PurityFiniteSetting.{u}) {B' B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB' : B' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB'] [QuasiCompact aB']
    {b : B' ⟶ B} {X' : Pair B' d} {X : Pair B d} (sq : BaseChange b X' X) :
    IsPullback (reesBaseMap sq) (familyPair X').g (familyPair X).g
      (AffineSpace.map (ULift.{u} (Fin 1)) b) ∧
    (familyPair X').s ≫ reesBaseMap sq =
      AffineSpace.map (ULift.{u} (Fin 1)) b ≫ (familyPair X).s ∧
    Scheme.Hom.deformationSpaceOneFibre X'.g X'.s ≫ reesBaseMap sq =
      sq.map ≫ Scheme.Hom.deformationSpaceOneFibre X.g X.s := by
  have hc := SectionReesBaseChange.pairMap_compatible X.g X'.g X.s X'.s sq.map b
    sq.section_eq sq.square.w
  refine ⟨?_, hc.2.1, hc.2.2.1⟩
  apply Scheme.IdealSheafData.isPullback_deformationSpaceMap_proj
    sq.map X.s.ker X'.s.ker _ (g := X.g) (g' := X'.g) (b := b) (sq := sq.square)
  intro x
  obtain ⟨U', U, hU, hx, _, H⟩ := reesBaseCover sq x
  exact ⟨U', U, hU, hx, H⟩

/-- The induced square of actual deformation pairs under arbitrary base change.
Source: DNC base-change geometry
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def familyBaseChange (P : PurityFiniteSetting.{u}) {B' B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB' : B' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB'] [QuasiCompact aB']
    {b : B' ⟶ B} {X' : Pair B' d} {X : Pair B d} (sq : BaseChange b X' X) :
    BaseChange (AffineSpace.map (ULift.{u} (Fin 1)) b) (familyPair X') (familyPair X) :=
  ⟨reesBaseMap sq, (reesBaseGeometry P aB aB' sq).1,
    (reesBaseGeometry P aB aB' sq).2.1⟩

/-- The canonical normal comparison under base change, as the unique lift through the
zero-fibre pullback. Its first component is the quotient by t of the Rees comparison.
Source: DNC geometry, base change and zero fibre
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def normalBaseMap (P : PurityFiniteSetting.{u}) {B' B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB' : B' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB'] [QuasiCompact aB']
    {b : B' ⟶ B} {X' : Pair B' d} {X : Pair B d} (sq : BaseChange b X' X) :
    (normalPair P aB' X').V ⟶ (normalPair P aB X).V :=
  (Scheme.Hom.isPullback_normalConeToDeformationSpace X.g X.s).lift
    (X'.s.ker.normalConeToDeformationSpace ≫ reesBaseMap sq)
    ((normalPair P aB' X').g ≫ b) (by
      change (X'.s.ker.normalConeToDeformationSpace ≫ reesBaseMap sq) ≫
          Scheme.Hom.deformationSpaceProj X.g X.s =
        (Scheme.Hom.normalConeProj X'.g X'.s ≫ b) ≫
          AffineSpace.zeroSection (ULift.{u} (Fin 1)) B
      have he : reesBaseMap sq ≫ Scheme.Hom.deformationSpaceProj X.g X.s =
          Scheme.Hom.deformationSpaceProj X'.g X'.s ≫
            AffineSpace.map (ULift.{u} (Fin 1)) b :=
        (reesBaseGeometry P aB aB' sq).1.w
      rw [Category.assoc, he, ← Category.assoc,
        (Scheme.Hom.isPullback_normalConeToDeformationSpace X'.g X'.s).w,
        Category.assoc, AffineSpace.zeroSection_comp_map, ← Category.assoc])

/-- The normal comparison is Cartesian and preserves zero sections under every
base change, and its functoriality with etale maps is the quotient of Rees functoriality.
Source: DNC geometry, clauses (1) and (5)
(blueprint: lem-pur-section-etale-restriction-coherence).
Proof: the zero-fibre inclusion is a pullback of t=0. Base-change the Rees pullback
and use pullback pasting to obtain the asserted normal pullback. The unique lift
normalBaseMap has the stated zero-section identity, because both composites agree
through the closed zero-fibre inclusion. The same uniqueness shows that two
etale/base-change composites of normal maps agree. -/
theorem normalBaseGeometry (P : PurityFiniteSetting.{u}) {B' B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB' : B' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB'] [QuasiCompact aB']
    {b : B' ⟶ B} {X' : Pair B' d} {X : Pair B d} (sq : BaseChange b X' X) :
    IsPullback (normalBaseMap P aB aB' sq) (normalPair P aB' X').g
      (normalPair P aB X).g b ∧
    (normalPair P aB' X').s ≫ normalBaseMap P aB aB' sq =
      b ≫ (normalPair P aB X).s := by
  have hrees := reesBaseGeometry P aB aB' sq
  have hzero := Scheme.Hom.isPullback_normalConeToDeformationSpace X.g X.s
  have hzero' := Scheme.Hom.isPullback_normalConeToDeformationSpace X'.g X'.s
  have hfst : normalBaseMap P aB aB' sq ≫ X.s.ker.normalConeToDeformationSpace =
      X'.s.ker.normalConeToDeformationSpace ≫ reesBaseMap sq :=
    hzero.lift_fst _ _ _
  have hsnd : normalBaseMap P aB aB' sq ≫ (normalPair P aB X).g =
      (normalPair P aB' X').g ≫ b := hzero.lift_snd _ _ _
  constructor
  · have outer := hzero'.paste_horiz hrees.1
    rw [AffineSpace.zeroSection_comp_map, ← hfst] at outer
    exact outer.of_right hsnd hzero
  · apply hzero.hom_ext
    · dsimp only [normalPair]
      simp only [Category.assoc, hfst]
      rw [← Category.assoc,
        Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace,
        Category.assoc]
      have he := hrees.2.1
      dsimp only [familyPair] at he
      rw [he, ← Category.assoc, AffineSpace.zeroSection_comp_map, Category.assoc,
        Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace]
    · have he := hsnd
      dsimp only [normalPair] at he ⊢
      rw [Category.assoc, he, ← Category.assoc,
        Scheme.Hom.normalConeZeroSection_normalConeProj X'.section_eq,
        Category.assoc, Scheme.Hom.normalConeZeroSection_normalConeProj X.section_eq,
        Category.id_comp, Category.comp_id]

/-- The actual square of normal zero-section pairs under base change.
Source: DNC geometry, base-change clause
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def normalBaseChange (P : PurityFiniteSetting.{u}) {B' B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB' : B' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB'] [QuasiCompact aB']
    {b : B' ⟶ B} {X' : Pair B' d} {X : Pair B d} (sq : BaseChange b X' X) :
    BaseChange b (normalPair P aB' X') (normalPair P aB X) :=
  ⟨normalBaseMap P aB aB' sq, (normalBaseGeometry P aB aB' sq).1,
    (normalBaseGeometry P aB aB' sq).2⟩

/-- Pullback pasting for one or zero sections of the affine line, in canonical order.
Source: DNC endpoint comparisons and derived pullback composition
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def endpointPull (P : PurityFiniteSetting.{u}) {B' B : Scheme.{u}} (b : B' ⟶ B)
    (i : B ⟶ AffineSpace (ULift.{u} (Fin 1)) B)
    (i' : B' ⟶ AffineSpace (ULift.{u} (Fin 1)) B')
    (hi : i' ≫ AffineSpace.map (ULift.{u} (Fin 1)) b = b ≫ i)
    (F : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology (AffineSpace (ULift.{u} (Fin 1)) B))
      (ModuleCat.{u + 1} P.Coefficient))) :=
  ((ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) b i).app F).symm ≪≫
    (ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) hi.symm).app F ≪≫
    (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) i'
      (AffineSpace.map (ULift.{u} (Fin 1)) b)).app F

/-- The standard rank-zero pair, represented by the canonically identical B over B.
Source: DNC geometry, standard pair in rank zero
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def standardZero (B : Scheme.{u}) : Pair B 0 where
  V := B
  g := 𝟙 B
  s := 𝟙 B
  smooth := inferInstance
  separated := inferInstance
  quasiCompact := inferInstance
  closed := inferInstance
  section_eq := Category.id_comp _

/-- For the zero ideal, the extended Rees algebra is the polynomial algebra.
Check bijectivity of the polynomial-to-Rees map on each affine open and glue. -/
private theorem polynomialToRees_isIso {V : Scheme.{u}} (I : V.IdealSheafData)
    (hI : I = ⊥) :
    IsIso (Scheme.AffineZariskiSite.relativeGluingMap V.coequifibered_toPolynomialPresheaf
      I.coequifibered_toReesPresheaf I.polynomialToRees) := by
  apply Scheme.AffineZariskiSite.relativeGluingMap_of_forall _
    (MorphismProperty.isomorphisms Scheme) _ _
    I.toPolynomialPresheaf_comp_polynomialToRees
  intro U
  have he : I.siteIdeal U = ⊥ := by
    subst I
    rfl
  have hinj : Function.Injective (I.siteIdeal U).toExtendedReesAlgebra := by
    intro x y h
    exact Polynomial.toLaurent_injective (congrArg Subtype.val h)
  have hsurj : Function.Surjective (I.siteIdeal U).toExtendedReesAlgebra := by
    intro x
    have hx := Ideal.mapRingHom_mem_range_toLaurent (I := I.siteIdeal U)
      (RingHom.id Γ(V, U.1)) (by rw [he]; exact bot_le) x.property
    simp only [LaurentPolynomial.mapRingHom_id] at hx
    obtain ⟨p, hp⟩ := hx
    exact ⟨p, Subtype.ext hp⟩
  have : IsIso (I.polynomialToRees.app (.op U)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
  infer_instance

/-- Both projections of the rank-zero standard deformation are canonical isomorphisms.
Source: DNC geometry, standard pair clause
(blueprint: lem-pur-section-etale-restriction-coherence).
Proof: the identity centre has zero ideal. Its extended-Rees algebra is R[t], and its
associated-graded algebra is R concentrated in degree zero. Thus both displayed
projections are the corresponding relative-spectrum identities, with their augmentations
as inverses; glue these identities over the affine cover of B. -/
theorem standardZeroGeometry (P : PurityFiniteSetting.{u}) {B : Scheme.{u}}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    IsIso (normalPair P aB (standardZero B)).g ∧
      IsIso (familyPair (standardZero B)).g := by
  have he : (𝟙 B : B ⟶ B).ker = ⊥ := Scheme.Hom.ker_eq_bot_of_isIso _
  have hi := polynomialToRees_isIso (𝟙 B : B ⟶ B).ker he
  have hf : IsIso (familyPair (standardZero B)).g := by
    dsimp only [familyPair, standardZero, Scheme.Hom.deformationSpaceProj]
    change IsIso (((𝟙 B : B ⟶ B).ker.deformationSpaceToPolynomialSpec ≫
      B.polynomialSpecToAffineSpace) ≫ AffineSpace.map (ULift.{u} (Fin 1)) (𝟙 B))
    have : IsIso (𝟙 B : B ⟶ B).ker.deformationSpaceToPolynomialSpec := hi
    infer_instance
  exact ⟨(Scheme.Hom.isPullback_normalConeToDeformationSpace
    (𝟙 B) (𝟙 B)).isIso_snd_of_isIso hf, hf⟩

/-- The canonical collapse of the rank-zero standard normal pair to the identity pair.
Source: DNC geometry, standard rank-zero comparisons
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def standardZeroNormalMap (P : PurityFiniteSetting.{u}) {B : Scheme.{u}}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    EtaleMap (normalPair P aB (standardZero B)) (standardZero B) :=
  letI := (standardZeroGeometry P aB).1
  { map := (normalPair P aB (standardZero B)).g
    etale := inferInstance
    separated := inferInstance
    quasiCompact := inferInstance
    over_eq := Category.comp_id _
    section_eq := (normalPair P aB (standardZero B)).section_eq
    centres := IsPullback.of_vert_isIso
      ⟨by
        change (normalPair P aB (standardZero B)).s ≫
          (normalPair P aB (standardZero B)).g = 𝟙 B
        exact (normalPair P aB (standardZero B)).section_eq⟩ }

/-- The identity and composition equations, stated uniformly for all smooth pairs.
Applying them to familyPair and normalPair gives the corresponding family and
normal endpoint equations, and d = 0 and the empty base are included.
Source: composition coherence Step 1
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def Composition (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB] (d : ℕ),
    (∀ X : Pair B d, restriction P aB (EtaleMap.id X) = Iso.refl _) ∧
    (∀ (X'' X' X : Pair B d) (b : EtaleMap X'' X') (a : EtaleMap X' X),
      restriction P aB (b.comp a) = restriction P aB b ≪≫ restriction P aB a) ∧
    (∀ (X'' X' X : Pair B d) (b : EtaleMap X'' X') (a : EtaleMap X' X),
      deformationMap (b.comp a) = deformationMap b ≫ deformationMap a ∧
      normalMap P aB (b.comp a) = normalMap P aB b ≫ normalMap P aB a ∧
      familyRestriction P aB (b.comp a) =
        familyRestriction P aB b ≪≫ familyRestriction P aB a ∧
      restriction P aB (normalEtaleMap P aB (b.comp a)) =
        restriction P aB (normalEtaleMap P aB b) ≪≫
          restriction P aB (normalEtaleMap P aB a)) ∧
    (∀ X : Pair B d, deformationMap (EtaleMap.id X) = 𝟙 _ ∧
      normalMap P aB (EtaleMap.id X) = 𝟙 _)

/-- Canonical smooth section base change commutes with restriction, for every allowed
base map and every pair of Cartesian pullback squares, including further restrictions.
The same assertion applied to deformation and normal pairs supplies base-change
compatibility of their restriction maps. No flatness is assumed.
Source: composition coherence Step 1, smooth base-change pasting
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def BaseCompatibility (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ (B B₀ : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB₀ : B₀ ⟶ Spec (.of P.field.k))
    [IsSeparated aB₀] [LocallyOfFiniteType aB₀] [QuasiCompact aB₀]
    (b : B₀ ⟶ B) (_hb : b ≫ aB = aB₀) (d : ℕ)
    (X' X : Pair B d) (X₀' X₀ : Pair B₀ d)
    (a : EtaleMap X' X) (a₀ : EtaleMap X₀' X₀)
    (sq : BaseChange b X₀ X) (sq' : BaseChange b X₀' X')
    (_ha : a₀.map ≫ sq.map = sq'.map ≫ a.map),
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (restriction P aB a) ≪≫ baseComparison P aB aB₀ sq =
      baseComparison P aB aB₀ sq' ≪≫ restriction P aB₀ a₀ ∧
    deformationMap a₀ ≫ reesBaseMap sq = reesBaseMap sq' ≫ deformationMap a ∧
    normalMap P aB₀ a₀ ≫ normalBaseMap P aB aB₀ sq =
      normalBaseMap P aB aB₀ sq' ≫ normalMap P aB a

/-- Family restriction reads at one and zero as precisely R_a and R_n, and intertwines
the unique deformation maps. This is an equality of actual derived isomorphisms.
Source: orientation charts Step 3, normalized deformation uniqueness
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def Endpoints (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) (X' X : Pair B d) (a : EtaleMap X' X),
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso
          (familyRestriction P aB a) ≪≫ endpointOne P aB X =
      endpointOne P aB X' ≪≫ restriction P aB a) ∧
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso
          (familyRestriction P aB a) ≪≫ endpointZero P aB X =
      endpointZero P aB X' ≪≫ restriction P aB (normalEtaleMap P aB a)) ∧
    (delta P aB X' ≪≫ restriction P aB (normalEtaleMap P aB a) =
      restriction P aB a ≪≫ delta P aB X)

/-- Endpoint comparisons and the normalized deformation commute with every base
restriction; together with BaseCompatibility this includes their further open and etale
restrictions. The base map is arbitrary among the separated finite-type k-schemes.
Source: composition coherence Step 1 and DNC normalization uniqueness
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def NormalizedBase (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ (B B₀ : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB₀ : B₀ ⟶ Spec (.of P.field.k))
    [IsSeparated aB₀] [LocallyOfFiniteType aB₀] [QuasiCompact aB₀]
    (b : B₀ ⟶ B) (_hb : b ≫ aB = aB₀) (d : ℕ)
    (X : Pair B d) (X₀ : Pair B₀ d) (sq : BaseChange b X₀ X),
    (endpointPull P b _ _ (AffineSpace.oneSection_comp_map b)
        (invariant P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) (familyPair X)) ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) B₀)).leftDerivedFunctor.mapIso
          (baseComparison P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB)
            ((AffineSpace (ULift.{u} (Fin 1)) B₀ ↘ B₀) ≫ aB₀)
            (familyBaseChange P aB aB₀ sq)) ≪≫ endpointOne P aB₀ X₀ =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (endpointOne P aB X) ≪≫ baseComparison P aB aB₀ sq) ∧
    (endpointPull P b _ _ (AffineSpace.zeroSection_comp_map b)
        (invariant P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) (familyPair X)) ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B₀)).leftDerivedFunctor.mapIso
          (baseComparison P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB)
            ((AffineSpace (ULift.{u} (Fin 1)) B₀ ↘ B₀) ≫ aB₀)
            (familyBaseChange P aB aB₀ sq)) ≪≫ endpointZero P aB₀ X₀ =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (endpointZero P aB X) ≪≫
          baseComparison P aB aB₀ (normalBaseChange P aB aB₀ sq)) ∧
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (delta P aB X) ≪≫ baseComparison P aB aB₀ (normalBaseChange P aB aB₀ sq) =
      baseComparison P aB aB₀ sq ≪≫ delta P aB₀ X₀)

/-- The canonical section base comparisons preserve identities and successive base
restriction, with the actual derived pullback constraints. This applies also to every
normal or family pair, so all equations remain coherent under repeated restrictions.
Source: smooth base-change pasting in composition coherence Step 1
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def BasePasting (P : PurityFiniteSetting.{u}) : Prop :=
  (∀ (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB] (d : ℕ) (X : Pair B d),
    baseComparison P aB aB (BaseChange.id X) =
      (ProEtale.leftDerivedUpperStarId
        (ModuleCat.{u + 1} P.Coefficient) B).app (invariant P aB X)) ∧
  (∀ (B B₁ B₂ : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB₁ : B₁ ⟶ Spec (.of P.field.k))
    [IsSeparated aB₁] [LocallyOfFiniteType aB₁] [QuasiCompact aB₁]
    (aB₂ : B₂ ⟶ Spec (.of P.field.k))
    [IsSeparated aB₂] [LocallyOfFiniteType aB₂] [QuasiCompact aB₂]
    (b₁ : B₁ ⟶ B) (_h₁ : b₁ ≫ aB = aB₁) (b₂ : B₂ ⟶ B₁) (_h₂ : b₂ ≫ aB₁ = aB₂)
    (d : ℕ) (X : Pair B d) (X₁ : Pair B₁ d) (X₂ : Pair B₂ d)
    (sq₁ : BaseChange b₁ X₁ X) (sq₂ : BaseChange b₂ X₂ X₁),
    baseComparison P aB aB₂ (sq₂.comp sq₁) =
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        b₂ b₁).app (invariant P aB X) ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b₂).leftDerivedFunctor.mapIso
        (baseComparison P aB aB₁ sq₁) ≪≫ baseComparison P aB₁ aB₂ sq₂)

/-- In rank zero the deformation map is the identity after the canonical normal
projection identification with the standard identity pair.
Source: DNC standard pair and normalization at one
(blueprint: lem-pur-section-etale-restriction-coherence). -/
def RankZero (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB],
    delta P aB (standardZero B) ≪≫ restriction P aB (standardZeroNormalMap P aB) =
      Iso.refl (invariant P aB (standardZero B))

end WeilConjectures.PurityFiniteSetting.SectionRestriction
