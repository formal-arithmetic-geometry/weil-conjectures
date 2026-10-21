/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.EtaleImmersionShriekNormalization

/-! # The specified compact-support comparison of an equal factored chart

Source: Stacks Project, Tags 0F7I, 0F7J and 0F7K; blueprint main-20261015,
opening and final paragraphs of sk-prop-sf-rf-shriek-preservation
(blueprint: lem-sf-etale-chart-left-compositor).

The helpers transport the existing canonical comparisons through the fully faithful
inclusions of D+. They construct the specified transformation, including its equality
transport, rather than choosing an isomorphism between its endpoint objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The existing open normalization, read in D+ by full faithfulness of its inclusion.
Source: Stacks Project, Tag 0F7I (blueprint: lem-sf-etale-chart-left-compositor). -/
noncomputable def etaleChartOpenNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W T : Scheme.{u}} (j : W ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (d : Compactification j) :
    rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility _ d ≪≫
      etaleOpenCompactSupportNormalization A j d ≪≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlusCompatibility.symm)

/-- The existing closed normalization, read in D+ by full faithfulness of its inclusion.
Source: Stacks Project, Tags 0F7I and 0F51
(blueprint: lem-sf-etale-chart-left-compositor). -/
noncomputable def etaleChartClosedNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z T : Scheme.{u}} (c : Z ⟶ T) [IsClosedImmersion c]
    (d : Compactification c) :
    rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d ≅
      (lowerStar (ModuleCat.{u + 1} A) c).mapDerivedCategoryPlus :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility _ d ≪≫
      etaleClosedCompactSupportNormalization A c d ≪≫
      (lowerStar (ModuleCat.{u + 1} A) c).mapDerivedCategoryPlusCompatibility.symm)

/-- The canonical compositor with three explicitly supplied compactifications, obtained
from the recorded compositor by the canonical changes of choice.
Source: Stacks Project, Tag 0F7J (blueprint: lem-sf-etale-chart-left-compositor). -/
noncomputable def etaleChartCompactSupportCompositor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g)) :
    rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cf ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cg ≅
      rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cfg := by
  letI := cf.hasCompactification
  letI := cg.hasCompactification
  letI := cfg.hasCompactification
  exact Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationPlusIso A cf
        (HasCompactification.compactification f)) _ ≪≫
    Functor.isoWhiskerLeft (rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f)
      (rightDerivedLowerShriekOfCompactificationPlusIso A cg
        (HasCompactification.compactification g)) ≪≫
    rightDerivedLowerShriekPlusCompIso A f g ≪≫
    rightDerivedLowerShriekOfCompactificationPlusIso A
      (HasCompactification.compactification (f ≫ g)) cfg

/-- Substitution along the chart equality, followed by the canonical change between the
compactifications of the now identical morphism. Equality elimination supplies the transport.
Source: Stacks Project, Tag 0F7I (blueprint: lem-sf-etale-chart-left-compositor). -/
noncomputable def etaleChartCompactSupportTransport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} [QuasiCompact f] [QuasiCompact g]
    (h : f = g) (cf : Compactification f) (cg : Compactification g) :
    rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cf ≅
      rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cg := by
  subst g
  exact rightDerivedLowerShriekOfCompactificationPlusIso A cf cg

private lemma chartHcomp_trans
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G H : C ⥤ D} {I J K : D ⥤ E}
    (a : F ≅ G) (b : G ≅ H) (c : I ≅ J) (d : J ≅ K) :
    NatIso.hcomp (a ≪≫ b) (c ≪≫ d) =
      NatIso.hcomp a c ≪≫ NatIso.hcomp b d := by
  ext X
  simp [NatIso.hcomp, NatTrans.hcomp, NatTrans.naturality_assoc]

private lemma chartHcomp_eq
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} {H I : D ⥤ E} (a : F ≅ G) (b : H ≅ I) :
    NatIso.hcomp a b =
      Functor.isoWhiskerRight a H ≪≫ Functor.isoWhiskerLeft G b := by
  ext X
  exact (b.hom.naturality (a.hom.app X)).symm

private lemma chartHcomp_refl_left
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) {H I : D ⥤ E} (b : H ≅ I) :
    NatIso.hcomp (Iso.refl F) b = Functor.isoWhiskerLeft F b := by
  ext X
  simp [NatIso.hcomp, NatTrans.hcomp]

private lemma chartHcomp_refl_right
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} (a : F ≅ G) (H : D ⥤ E) :
    NatIso.hcomp a (Iso.refl H) = Functor.isoWhiskerRight a H := by
  ext X
  simp [NatIso.hcomp, NatTrans.hcomp]

private lemma chartSquare_symm
    {C : Type*} [Category C] {X Y X' Y' : C}
    (a : X ≅ Y) (b : X' ≅ Y') (c : X ≅ X') (d : Y ≅ Y')
    (h : c ≪≫ b = a ≪≫ d) : d ≪≫ b.symm = a.symm ≪≫ c := by
  calc
    d ≪≫ b.symm = a.symm ≪≫ (a ≪≫ d) ≪≫ b.symm := by simp [Iso.trans_assoc]
    _ = a.symm ≪≫ (c ≪≫ b) ≪≫ b.symm := by rw [h]
    _ = a.symm ≪≫ c := by simp [Iso.trans_assoc]

private lemma chartSquare_conjugate
    {C : Type*} [Category C] {X Y X' Y' U V U' V' : C}
    (a : X ≅ Y) (b : X' ≅ Y') (c : X ≅ X') (d : Y ≅ Y')
    (u : U ≅ X) (u' : U' ≅ X') (v : Y ≅ V) (v' : Y' ≅ V')
    (h : c ≪≫ b = a ≪≫ d) :
    (u ≪≫ c ≪≫ u'.symm) ≪≫ (u' ≪≫ b ≪≫ v') =
      (u ≪≫ a ≪≫ v) ≪≫ (v.symm ≪≫ d ≪≫ v') := by
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id_assoc]
  rw [← Iso.trans_assoc c b v', h, Iso.trans_assoc]

private lemma chartSquare_refl
    {C : Type*} [Category C] {X Y : C} (c : X ≅ Y) :
    c ≪≫ Iso.refl Y = Iso.refl X ≪≫ c := by simp

private lemma chartSquare_trans
    {C : Type*} [Category C] {X Y Z X' Y' Z' : C}
    {a : X ≅ Y} {b : Y ≅ Z} {a' : X' ≅ Y'} {b' : Y' ≅ Z'}
    {c : X ≅ X'} {d : Y ≅ Y'} {e : Z ≅ Z'}
    (ha : c ≪≫ a' = a ≪≫ d) (hb : d ≪≫ b' = b ≪≫ e) :
    c ≪≫ (a' ≪≫ b') = (a ≪≫ b) ≪≫ e := by
  rw [← Iso.trans_assoc, ha, Iso.trans_assoc, hb, Iso.trans_assoc]

private lemma chartSquare_hcomp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G F' G' : C ⥤ D} {H I H' I' : D ⥤ E}
    {a : F ≅ G} {a' : F' ≅ G'} {b : H ≅ I} {b' : H' ≅ I'}
    {c : F ≅ F'} {d : G ≅ G'} {e : H ≅ H'} {k : I ≅ I'}
    (ha : c ≪≫ a' = a ≪≫ d) (hb : e ≪≫ b' = b ≪≫ k) :
    NatIso.hcomp c e ≪≫ NatIso.hcomp a' b' =
      NatIso.hcomp a b ≪≫ NatIso.hcomp d k := by
  rw [← chartHcomp_trans, ha, hb, chartHcomp_trans]

private lemma chartCancelRight_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G H : C ⥤ D} (I : D ⥤ E) [I.Full] [I.Faithful]
    (a : F ≅ G) (b : G ⋙ I ≅ H ⋙ I) :
    a ≪≫ Functor.fullyFaithfulCancelRight I b =
      Functor.fullyFaithfulCancelRight I (Functor.isoWhiskerRight a I ≪≫ b) := by
  ext X
  apply I.map_injective
  simp

private lemma chartOpenNormalization_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W T : Scheme.{u}} [IsNoetherian W] [IsNoetherian T]
    (j : W ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (c d : Compactification j) :
    rightDerivedLowerShriekOfCompactificationPlusIso A c d ≪≫
        etaleChartOpenNormalization A j d = etaleChartOpenNormalization A j c := by
  have hn := (etaleImmersionShriekNormalization A j (𝟙 T) c
    (Compactification.ofIsProper (𝟙 T))).2.2.2.2.2.1 d
  unfold etaleChartOpenNormalization
  rw [chartCancelRight_comp]
  congr 1
  rw [← hn]
  simp only [rightDerivedLowerShriekOfCompactificationPlusιIso, Iso.trans_assoc,
    Iso.self_symm_id_assoc]

private lemma chartClosedNormalization_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W T : Scheme.{u}} [IsNoetherian W] [IsNoetherian T]
    (j : W ⟶ T) [IsClosedImmersion j]
    (c d : Compactification j) :
    rightDerivedLowerShriekOfCompactificationPlusIso A c d ≪≫
        etaleChartClosedNormalization A j d = etaleChartClosedNormalization A j c := by
  have hn := (etaleImmersionShriekNormalization A (𝟙 T) j
    (Compactification.ofIsOpenImmersion (𝟙 T)) c).2.2.2.2.2.2 d
  unfold etaleChartClosedNormalization
  rw [chartCancelRight_comp]
  congr 1
  rw [← hn]
  simp only [rightDerivedLowerShriekOfCompactificationPlusιIso, Iso.trans_assoc,
    Iso.self_symm_id_assoc]

private lemma chartCompositor_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g)) :
    etaleChartCompactSupportCompositor A f g cf cg cfg =
      NatIso.hcomp
          (rightDerivedLowerShriekOfCompactificationPlusIso A cf
            (HasCompactification.compactification f))
          (rightDerivedLowerShriekOfCompactificationPlusIso A cg
            (HasCompactification.compactification g)) ≪≫
        rightDerivedLowerShriekPlusCompIso A f g ≪≫
        rightDerivedLowerShriekOfCompactificationPlusIso A
          (HasCompactification.compactification (f ≫ g)) cfg := by
  rw [chartHcomp_eq]
  simp only [etaleChartCompactSupportCompositor, rightDerivedLowerShriekPlus_eq,
    Iso.trans_assoc]

private lemma chartCompositor_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    (cf cf' : Compactification f) (cg cg' : Compactification g)
    (cfg cfg' : Compactification (f ≫ g)) :
    NatIso.hcomp (rightDerivedLowerShriekOfCompactificationPlusIso A cf cf')
        (rightDerivedLowerShriekOfCompactificationPlusIso A cg cg') ≪≫
        etaleChartCompactSupportCompositor A f g cf' cg' cfg' =
      etaleChartCompactSupportCompositor A f g cf cg cfg ≪≫
        rightDerivedLowerShriekOfCompactificationPlusIso A cfg cfg' := by
  let := cf.hasCompactification
  let := cg.hasCompactification
  let := cfg.hasCompactification
  rw [chartCompositor_eq, chartCompositor_eq]
  simp only [← Iso.trans_assoc]
  rw [← chartHcomp_trans,
    rightDerivedLowerShriekOfCompactificationPlusIso_trans,
    rightDerivedLowerShriekOfCompactificationPlusIso_trans]
  simp only [Iso.trans_assoc, rightDerivedLowerShriekOfCompactificationPlusIso_trans]

private lemma chartTransport_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} [QuasiCompact f] [QuasiCompact g]
    (h : f = g) (cf cf' : Compactification f) (cg cg' : Compactification g) :
    rightDerivedLowerShriekOfCompactificationPlusIso A cf cf' ≪≫
        etaleChartCompactSupportTransport A h cf' cg' =
      etaleChartCompactSupportTransport A h cf cg ≪≫
        rightDerivedLowerShriekOfCompactificationPlusIso A cg cg' := by
  subst g
  simp only [etaleChartCompactSupportTransport,
    rightDerivedLowerShriekOfCompactificationPlusIso_trans]

section Chart

variable (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U V P : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U] [IsNoetherian V] [IsNoetherian P]
    (f : X ⟶ Y) (s : U ⟶ X) (v : V ⟶ Y) (i : U ⟶ P) (p : P ⟶ V)
    [IsOpenImmersion s] [IsOpenImmersion v] [IsClosedImmersion i]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (h : s ≫ f = (i ≫ p) ≫ v)
    (cf : Compactification f) (cs : Compactification s) (cv : Compactification v)
    (ci : Compactification i) (cp : Compactification p)
    (csf : Compactification (s ≫ f)) (cip : Compactification (i ≫ p))
    (cipv : Compactification ((i ≫ p) ≫ v))

/-- The six specified arrows, with equality transport inserted between the middle values.
Every functor and every input in this construction belongs to D+.
Source: Stacks Project, Tags 0F7I, 0F7J, 0F7K
(blueprint: lem-sf-etale-chart-left-compositor). -/
noncomputable def etaleChartLeftCompositorPlus :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cf ≅
      (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cp ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus :=
  Functor.isoWhiskerRight (etaleChartOpenNormalization A s cs).symm _ ≪≫
    etaleChartCompactSupportCompositor A s f cs cf csf ≪≫
    etaleChartCompactSupportTransport A h csf cipv ≪≫
    (etaleChartCompactSupportCompositor A (i ≫ p) v cip cv cipv).symm ≪≫
    Functor.isoWhiskerRight
      (etaleChartCompactSupportCompositor A i p ci cp cip).symm _ ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (etaleChartClosedNormalization A i ci) _) _ ≪≫
    Functor.isoWhiskerLeft
      ((lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cp)
      (etaleChartOpenNormalization A v cv)

/-- The specified chart comparison in the ambient unbounded category, evaluated only on D+.
The endpoint compatibility maps identify the preceding six-arrow D+ construction with
Rf_! Ds_! and Dv_! Rp_! Di_* in the ordinary unbounded derived categories.
Source: Stacks Project, Tags 0F7J and 0F7K
(blueprint: lem-sf-etale-chart-left-compositor). -/
noncomputable def etaleChartLeftCompositor :
    DerivedCategory.Plus.ι ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) s).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf ≅
      DerivedCategory.Plus.ι ⋙ (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cp ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory :=
  Functor.isoWhiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility _ cf).symm ≪≫
    Functor.isoWhiskerRight
      (etaleChartLeftCompositorPlus A f s v i p h cf cs cv ci cp csf cip cipv)
      DerivedCategory.Plus.ι ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus
        (rightDerivedLowerShriekOfCompactificationPlusCompatibility _ cp))
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

private lemma chartLeftCompositorPlus_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U V P : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U] [IsNoetherian V] [IsNoetherian P]
    (f : X ⟶ Y) (s : U ⟶ X) (v : V ⟶ Y) (i : U ⟶ P) (p : P ⟶ V)
    [IsOpenImmersion s] [IsOpenImmersion v] [IsClosedImmersion i]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (h : s ≫ f = (i ≫ p) ≫ v)
    (cf : Compactification f) (cs : Compactification s) (cv : Compactification v)
    (ci : Compactification i) (cp : Compactification p)
    (csf : Compactification (s ≫ f)) (cip : Compactification (i ≫ p))
    (cipv : Compactification ((i ≫ p) ≫ v))
    (cf' : Compactification f) (cs' : Compactification s) (cv' : Compactification v)
    (ci' : Compactification i) (cp' : Compactification p)
    (csf' : Compactification (s ≫ f)) (cip' : Compactification (i ≫ p))
    (cipv' : Compactification ((i ≫ p) ≫ v)) :
    Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus
        (rightDerivedLowerShriekOfCompactificationPlusIso A cf cf') ≪≫
        etaleChartLeftCompositorPlus A f s v i p h cf' cs' cv' ci' cp' csf' cip' cipv' =
      etaleChartLeftCompositorPlus A f s v i p h cf cs cv ci cp csf cip cipv ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft
            (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus
            (rightDerivedLowerShriekOfCompactificationPlusIso A cp cp'))
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus := by
  let C {T S : Scheme.{u}} {q : T ⟶ S} [QuasiCompact q]
      (c d : Compactification q) := rightDerivedLowerShriekOfCompactificationPlusIso A c d
  have hs : C cs cs' ≪≫ etaleChartOpenNormalization A s cs' =
      etaleChartOpenNormalization A s cs ≪≫ Iso.refl _ := by
    simpa using chartOpenNormalization_change A s cs cs'
  have hi : C ci ci' ≪≫ etaleChartClosedNormalization A i ci' =
      etaleChartClosedNormalization A i ci ≪≫ Iso.refl _ := by
    simpa using chartClosedNormalization_change A i ci ci'
  have hv : C cv cv' ≪≫ etaleChartOpenNormalization A v cv' =
      etaleChartOpenNormalization A v cv ≪≫ Iso.refl _ := by
    simpa using chartOpenNormalization_change A v cv cv'
  have h₁ := chartSquare_hcomp (chartSquare_symm _ _ _ _ hs) (chartSquare_refl (C cf cf'))
  have h₂ := chartCompositor_change A s f cs cs' cf cf' csf csf'
  have h₃ := chartTransport_change A h csf csf' cipv cipv'
  have h₄ := chartSquare_symm _ _ _ _
    (chartCompositor_change A (i ≫ p) v cip cip' cv cv' cipv cipv')
  have h₅ := chartSquare_hcomp (chartSquare_symm _ _ _ _
    (chartCompositor_change A i p ci ci' cp cp' cip cip')) (chartSquare_refl (C cv cv'))
  have h₆ := chartSquare_hcomp (chartSquare_hcomp hi (chartSquare_refl (C cp cp')))
    (chartSquare_refl (C cv cv'))
  have h₇ := chartSquare_hcomp
    (chartSquare_refl (Functor.isoWhiskerLeft
      (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus (C cp cp'))) hv
  simp only [chartHcomp_refl_left, chartHcomp_refl_right] at h₁ h₅ h₆ h₇
  simpa only [etaleChartLeftCompositorPlus, Iso.trans_assoc] using
    chartSquare_trans h₁ (chartSquare_trans h₂ (chartSquare_trans h₃
      (chartSquare_trans h₄ (chartSquare_trans h₅ (chartSquare_trans h₆ h₇)))))

end Chart

/-- The constructed ambient chart isomorphism is natural on bounded-below inputs and
commutes with all canonical compactification changes. The definitions above specify its
six-factor value, including transport along h; its type asserts componentwise invertibility.

Source: Stacks Project, Tags 0F7I, 0F7J and 0F7K; blueprint main-20261015,
opening and final paragraphs of sk-prop-sf-rf-shriek-preservation
(blueprint: lem-sf-etale-chart-left-compositor).

Proof plan:
1. By lem-weil-pbc-module-sheaves-enough-injectives and
   lem-weil-pbc-dplus-injective-representative, represent any input with lower bound m by
   injectives vanishing below m. Extension by zero preserves that termwise bound. Resolve
   again with the same bound on the compactification; the resulting complex is K-injective.
   The construction def-amb-etale-compact-support computes Rr_* Dj_! by this complex,
   whose direct image still vanishes below m. Thus each compact-support intermediate is D+.
2. The exact immersion functors preserve the same bound by
   lem-sf-etale-immersion-shriek-normalization. Start with the inverse open normalization
   whiskered by Rf_!, then the (f,s) compositor of lem-amb-etale-compact-comparisons.
   Eliminate h to transport the middle value to the other factorization and apply the
   inverse (v,pi) compositor. These are the first three arrows of the specified formula.
3. Apply the inverse (p,i) compositor whiskered by Rv_!, then the closed normalization
   whiskered by Rp_! and Rv_!, then the open normalization for v at Rp_! Di_* H.
   All inputs are D+ by steps 1 and 2. These are the last three arrows of the formula.
4. Each arrow is an isomorphism. Reverse the arrows and take their inverses; associativity
   and adjacent inverse cancellations give both inverse equations.
5. Naturality of every normalization and compositor gives its component square. Inverse
   squares follow by multiplication by inverses; whiskered squares follow by applying the
   outer functor. Paste the six squares to obtain the displayed naturality equation.
6. For changed compactifications, use the canonical comparison at every intermediate
   functor. The compositor squares commute by lem-amb-etale-compact-comparisons, and the
   normalization squares by lem-sf-etale-immersion-shriek-normalization. Whisker and invert
   these squares as in step 5, then paste. Intermediate comparisons cancel, leaving exactly
   the endpoint equation below. Elimination of h handles equality transport, and the
   comparison cocycle law handles successive changes. -/
theorem etaleChartLeftCompositor_spec
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U V P : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U] [IsNoetherian V] [IsNoetherian P]
    (f : X ⟶ Y) (s : U ⟶ X) (v : V ⟶ Y) (i : U ⟶ P) (p : P ⟶ V)
    [IsOpenImmersion s] [IsOpenImmersion v] [IsClosedImmersion i]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (h : s ≫ f = (i ≫ p) ≫ v)
    (cf : Compactification f) (cs : Compactification s) (cv : Compactification v)
    (ci : Compactification i) (cp : Compactification p)
    (csf : Compactification (s ≫ f)) (cip : Compactification (i ≫ p))
    (cipv : Compactification ((i ≫ p) ≫ v)) :
    (∀ (H' H : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (a : H' ⟶ H),
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) s).mapDerivedCategory.map
            (DerivedCategory.Plus.ι.map a)) ≫
          (etaleChartLeftCompositor A f s v i p h cf cs cv ci cp csf cip cipv).hom.app H =
        (etaleChartLeftCompositor A f s v i p h cf cs cv ci cp csf cip cipv).hom.app H' ≫
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
            ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cp).map
              ((lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategory.map
                (DerivedCategory.Plus.ι.map a)))) ∧
    (∀ (cf' : Compactification f) (cs' : Compactification s) (cv' : Compactification v)
      (ci' : Compactification i) (cp' : Compactification p)
      (csf' : Compactification (s ≫ f)) (cip' : Compactification (i ≫ p))
      (cipv' : Compactification ((i ≫ p) ≫ v)),
      (Functor.isoWhiskerLeft
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus
          (rightDerivedLowerShriekOfCompactificationPlusιIso A cf cf')).hom ≫
          (etaleChartLeftCompositor A f s v i p h cf' cs' cv' ci' cp' csf' cip' cipv').hom =
        (etaleChartLeftCompositor A f s v i p h cf cs cv ci cp csf cip cipv).hom ≫
          (Functor.isoWhiskerRight
            (Functor.isoWhiskerLeft
              (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus
              (rightDerivedLowerShriekOfCompactificationPlusιIso A cp cp'))
            (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory).hom) := by
  constructor
  · intro H' H a
    exact (etaleChartLeftCompositor A f s v i p h cf cs cv ci cp csf cip cipv).hom.naturality a
  · intro cf' cs' cv' ci' cp' csf' cip' cipv'
    have hp := congrArg (fun e ↦ Functor.isoWhiskerRight e DerivedCategory.Plus.ι)
      (chartLeftCompositorPlus_change A f s v i p h cf cs cv ci cp csf cip cipv
        cf' cs' cv' ci' cp' csf' cip' cipv')
    simp only [Functor.isoWhiskerRight_trans] at hp
    have ha := chartSquare_conjugate _ _ _ _
      (Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus
        (rightDerivedLowerShriekOfCompactificationPlusCompatibility _ cf).symm)
      (Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus
        (rightDerivedLowerShriekOfCompactificationPlusCompatibility _ cf').symm)
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft
          (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus
          (rightDerivedLowerShriekOfCompactificationPlusCompatibility _ cp))
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory)
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft
          (lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlus
          (rightDerivedLowerShriekOfCompactificationPlusCompatibility _ cp'))
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory) hp
    apply NatTrans.ext
    funext K
    have hk := congrArg (fun e ↦ e.hom.app K) ha
    dsimp only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift] at hk
    simpa [etaleChartLeftCompositor,
      rightDerivedLowerShriekOfCompactificationPlusιIso, Category.assoc,
      Functor.mapDerivedCategoryPlus, ObjectProperty.lift, ← Functor.map_comp] using hk

end AlgebraicGeometry.Etale
