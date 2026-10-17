/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.CategoryTheory.FilteredComplexCanonicalModel
public import Sheaf.CategoryTheory.FilteredComplexDecalageTower
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis
import all Sheaf.Algebra.Homology.FilteredComplexBoundaryPullback

/-! # Representatives for the decalage page comparison

Source: Stacks Project, Tags 012K and 015X.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem representative_factors_decalage
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 1 ≤ r) :
    (U.filtration.decalage.complexStep (-q) (p + q)).Factors
      ((U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
        (U.filtration.step p).arrow.f (p + q)) := by
  rw [DecreasingFiltration.decalage_complexStep]
  have hp : -q + (p + q) = p := by omega
  rw [hp]
  have hf := (pullback_factors_iff _ _ _).mp
    (U.filtration.complexCycleRepresentatives p (p + q) r).factors_self
  apply (Subobject.inf_factors _).mpr
  refine ⟨Subobject.factors_left_of_inf_factors hf, ?_⟩
  have hd := Subobject.factors_right_of_inf_factors hf
  apply Subobject.factors_of_le _ _ hd
  apply (Subobject.pullback _).monotone
  dsimp only [DecreasingFiltration.complexStep]
  rw [imageSubobject_mono, imageSubobject_mono]
  apply Subobject.mk_le_mk_of_comm
    ((Subobject.ofLE (U.filtration.step (p + r)) (U.filtration.step (p + 1))
      (U.filtration.antitone_step (by omega))).f (p + q + 1))
  exact congrArg (fun f ↦ f.f (p + q + 1))
    (Subobject.ofLE_arrow (U.filtration.antitone_step (show p + 1 ≤ p + r by omega)))

/-- The unique restriction of an unquotiented cycle representative to decalage. -/
theorem filteredComplexDecalageRepresentative_exists_unique
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 1 ≤ r) :
    ∃! k : (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
        (U.filtration.decalage.step (-q) : CochainComplex C ℤ).X (p + q),
      k ≫ (U.filtration.decalage.step (-q)).arrow.f (p + q) =
        (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
          (U.filtration.step p).arrow.f (p + q) := by
  have hf := representative_factors_decalage U p q r hr
  rw [DecreasingFiltration.complexStep, imageSubobject_mono,
    Subobject.mk_factors_iff] at hf
  obtain ⟨k, hk⟩ := hf
  refine ⟨k, hk, ?_⟩
  intro k' hk'
  exact (cancel_mono _).1 (hk'.trans hk.symm)

/-- Restrict a representative to the degreewise decalage subobject. -/
noncomputable def filteredComplexDecalageRepresentative
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 1 ≤ r) :
    (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
      (U.filtration.decalage.step (-q) : CochainComplex C ℤ).X (p + q) :=
  (filteredComplexDecalageRepresentative_exists_unique U p q r hr).choose

@[reassoc]
theorem filteredComplexDecalageRepresentative_arrow
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 1 ≤ r) :
    filteredComplexDecalageRepresentative U p q r hr ≫
        (U.filtration.decalage.step (-q)).arrow.f (p + q) =
      (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
        (U.filtration.step p).arrow.f (p + q) :=
  (filteredComplexDecalageRepresentative_exists_unique U p q r hr).choose_spec.1

private theorem representative_d_factors_decalage
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    (U.filtration.decalage.complexStep (1 - q) (p + q + 1)).Factors
      ((U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
        (U.filtration.step p).arrow.f (p + q) ≫ U.obj.d (p + q) (p + q + 1)) := by
  rw [DecreasingFiltration.decalage_complexStep]
  have hp : 1 - q + (p + q + 1) = p + 2 := by omega
  rw [hp]
  apply (Subobject.inf_factors _).mpr
  constructor
  · have hf := (pullback_factors_iff _ _ _).mp
      (U.filtration.complexCycleRepresentatives p (p + q) r).factors_self
    have hd := (pullback_factors_iff _ _ _).mp
      (Subobject.factors_right_of_inf_factors hf)
    rw [Category.assoc] at hd
    apply Subobject.factors_of_le _ _ hd
    dsimp only [DecreasingFiltration.complexStep]
    let j := Subobject.ofLE (U.filtration.step (p + r)) (U.filtration.step (p + 2))
      (U.filtration.antitone_step (by omega))
    have hj := congrArg (fun f ↦ f.f (p + q + 1))
      (Subobject.ofLE_arrow (U.filtration.antitone_step (show p + 2 ≤ p + r by omega)))
    simp only [HomologicalComplex.comp_f] at hj
    simpa only [j, hj] using
      imageSubobject_comp_le (j.f (p + q + 1))
        ((U.filtration.step (p + 2)).arrow.f (p + q + 1))
  · apply (pullback_factors_iff _ _ _).mpr
    simp only [Category.assoc, U.obj.d_comp_d, comp_zero]
    exact Subobject.factors_zero

/-- A representative is a cycle modulo the next decalage step. -/
theorem filteredComplexDecalageRepresentative_cycle
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    (a : ℤ) (ha : a ≤ -q) :
    let Q := U.filtration.decalage.complexQuotient a (1 - q) (by omega)
    (filteredComplexDecalageRepresentative U p q r (by omega) ≫
        (Subobject.ofLE (U.filtration.decalage.step (-q))
          (U.filtration.decalage.step a)
          (U.filtration.decalage.antitone_step ha)).f (p + q) ≫
        (U.filtration.decalage.complexQuotientπ a (1 - q) (by omega)).f (p + q)) ≫
      Q.d (p + q) (p + q + 1) = 0 := by
  let Q := U.filtration.decalage.complexQuotient a (1 - q) (by omega)
  let l := Subobject.ofLE (U.filtration.decalage.step (-q))
    (U.filtration.decalage.step a) (U.filtration.decalage.antitone_step ha)
  let π := U.filtration.decalage.complexQuotientπ a (1 - q) (by omega)
  let k := filteredComplexDecalageRepresentative U p q r (by omega)
  have hd := representative_d_factors_decalage U p q r hr
  rw [DecreasingFiltration.complexStep, imageSubobject_mono,
    Subobject.mk_factors_iff] at hd
  obtain ⟨y, hy⟩ : ∃ y :
      (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
        (U.filtration.decalage.step (1 - q) : CochainComplex C ℤ).X (p + q + 1),
      y ≫ (U.filtration.decalage.step (1 - q)).arrow.f (p + q + 1) =
        (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
          (U.filtration.step p).arrow.f (p + q) ≫ U.obj.d (p + q) (p + q + 1) := hd
  have he : k ≫ l.f (p + q) ≫
      (U.filtration.decalage.step a : CochainComplex C ℤ).d (p + q) (p + q + 1) =
      y ≫ (Subobject.ofLE (U.filtration.decalage.step (1 - q))
        (U.filtration.decalage.step a)
        (U.filtration.decalage.antitone_step (by omega))).f (p + q + 1) := by
    apply (cancel_mono ((U.filtration.decalage.step a).arrow.f (p + q + 1))).1
    rw [Category.assoc, Category.assoc, ← (U.filtration.decalage.step a).arrow.comm]
    have hl : l.f (p + q) ≫ (U.filtration.decalage.step a).arrow.f (p + q) =
        (U.filtration.decalage.step (-q)).arrow.f (p + q) :=
      congrArg (fun f ↦ f.f (p + q))
        (Subobject.ofLE_arrow (U.filtration.decalage.antitone_step ha))
    simp only [Category.assoc, reassoc_of% hl,
      ← HomologicalComplex.comp_f, Subobject.ofLE_arrow]
    simpa only [Category.assoc, k] using
      (congrArg (fun f ↦ f ≫ U.obj.d (p + q) (p + q + 1))
        (filteredComplexDecalageRepresentative_arrow U p q r (by omega))).trans
          (by simpa only [Category.assoc] using hy.symm)
  change (k ≫ l.f (p + q) ≫ π.f (p + q)) ≫ Q.d (p + q) (p + q + 1) = 0
  simp only [Category.assoc]
  rw [π.comm]
  calc
    _ = (y ≫ (Subobject.ofLE (U.filtration.decalage.step (1 - q))
        (U.filtration.decalage.step a)
        (U.filtration.decalage.antitone_step (by omega))).f (p + q + 1)) ≫
        π.f (p + q + 1) := by
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ π.f (p + q + 1)) he
    _ = 0 := by
      simp only [Category.assoc, π, DecreasingFiltration.complexQuotientπ,
        ← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f, comp_zero]

/-- The cycle in a quotient of decalage steps represented by an original filtered cycle. -/
noncomputable def filteredComplexDecalageRepresentativeCycle
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    (a : ℤ) (ha : a ≤ -q) :
    (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
      (U.filtration.decalage.complexQuotient a (1 - q) (by omega)).cycles (p + q) :=
  HomologicalComplex.liftCycles _
    (filteredComplexDecalageRepresentative U p q r (by omega) ≫
      (Subobject.ofLE (U.filtration.decalage.step (-q)) (U.filtration.decalage.step a)
        (U.filtration.decalage.antitone_step ha)).f (p + q) ≫
      (U.filtration.decalage.complexQuotientπ a (1 - q) (by omega)).f (p + q))
    (p + q + 1) (by simp) (filteredComplexDecalageRepresentative_cycle U p q r hr a ha)

@[reassoc]
theorem filteredComplexDecalageRepresentativeCycle_i
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    (a : ℤ) (ha : a ≤ -q) :
    filteredComplexDecalageRepresentativeCycle U p q r hr a ha ≫
        (U.filtration.decalage.complexQuotient a (1 - q) (by omega)).iCycles (p + q) =
      filteredComplexDecalageRepresentative U p q r (by omega) ≫
        (Subobject.ofLE (U.filtration.decalage.step (-q)) (U.filtration.decalage.step a)
          (U.filtration.decalage.antitone_step ha)).f (p + q) ≫
        (U.filtration.decalage.complexQuotientπ a (1 - q) (by omega)).f (p + q) :=
  HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The class of a cycle representative in the larger right-hand decalage interval. -/
noncomputable def filteredComplexDecalageRepresentativeClass
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
      (U.filtration.decalageTowerInterval (q : EInt) ((q + (r - 1) : ℤ) : EInt)
        (by simp; omega)).X₃.homology
        (p + q) :=
  filteredComplexDecalageRepresentativeCycle U p q r hr (1 - (q + (r - 1))) (by omega) ≫
    (U.filtration.decalage.complexQuotient (1 - (q + (r - 1))) (1 - q)
      (by omega)).homologyπ (p + q)

/-- Embed a spectral-object page in the cohomology of its right-hand interval.
The two factors before the interval comparison are the canonical monomorphisms
from page homology to opcycles and from opcycles to interval cohomology. -/
noncomputable def filteredComplexDecalagePageEmbedding
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    ((((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence).page r hr).X
        (p, q) ⟶
      (U.filtration.decalageTowerInterval (q : EInt) ((q + (r - 1) : ℤ) : EInt)
        (by simp; omega)).X₃.homology
        (p + q) :=
  if h : r = 2 then by
    subst r
    exact
      (((filteredComplexDecalageSpectralObjectFunctor C).obj U).spectralSequenceFirstPageXIso
        Abelian.SpectralObject.coreE₂Cohomological (p, q) (q : EInt)
        ((q + (2 - 1) : ℤ) : EInt) rfl rfl (p + q) rfl).hom ≫
      (filteredComplexDecalageIntervalIso U (q : EInt) ((q + (2 - 1) : ℤ) : EInt)
        (by simp) (p + q)).hom
  else
    let X := (filteredComplexDecalageSpectralObjectFunctor C).obj U
    (X.spectralSequencePageXIso Abelian.SpectralObject.coreE₂Cohomological r hr (p, q)
      ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt)
      ((q + (r - 1) : ℤ) : EInt) rfl rfl rfl (by dsimp; congr 1; omega)
      (p + q - 1) (p + q) (p + q + 1) rfl).hom ≫
      (X.kernelSequenceE
        (homOfLE (by simp; omega : ((q - r + 2 : ℤ) : EInt) ≤ (q : EInt)))
        (homOfLE (by simp : (q : EInt) ≤ ((q + 1 : ℤ) : EInt)))
        (homOfLE (by simp; omega : ((q + 1 : ℤ) : EInt) ≤ ((q + (r - 1) : ℤ) : EInt)))
        (homOfLE (by simp; omega : (q : EInt) ≤ ((q + (r - 1) : ℤ) : EInt)))
        (Subsingleton.elim _ _) (p + q - 1) (p + q) (p + q + 1)).f ≫
      (filteredComplexDecalageIntervalIso U (q : EInt) ((q + (r - 1) : ℤ) : EInt)
        (by simp; omega) (p + q)).hom

instance filteredComplexDecalagePageEmbedding_mono
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    Mono (filteredComplexDecalagePageEmbedding U p q r hr) := by
  unfold filteredComplexDecalagePageEmbedding
  split_ifs with h
  · subst r
    infer_instance
  · infer_instance

/-- On page two the embedding is the usual first-page computation. -/
theorem filteredComplexDecalagePageEmbedding_two
    (U : FilteredObject (CochainComplex C ℤ)) (p q : ℤ) :
    filteredComplexDecalagePageEmbedding U p q 2 le_rfl =
      (((filteredComplexDecalageSpectralObjectFunctor C).obj U).spectralSequenceFirstPageXIso
        Abelian.SpectralObject.coreE₂Cohomological (p, q) (q : EInt)
        ((q + (2 - 1) : ℤ) : EInt) rfl rfl (p + q) rfl).hom ≫
      (filteredComplexDecalageIntervalIso U (q : EInt) ((q + (2 - 1) : ℤ) : EInt)
        (by simp) (p + q)).hom := by
  simp [filteredComplexDecalagePageEmbedding]

/-- Representative cohomology classes commute with filtered chain maps.
Source: Stacks Project, Tag 012K, functoriality of the cycle construction.
(blueprint: lem-sp-filtered-complex-decalage-representative-naturality).

Proof. The ambient representative square uniquely identifies the two maps into
D^(-q). The interval quotient squares then give equality of their cycle lifts
by monicity of the cycle inclusion. Compose with homologyπ and use its naturality. -/
@[reassoc]
theorem filteredComplexDecalageRepresentativeClass_naturality
    {U V : FilteredObject (CochainComplex C ℤ)} (t : U ⟶ V)
    (p q r : ℤ) (hr : 2 ≤ r)
    (ρ : (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
      (V.filtration.complexCycleRepresentatives p (p + q) r : C))
    (hρ : ρ ≫ (V.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
        (V.filtration.step p).arrow.f (p + q) =
      (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
        (U.filtration.step p).arrow.f (p + q) ≫ t.hom.f (p + q)) :
    ρ ≫ filteredComplexDecalageRepresentativeClass V p q r hr =
      filteredComplexDecalageRepresentativeClass U p q r hr ≫
        HomologicalComplex.homologyMap
          (DecreasingFiltration.decalageTowerIntervalMap t (q : EInt)
            ((q + (r - 1) : ℤ) : EInt) (by simp; omega)).τ₃ (p + q) := by
  let a := 1 - (q + (r - 1))
  let QU := U.filtration.decalage.complexQuotient a (1 - q) (by omega)
  let QV := V.filtration.decalage.complexQuotient a (1 - q) (by omega)
  let T := DecreasingFiltration.decalageTowerIntervalMap t (q : EInt)
    ((q + (r - 1) : ℤ) : EInt) (by simp; omega)
  let f : QU ⟶ QV := T.τ₃
  let kU := filteredComplexDecalageRepresentative U p q r (by omega)
  let kV := filteredComplexDecalageRepresentative V p q r (by omega)
  let lU := Subobject.ofLE (U.filtration.decalage.step (-q))
    (U.filtration.decalage.step a) (U.filtration.decalage.antitone_step (by dsimp [a]; omega))
  let lV := Subobject.ofLE (V.filtration.decalage.step (-q))
    (V.filtration.decalage.step a) (V.filtration.decalage.antitone_step (by dsimp [a]; omega))
  have hlU : lU.f (p + q) ≫ (U.filtration.decalage.step a).arrow.f (p + q) =
      (U.filtration.decalage.step (-q)).arrow.f (p + q) :=
    congrArg (fun f ↦ f.f (p + q)) (Subobject.ofLE_arrow
      (U.filtration.decalage.antitone_step (show a ≤ -q by dsimp [a]; omega)))
  have hlV : lV.f (p + q) ≫ (V.filtration.decalage.step a).arrow.f (p + q) =
      (V.filtration.decalage.step (-q)).arrow.f (p + q) :=
    congrArg (fun f ↦ f.f (p + q)) (Subobject.ofLE_arrow
      (V.filtration.decalage.antitone_step (show a ≤ -q by dsimp [a]; omega)))
  have ht : T.τ₂.f (p + q) ≫ (V.filtration.decalage.step a).arrow.f (p + q) =
      (U.filtration.decalage.step a).arrow.f (p + q) ≫ t.hom.f (p + q) :=
    congrArg (fun f ↦ f.f (p + q))
      (DecreasingFiltration.decalageTowerMap_app_arrow t ((q + (r - 1) : ℤ) : EInt))
  have hk : kU ≫ lU.f (p + q) ≫ T.τ₂.f (p + q) = ρ ≫ kV ≫ lV.f (p + q) := by
    apply (cancel_mono ((V.filtration.decalage.step a).arrow.f (p + q))).1
    simp only [Category.assoc, ht, reassoc_of% hlU, hlV]
    dsimp only [kU, kV]
    rw [filteredComplexDecalageRepresentative_arrow_assoc,
      filteredComplexDecalageRepresentative_arrow]
    exact hρ.symm
  have hπ : T.τ₂.f (p + q) ≫
        (V.filtration.decalage.complexQuotientπ a (1 - q) (by dsimp [a]; omega)).f
          (p + q) =
      (U.filtration.decalage.complexQuotientπ a (1 - q) (by dsimp [a]; omega)).f
          (p + q) ≫ f.f (p + q) :=
    congrArg (fun g ↦ g.f (p + q)) T.comm₂₃
  have hg :
      filteredComplexDecalageRepresentativeCycle U p q r hr a (by dsimp [a]; omega) ≫
          HomologicalComplex.cyclesMap f (p + q) =
        ρ ≫ filteredComplexDecalageRepresentativeCycle V p q r hr a
          (by dsimp [a]; omega) := by
    have hU : filteredComplexDecalageRepresentativeCycle U p q r hr a
          (by dsimp [a]; omega) ≫ QU.iCycles (p + q) =
        kU ≫ lU.f (p + q) ≫
          (U.filtration.decalage.complexQuotientπ a (1 - q)
            (by dsimp [a]; omega)).f (p + q) :=
      filteredComplexDecalageRepresentativeCycle_i U p q r hr a (by dsimp [a]; omega)
    have hV : filteredComplexDecalageRepresentativeCycle V p q r hr a
          (by dsimp [a]; omega) ≫ QV.iCycles (p + q) =
        kV ≫ lV.f (p + q) ≫
          (V.filtration.decalage.complexQuotientπ a (1 - q)
            (by dsimp [a]; omega)).f (p + q) :=
      filteredComplexDecalageRepresentativeCycle_i V p q r hr a (by dsimp [a]; omega)
    apply (cancel_mono (QV.iCycles (p + q))).1
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
    rw [← Category.assoc, hU, Category.assoc, hV]
    simp only [Category.assoc]
    rw [← hπ]
    simpa only [Category.assoc] using congrArg
      (fun g ↦ g ≫ (V.filtration.decalage.complexQuotientπ a (1 - q)
        (by dsimp [a]; omega)).f (p + q)) hk
  change ρ ≫ (filteredComplexDecalageRepresentativeCycle V p q r hr a
        (by dsimp [a]; omega) ≫ QV.homologyπ (p + q)) =
      (filteredComplexDecalageRepresentativeCycle U p q r hr a
        (by dsimp [a]; omega) ≫ QU.homologyπ (p + q)) ≫
          HomologicalComplex.homologyMap f (p + q)
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ QV.homologyπ (p + q)) hg.symm

private theorem decalage_boundary_factors_iff
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    {X : C} (x : X ⟶ U.obj.X (p + q))
    (hd : (U.filtration.complexStep (p + r) (p + q + 1)).Factors
      (x ≫ U.obj.d (p + q) (p + q + 1))) :
    ((U.filtration.complexStep p (p + q) ⊓
        (Subobject.«exists» (U.obj.d (p + q - 1) (p + q))).obj
          (U.filtration.complexStep (p - r + 1) (p + q - 1))) ⊔
        U.filtration.complexStep (p + 1) (p + q)).Factors x ↔
      ((U.filtration.decalage.complexStep (-q) (p + q) ⊓
        (Subobject.«exists» (U.obj.d (p + q - 1) (p + q))).obj
          (U.filtration.decalage.complexStep (1 - (q + (r - 1))) (p + q - 1))) ⊔
        U.filtration.decalage.complexStep (1 - q) (p + q)).Factors x := by
  let F := U.filtration
  let n := p + q
  let a := 1 - (q + (r - 1))
  let B := F.complexStep p n ⊓
    (Subobject.«exists» (U.obj.d (n - 1) n)).obj (F.complexStep (p - r + 1) (n - 1))
  let BD := F.decalage.complexStep (-q) n ⊓
    (Subobject.«exists» (U.obj.d (n - 1) n)).obj (F.decalage.complexStep a (n - 1))
  have hD (b m : ℤ) : F.decalage.complexStep b m ≤ F.complexStep (b + m) m := by
    rw [DecreasingFiltration.decalage_complexStep]
    exact inf_le_left
  have hDp : F.decalage.complexStep (-q) n ≤ F.complexStep p n := by
    convert hD (-q) n using 1; congr 1; dsimp [n]; omega
  have hDa : F.decalage.complexStep a (n - 1) ≤
      F.complexStep (p - r + 1) (n - 1) := by
    convert hD a (n - 1) using 1; congr 1; dsimp [a, n]; omega
  have hDN : F.decalage.complexStep (1 - q) n ≤ F.complexStep (p + 1) n := by
    convert hD (1 - q) n using 1; congr 1; dsimp [n]; omega
  change (B ⊔ F.complexStep (p + 1) n).Factors x ↔
    (BD ⊔ F.decalage.complexStep (1 - q) n).Factors x
  constructor
  · intro hx
    obtain ⟨X₁, e₁, he₁, y, f, hsum⟩ :=
      DecreasingFiltration.sup_refinement B (F.complexStep (p + 1) n) x hx
    have hy : (imageSubobject
        ((F.step (p - r + 1)).arrow.f (n - 1) ≫ U.obj.d (n - 1) n)).Factors
          (y ≫ B.arrow) := by
      have h := Subobject.factors_of_factors_right y
        (Subobject.inf_arrow_factors_right (F.complexStep p n)
          ((Subobject.«exists» (U.obj.d (n - 1) n)).obj
            (F.complexStep (p - r + 1) (n - 1))))
      have hd' : (Subobject.«exists» (U.obj.d (n - 1) n)).obj
          (F.complexStep (p - r + 1) (n - 1)) = imageSubobject
            ((F.step (p - r + 1)).arrow.f (n - 1) ≫ U.obj.d (n - 1) n) := by
        dsimp only [DecreasingFiltration.complexStep]
        rw [← Subobject.exists_obj_top ((F.step (p - r + 1)).arrow.f (n - 1)),
          Subobject.exists_obj_comp, Subobject.exists_obj_top]
      simpa only [hd'] using h
    obtain ⟨X₂, e₂, he₂, z, hz⟩ := DecreasingFiltration.image_refinement _ _ hy
    have hdf : (e₂ ≫ f ≫ (F.complexStep (p + 1) n).arrow) ≫
        U.obj.d n (n + 1) = (e₂ ≫ e₁) ≫ x ≫ U.obj.d n (n + 1) := by
      have hh := congrArg (fun t ↦ e₂ ≫ t ≫ U.obj.d n (n + 1)) hsum
      simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
        reassoc_of% hz, U.obj.d_comp_d, comp_zero, zero_add] at hh
      simpa only [Category.assoc] using hh.symm
    have hfD : (F.decalage.complexStep (1 - q) n).Factors
        (e₂ ≫ f ≫ (F.complexStep (p + 1) n).arrow) := by
      rw [DecreasingFiltration.decalage_complexStep]
      have hi : 1 - q + n = p + 1 := by dsimp [n]; omega
      rw [hi]
      apply (Subobject.inf_factors _).mpr
      refine ⟨by simpa only [Category.assoc] using
        Subobject.factors_comp_arrow (e₂ ≫ f), ?_⟩
      apply (pullback_factors_iff _ _ _).mpr
      rw [hdf]
      apply Subobject.factors_of_le _ _ (Subobject.factors_of_factors_right (e₂ ≫ e₁) hd)
      dsimp only [DecreasingFiltration.complexStep]
      rw [imageSubobject_mono, imageSubobject_mono]
      apply Subobject.mk_le_mk_of_comm
        ((Subobject.ofLE (F.step (p + r)) (F.step (p + 1 + 1))
          (F.antitone_step (by omega))).f (n + 1))
      exact congrArg (fun t ↦ t.f (n + 1))
        (Subobject.ofLE_arrow (F.antitone_step (show p + 1 + 1 ≤ p + r by omega)))
    have hzD : (F.decalage.complexStep a (n - 1)).Factors
        (z ≫ (F.step (p - r + 1)).arrow.f (n - 1)) := by
      rw [DecreasingFiltration.decalage_complexStep]
      have hi : a + (n - 1) = p - r + 1 := by dsimp [a, n]; omega
      rw [hi]
      apply (Subobject.inf_factors _).mpr
      refine ⟨imageSubobject_factors_comp_self _ _, ?_⟩
      apply (pullback_factors_iff _ _ _).mpr
      have hn : n - 1 + 1 = n := by omega
      rw [hn]
      simp only [Category.assoc]
      rw [← hz]
      have hyP := Subobject.factors_of_factors_right (e₂ ≫ y)
        (Subobject.inf_arrow_factors_left (F.complexStep p n)
          ((Subobject.«exists» (U.obj.d (n - 1) n)).obj
            (F.complexStep (p - r + 1) (n - 1))))
      simp only [Category.assoc] at hyP
      apply Subobject.factors_of_le _ _ hyP
      dsimp only [DecreasingFiltration.complexStep]
      rw [imageSubobject_mono, imageSubobject_mono]
      apply Subobject.mk_le_mk_of_comm
        ((Subobject.ofLE (F.step p) (F.step (p - r + 1 + 1))
          (F.antitone_step (by omega))).f n)
      exact congrArg (fun t ↦ t.f n)
        (Subobject.ofLE_arrow (F.antitone_step (show p - r + 1 + 1 ≤ p by omega)))
    have hyD : BD.Factors (e₂ ≫ y ≫ B.arrow) := by
      apply (Subobject.inf_factors _).mpr
      constructor
      · rw [DecreasingFiltration.decalage_complexStep]
        have hi : -q + n = p := by dsimp [n]; omega
        rw [hi]
        apply (Subobject.inf_factors _).mpr
        constructor
        · simpa only [B, Category.assoc] using
            (Subobject.factors_of_factors_right (e₂ ≫ y)
              (Subobject.inf_arrow_factors_left (F.complexStep p n)
                ((Subobject.«exists» (U.obj.d (n - 1) n)).obj
                  (F.complexStep (p - r + 1) (n - 1)))))
        · apply (pullback_factors_iff _ _ _).mpr
          simp only [Category.assoc]
          rw [reassoc_of% hz]
          simp only [U.obj.d_comp_d, comp_zero]
          exact Subobject.factors_zero
      · rw [hz, ← Category.assoc]
        apply (pullback_factors_iff (U.obj.d (n - 1) n)
          ((Subobject.«exists» (U.obj.d (n - 1) n)).obj
            (F.decalage.complexStep a (n - 1))) _).mp
        exact Subobject.factors_of_le _
          ((Subobject.gc_exists_pullback (U.obj.d (n - 1) n)).le_u_l
            (F.decalage.complexStep a (n - 1))) hzD
    apply DecreasingFiltration.factors_desc_epi
      (BD ⊔ F.decalage.complexStep (1 - q) n) x (e₂ ≫ e₁)
    rw [Category.assoc, hsum, Preadditive.comp_add]
    exact Subobject.factors_add _ _
      (Subobject.sup_factors_of_factors_left hyD)
      (Subobject.sup_factors_of_factors_right hfD)
  · intro hx
    exact Subobject.factors_of_le _
      (sup_le_sup (inf_le_inf hDp ((Subobject.«exists» _).monotone hDa)) hDN) hx

open DecreasingFiltration in
private theorem interval_boundary_zero_iff {K : CochainComplex C ℤ}
    (F : DecreasingFiltration K) (p a b n : ℤ) (ha : a ≤ p) (hb : p ≤ b)
    {X : C} (x : X ⟶ (F.step p : CochainComplex C ℤ).X n) :
    let ht := ha.trans hb
    let T := F.complexQuotient a b ht
    (x ≫ (Subobject.ofLE (F.step p) (F.step a)
      (F.antitone_step ha)).f n ≫ (F.complexQuotientπ a b ht).f n) ≫
        T.pOpcycles n = 0 ↔
    ((F.complexStep p n ⊓ (Subobject.«exists» (K.d (n - 1) n)).obj
      (F.complexStep a (n - 1))) ⊔ F.complexStep b n).Factors
      (x ≫ (F.step p).arrow.f n) := by
  let ht := ha.trans hb
  let A : CochainComplex C ℤ := F.step a
  let T := F.complexQuotient a b ht
  let q := F.complexQuotientπ a b ht
  let l := Subobject.ofLE (F.step p) (F.step a) (F.antitone_step ha)
  let i := Subobject.ofLE (F.step b) (F.step a) (F.antitone_step ht)
  let j := Subobject.ofLE (F.step b) (F.step p)
    (F.antitone_step hb)
  let D := F.complexStep p n ⊓ (Subobject.«exists» (K.d (n - 1) n)).obj
    (F.complexStep a (n - 1))
  let V := D ⊔ F.complexStep b n
  have hmA : Mono ((F.step a).arrow.f n) := by
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (F.step a).arrow)
    infer_instance
  have hmP : Mono ((F.step p).arrow.f n) := by
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (F.step p).arrow)
    infer_instance
  have hq := quotient_epi F a b (n - 1) ht
  have hl : l.f n ≫ (F.step a).arrow.f n = (F.step p).arrow.f n :=
    congrArg (fun f => f.f n) (Subobject.ofLE_arrow (F.antitone_step ha))
  have hi : i.f n ≫ (F.step a).arrow.f n = (F.step b).arrow.f n :=
    congrArg (fun f => f.f n) (Subobject.ofLE_arrow (F.antitone_step ht))
  have hj : j.f n ≫ (F.step p).arrow.f n = (F.step b).arrow.f n :=
    congrArg (fun f => f.f n) (Subobject.ofLE_arrow
      (F.antitone_step hb))
  have hd : (Subobject.«exists» (K.d (n - 1) n)).obj (F.complexStep a (n - 1)) =
      imageSubobject ((F.step a).arrow.f (n - 1) ≫ K.d (n - 1) n) := by
    dsimp only [complexStep]
    rw [← Subobject.exists_obj_top ((F.step a).arrow.f (n - 1)),
      Subobject.exists_obj_comp, Subobject.exists_obj_top]
  change (x ≫ l.f n ≫ q.f n) ≫ T.pOpcycles n = 0 ↔
    V.Factors (x ≫ (F.step p).arrow.f n)
  constructor
  · intro hx
    obtain ⟨X₁, e₁, he₁, y₁, hy₁⟩ :=
      (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
        (T.opcyclesIsCokernel (n - 1) n (by simp)) (x ≫ l.f n ≫ q.f n)).mp hx
    obtain ⟨X₂, e₂, he₂, y₂, hy₂⟩ :=
      surjective_up_to_refinements_of_epi (q.f (n - 1)) y₁
    have hdiff : (e₂ ≫ e₁ ≫ x ≫ l.f n - y₂ ≫ A.d (n - 1) n) ≫ q.f n = 0 := by
      rw [Preadditive.sub_comp]
      have hh := congrArg (fun f => e₂ ≫ f) hy₁
      simp only [Category.assoc]
      rw [← q.comm]
      rw [reassoc_of% hy₂] at hh
      simpa only [Category.assoc, sub_self] using congrArg
        (fun f => f - (y₂ ≫ q.f (n - 1) ≫ T.d (n - 1) n)) hh
    obtain ⟨X₃, e₃, he₃, f, hf⟩ :=
      (quotient_exact F a b n ht).exact_up_to_refinements
        (e₂ ≫ e₁ ≫ x ≫ l.f n - y₂ ≫ A.d (n - 1) n) hdiff
    have hdecomp : (e₃ ≫ e₂ ≫ e₁) ≫ x ≫ (F.step p).arrow.f n =
        (e₃ ≫ y₂ ≫ A.d (n - 1) n) ≫ (F.step a).arrow.f n +
          f ≫ (F.step b).arrow.f n := by
      have hh := congrArg (fun t => t ≫ (F.step a).arrow.f n) hf
      change (e₃ ≫ (e₂ ≫ e₁ ≫ x ≫ l.f n - y₂ ≫ A.d (n - 1) n)) ≫
        (F.step a).arrow.f n = (f ≫ i.f n) ≫ (F.step a).arrow.f n at hh
      simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, hl, hi] at hh
      simpa only [Category.assoc, add_comm] using (sub_eq_iff_eq_add.mp hh)
    let bd := (e₃ ≫ y₂ ≫ A.d (n - 1) n) ≫ (F.step a).arrow.f n
    have hbP : (F.complexStep p n).Factors bd := by
      have hb : (e₃ ≫ e₂ ≫ e₁ ≫ x - f ≫ j.f n) ≫ (F.step p).arrow.f n = bd := by
        simp only [Preadditive.sub_comp, Category.assoc, hj]
        simpa only [Category.assoc, bd] using
          (eq_sub_iff_add_eq.mpr hdecomp.symm).symm
      rw [complexStep, imageSubobject_mono]
      exact ⟨e₃ ≫ e₂ ≫ e₁ ≫ x - f ≫ j.f n, hb⟩
    have hbD : D.Factors bd := by
      apply (Subobject.inf_factors _).mpr
      refine ⟨hbP, ?_⟩
      rw [hd]
      have hh : bd = (e₃ ≫ y₂) ≫
          ((F.step a).arrow.f (n - 1) ≫ K.d (n - 1) n) := by
        dsimp only [bd]
        rw [Category.assoc, (F.step a).arrow.comm]
        simp only [Category.assoc]
        rfl
      rw [hh]
      exact imageSubobject_factors_comp_self _ _
    have hfN : (F.complexStep b n).Factors
        (f ≫ (F.step b).arrow.f n) := by
      exact imageSubobject_factors_comp_self _ _
    apply factors_desc_epi V (x ≫ (F.step p).arrow.f n) (e₃ ≫ e₂ ≫ e₁)
    rw [hdecomp]
    exact Subobject.factors_add _ _
      (Subobject.sup_factors_of_factors_left hbD)
      (Subobject.sup_factors_of_factors_right hfN)
  · intro hx
    obtain ⟨X₁, e₁, he₁, y₁, f₁, hy₁⟩ := sup_refinement D
      (F.complexStep b n) (x ≫ (F.step p).arrow.f n) hx
    have hyD : (imageSubobject ((F.step a).arrow.f (n - 1) ≫ K.d (n - 1) n)).Factors
        (y₁ ≫ D.arrow) := by
      rw [← hd]
      exact Subobject.factors_of_factors_right _ (Subobject.inf_arrow_factors_right _ _)
    obtain ⟨X₂, e₂, he₂, y₂, hy₂⟩ := image_refinement _ _ hyD
    have hfN : (Subobject.mk ((F.step b).arrow.f n)).Factors
        (f₁ ≫ (F.complexStep b n).arrow) := by
      rw [← imageSubobject_mono, ← complexStep]
      exact Subobject.factors_comp_arrow _
    obtain ⟨f, hf⟩ := hfN
    have hdecomp : (e₂ ≫ e₁) ≫ x ≫ l.f n =
        y₂ ≫ A.d (n - 1) n + (e₂ ≫ f) ≫ i.f n := by
      apply (cancel_mono ((F.step a).arrow.f n)).mp
      simp only [Preadditive.add_comp, Category.assoc, hl, hi]
      have hh := congrArg (fun t => e₂ ≫ t) hy₁
      simp only [Preadditive.comp_add] at hh
      rw [hy₂, ← hf] at hh
      change e₂ ≫ e₁ ≫ x ≫ (F.step p).arrow.f n =
        (y₂ ≫ (F.step a).arrow.f (n - 1) ≫ K.d (n - 1) n) +
          e₂ ≫ f ≫ (F.step b).arrow.f n at hh
      rw [(F.step a).arrow.comm] at hh
      simpa only [Category.assoc] using hh
    rw [← cancel_epi (e₂ ≫ e₁), comp_zero]
    have hiq : i.f n ≫ q.f n = 0 :=
      congrArg (fun f => f.f n) (cokernel.condition i)
    have hdq : A.d (n - 1) n ≫ q.f n ≫ T.pOpcycles n = 0 := by
      rw [← Category.assoc, ← q.comm, Category.assoc, T.d_pOpcycles, comp_zero]
    have hh := congrArg (fun t => t ≫ q.f n ≫ T.pOpcycles n) hdecomp
    simpa only [Preadditive.add_comp, Category.assoc, hdq, reassoc_of% hiq, comp_zero, zero_comp,
      zero_add] using hh

/-- The decalage interval class vanishes exactly on the original page denominator.
Source: Stacks Project, Tag 012K, boundary formula; Tag 015X, second filtration.
(blueprint: lem-sp-filtered-complex-decalage-representative-kernels).

Proof. The boundary criterion in a quotient of decalage steps expresses vanishing as
factorization through the sum of the differential image of the lower step and the
upper step. Substitute the degreewise decalage formula. The forward inclusion follows
from monotonicity. Conversely lift a sum decomposition and its differential-image term
along epimorphisms. The differential-image term belongs to the original filtration
step, so its primitive satisfies the decalage condition. The remaining term has the
same differential as the cycle representative, hence satisfies the upper decalage
condition. Factorization descends along the composite epimorphism. -/
theorem filteredComplexDecalageRepresentativeClass_zero_iff
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    {X : C} (x : X ⟶ (U.filtration.complexCycleRepresentatives p (p + q) r : C)) :
    x ≫ filteredComplexDecalageRepresentativeClass U p q r hr = 0 ↔
      ((U.filtration.complexStep p (p + q) ⊓
        (Subobject.«exists» (U.obj.d (p + q - 1) (p + q))).obj
          (U.filtration.complexStep (p - r + 1) (p + q - 1))) ⊔
        U.filtration.complexStep (p + 1) (p + q)).Factors
          (x ≫ (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
            (U.filtration.step p).arrow.f (p + q)) := by
  let D := U.filtration.decalage
  let a := 1 - (q + (r - 1))
  let Q := D.complexQuotient a (1 - q) (by dsimp [a]; omega)
  let k := filteredComplexDecalageRepresentative U p q r (by omega)
  have hc := interval_boundary_zero_iff D (-q) a (1 - q) (p + q)
    (by dsimp [a]; omega) (by omega) (x ≫ k)
  dsimp only at hc
  have he : x ≫ filteredComplexDecalageRepresentativeClass U p q r hr = 0 ↔
      ((x ≫ k ≫
        (Subobject.ofLE (D.step (-q)) (D.step a) (D.antitone_step (by dsimp [a]; omega))).f
          (p + q) ≫ (D.complexQuotientπ a (1 - q) (by dsimp [a]; omega)).f (p + q)) ≫
        Q.pOpcycles (p + q)) = 0 := by
    rw [← cancel_mono (Q.homologyι (p + q)), zero_comp]
    change (x ≫ (filteredComplexDecalageRepresentativeCycle U p q r hr a
      (by dsimp [a]; omega) ≫ Q.homologyπ (p + q))) ≫ Q.homologyι (p + q) = 0 ↔ _
    simp only [Category.assoc, HomologicalComplex.homology_π_ι]
    have hi := filteredComplexDecalageRepresentativeCycle_i U p q r hr a
      (by dsimp [a]; omega)
    dsimp only [Q, D]
    rw [reassoc_of% hi]
  rw [he]
  simp only [Category.assoc] at hc ⊢
  rw [hc]
  have hk := filteredComplexDecalageRepresentative_arrow U p q r (by omega)
  simp only [k, D, hk]
  apply (decalage_boundary_factors_iff U p q r hr _ ?_).symm
  have hf := (pullback_factors_iff _ _ _).mp
    (U.filtration.complexCycleRepresentatives p (p + q) r).factors_self
  have hd := (pullback_factors_iff _ _ _).mp (Subobject.factors_right_of_inf_factors hf)
  simpa only [Category.assoc] using Subobject.factors_of_factors_right x hd

/-- The representative quotient and the decalage interval class have the same kernel.
Source: Stacks Project, Tag 012K and Tag 015X.
(blueprint: lem-sp-filtered-complex-decalage-representative-kernels).

Proof. A graded cycle maps to zero in the boundary quotient exactly when its graded
image factors through B_r. Pull this condition back along the graded projection.
The boundary-pullback theorem identifies it with vanishing in the opcycles of
F^(p-r+1)/F^(p+1), equivalently factorization through the ambient boundary sum.
The decalage representative vanishing criterion gives precisely the same sum.
Test this equivalence on the two kernel-subobject inclusions. -/
theorem filteredComplexDecalageRepresentative_kernels
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    (z : (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
      (U.filtration.complexCycles p (p + q) r : C))
    (hz : z ≫ (U.filtration.complexCycles p (p + q) r).arrow =
      (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
        (U.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q)) :
    kernelSubobject (z ≫ filteredComplexPageπ U.obj U.filtration r (p, q)) =
      kernelSubobject (filteredComplexDecalageRepresentativeClass U p q r hr) := by
  let F := U.filtration
  let R := F.complexCycleRepresentatives p (p + q) r
  let Z := F.complexCycles p (p + q) r
  let B := F.complexBoundaries p (p + q) r
  let π := (F.complexQuotientπ p (p + 1) (by omega)).f (p + q)
  let T := F.complexQuotient (p - r + 1) (p + 1) (by omega)
  let j := (Subobject.ofLE (F.step p) (F.step (p - r + 1))
    (F.antitone_step (by omega))).f (p + q) ≫
    (F.complexQuotientπ (p - r + 1) (p + 1) (by omega)).f (p + q)
  have hzero {X : C} (x : X ⟶ (R : C)) :
      x ≫ (z ≫ filteredComplexPageπ U.obj F r (p, q)) = 0 ↔
        x ≫ filteredComplexDecalageRepresentativeClass U p q r hr = 0 := by
    rw [filteredComplexDecalageRepresentativeClass_zero_iff]
    rw [← Category.assoc]
    change (x ≫ z) ≫ cokernel.π
      (Subobject.ofLE B Z (filteredComplex_boundaries_le_cycles U.obj F p (p + q) r)) = 0 ↔ _
    have hquot : (x ≫ z) ≫ cokernel.π
        (Subobject.ofLE B Z (filteredComplex_boundaries_le_cycles U.obj F p (p + q) r)) = 0 ↔
        B.Factors ((x ≫ z) ≫ Z.arrow) := by
      constructor
      · intro hzero
        apply (Subobject.factors_iff _ _).mpr
        refine ⟨Abelian.monoLift
          (Subobject.ofLE B Z (filteredComplex_boundaries_le_cycles U.obj F p (p + q) r))
          (x ≫ z) hzero, ?_⟩
        change Abelian.monoLift
            (Subobject.ofLE B Z (filteredComplex_boundaries_le_cycles U.obj F p (p + q) r))
            (x ≫ z) hzero ≫ B.arrow = _
        rw [← Subobject.ofLE_arrow
          (filteredComplex_boundaries_le_cycles U.obj F p (p + q) r),
          ← Category.assoc, Abelian.monoLift_comp]
      · intro hfactor
        obtain ⟨b, hb⟩ := (Subobject.factors_iff _ _).mp hfactor
        change b ≫ B.arrow = (x ≫ z) ≫ Z.arrow at hb
        have hab : x ≫ z = b ≫ Subobject.ofLE B Z
            (filteredComplex_boundaries_le_cycles U.obj F p (p + q) r) := by
          apply (cancel_mono Z.arrow).mp
          simpa only [Category.assoc, Subobject.ofLE_arrow] using hb.symm
        rw [hab, Category.assoc, cokernel.condition, comp_zero]
    rw [hquot]
    have hz' := congrArg (fun f => x ≫ f) hz
    dsimp only [B, Z, R, π] at hz' ⊢
    have hz'' : (x ≫ z) ≫
        (U.filtration.complexCycles p (p + q) r).arrow =
        (x ≫ (U.filtration.complexCycleRepresentatives p (p + q) r).arrow) ≫
          (U.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) := by
      simpa only [Category.assoc] using hz'
    rw [hz'']
    change B.Factors ((x ≫ R.arrow) ≫ π) ↔ _
    rw [← pullback_factors_iff π B (x ≫ R.arrow)]
    have hp := F.filteredComplex_boundary_pullback p (p + q) r (by omega)
    dsimp only at hp
    rw [← hp]
    rw [pullback_factors_iff, kernelSubobject_factors_iff]
    have hc := interval_boundary_zero_iff F p (p - r + 1) (p + 1) (p + q)
      (by omega) (by omega) (x ≫ R.arrow)
    dsimp only at hc
    simpa only [Category.assoc] using hc
  apply le_antisymm
  · apply le_kernelSubobject
    exact (hzero _).mp (kernelSubobject_arrow_comp _)
  · apply le_kernelSubobject
    exact (hzero _).mpr (kernelSubobject_arrow_comp _)

/-- Normalization of a page isomorphism by its actual unquotiented cycle representatives.
Source: Stacks Project, Tag 012K, cycle/boundary quotient formulas.
(blueprint: def-sp-filtered-complex-decalage-page-data). -/
def FilteredComplexDecalagePageIsoProperty
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    (e : filteredComplexPageObject U.obj U.filtration r (p, q) ≅
      ((((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence).page
        r hr).X (p, q)) : Prop :=
  ∀ (z : (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
      (U.filtration.complexCycles p (p + q) r : C)),
    z ≫ (U.filtration.complexCycles p (p + q) r).arrow =
      (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
        (U.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) →
    z ≫ filteredComplexPageπ U.obj U.filtration r (p, q) ≫ e.hom ≫
        filteredComplexDecalagePageEmbedding U p q r hr =
      filteredComplexDecalageRepresentativeClass U p q r hr

/-- The representative equation uniquely determines a page comparison. -/
theorem filteredComplexDecalagePageIso_ext
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    (e e' : filteredComplexPageObject U.obj U.filtration r (p, q) ≅
      ((((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence).page
        r hr).X (p, q))
    (he : FilteredComplexDecalagePageIsoProperty U p q r hr e)
    (he' : FilteredComplexDecalagePageIsoProperty U p q r hr e') : e = e' := by
  obtain ⟨z, _, hzepi, _, hz, _⟩ :=
    U.filtration.filteredComplex_representative_epis p (p + q) r (by omega)
  have : Epi z := hzepi
  have : Epi (filteredComplexPageπ U.obj U.filtration r (p, q)) := by
    unfold filteredComplexPageπ
    infer_instance
  apply Iso.ext
  apply (cancel_mono (filteredComplexDecalagePageEmbedding U p q r hr)).1
  apply (cancel_epi (z ≫ filteredComplexPageπ U.obj U.filtration r (p, q))).1
  simpa only [Category.assoc] using (he z hz).trans (he' z hz).symm

end CategoryTheory
