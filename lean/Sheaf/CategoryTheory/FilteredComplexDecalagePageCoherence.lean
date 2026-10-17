/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.CategoryTheory.FilteredComplexDecalagePageIso
import Sheaf.CategoryTheory.FilteredComplexDecalageIntervalMaps
import all Sheaf.CategoryTheory.FilteredComplexDecalagePageData

/-! # Differential and successor compatibility of the normalized decalage pages

Source: Stacks Project, Tags 012K and 015X.
(blueprint: lem-sp-filtered-complex-decalage-page-coherence).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem representative_derivative_cycle
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r) :
    ∃ y : (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
        (U.filtration.decalage.step (1 - q) : CochainComplex C ℤ).cycles (p + q + 1),
      y ≫ (U.filtration.decalage.step (1 - q) : CochainComplex C ℤ).iCycles (p + q + 1) ≫
          (U.filtration.decalage.step (1 - q)).arrow.f (p + q + 1) =
        (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
          (U.filtration.step p).arrow.f (p + q) ≫ U.obj.d (p + q) (p + q + 1) := by
  let S : CochainComplex C ℤ := U.filtration.decalage.step (1 - q)
  have hd := representative_d_factors_decalage U p q r hr
  rw [DecreasingFiltration.complexStep, imageSubobject_mono,
    Subobject.mk_factors_iff] at hd
  obtain ⟨x, hx⟩ : ∃ x :
      (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶ S.X (p + q + 1),
      x ≫ (U.filtration.decalage.step (1 - q)).arrow.f (p + q + 1) =
        (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
          (U.filtration.step p).arrow.f (p + q) ≫ U.obj.d (p + q) (p + q + 1) := hd
  have hz : x ≫ S.d (p + q + 1) (p + q + 1 + 1) = 0 := by
    apply (cancel_mono ((U.filtration.decalage.step (1 - q)).arrow.f
      (p + q + 1 + 1))).1
    rw [zero_comp, Category.assoc,
      ← (U.filtration.decalage.step (1 - q)).arrow.comm,
      ← Category.assoc, hx]
    simp only [Category.assoc, U.obj.d_comp_d, comp_zero]
  refine ⟨HomologicalComplex.liftCycles S x (p + q + 1 + 1) (by simp) hz, ?_⟩
  change HomologicalComplex.liftCycles S x (p + q + 1 + 1) (by simp) hz ≫
    S.iCycles (p + q + 1) ≫ _ = _
  rw [← Category.assoc, HomologicalComplex.liftCycles_i]
  exact hx

private theorem interval_connecting
    (U : FilteredObject (CochainComplex C ℤ))
    (a b c : EInt) (hab : a ≤ b) (hbc : b ≤ c) (n m : ℤ) (hn : n + 1 = m) :
    ((filteredComplexDecalageSpectralObjectFunctor C).obj U).δ
        (homOfLE hab) (homOfLE hbc) n m hn ≫
        (filteredComplexDecalageIntervalIso U a b hab m).hom =
      (filteredComplexDecalageIntervalIso U b c hbc n).hom ≫
        (U.filtration.decalageTowerInterval_shortExact b c hbc).δ n m hn ≫
        HomologicalComplex.homologyMap
          (U.filtration.decalageTowerInterval a b hab).g m := by
  let F := U.filtration.decalageTower
  let f := F.map (homOfLE hab)
  let g := F.map (homOfLE hbc)
  let S := U.filtration.decalageTowerInterval b c hbc
  let hS := U.filtration.decalageTowerInterval_shortExact b c hbc
  let H := HomologicalComplex.homologyFunctor C (.up ℤ) 0
  let en := HomotopyCategory.homologyFunctorFactors C (.up ℤ) n
  let em := HomotopyCategory.homologyFunctorFactors C (.up ℤ) m
  have hc := CochainComplex.mappingCone.homologySequenceδ_triangleh hS n m hn
  rw [CochainComplex.homologySequenceδ_quotient_mapTriangle_obj] at hc
  have hc' : H.shiftMap (CochainComplex.mappingCone.triangle g).mor₃ n m (by omega) =
      HomologicalComplex.homologyMap (CochainComplex.mappingCone.descShortComplex S) n ≫
        hS.δ n m hn := by
    apply (cancel_epi (en.hom.app _)).1
    apply (cancel_mono (em.inv.app _)).1
    dsimp only [CochainComplex.mappingCone.triangleh, CochainComplex.mappingCone.triangle,
      Pretriangulated.Triangle.mk] at hc ⊢
    simpa only [en, em, H, S, g, F, DecreasingFiltration.decalageTowerInterval,
      Category.assoc] using hc
  have hδ : ((filteredComplexDecalageSpectralObjectFunctor C).obj U).δ
      (homOfLE hab) (homOfLE hbc) n m hn =
      (HomotopyCategory.homologyFunctor C (.up ℤ) 0).homologySequenceδ
        ((HomotopyCategory.quotient C (.up ℤ)).mapTriangle.obj
          (CochainComplex.mappingConeCompTriangle f g)) n m hn := by
    change (HomotopyCategory.homologyFunctor C (.up ℤ) 0).shiftMap _ n m _ =
      (HomotopyCategory.homologyFunctor C (.up ℤ) 0).shiftMap _ n m _
    congr 1
    dsimp [filteredComplexDecalageSpectralObjectFunctor,
      Triangulated.SpectralObject.precomp, Triangulated.SpectralObject.precompFunctor,
      Triangulated.SpectralObject.ω₂, Triangulated.SpectralObject.δ,
      HomotopyCategory.spectralObjectMappingCone]
    simp only [CochainComplex.mappingCone.map_id, Functor.map_id, Category.id_comp,
      Category.comp_id]
    rfl
  rw [hδ, CochainComplex.homologySequenceδ_quotient_mapTriangle_obj]
  change (en.hom.app _ ≫ H.shiftMap
      (CochainComplex.mappingConeCompTriangle f g).mor₃ n m (by omega) ≫ em.inv.app _) ≫
      (em.hom.app _ ≫ HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.descShortComplex
          (U.filtration.decalageTowerInterval a b hab)) m) = _
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [CochainComplex.mappingConeCompTriangle_mor₃, Functor.shiftMap_comp]
  erw [reassoc_of% hc']
  simp only [Category.assoc]
  change en.hom.app _ ≫ HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.descShortComplex S) n ≫ hS.δ n m hn ≫
      HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) m ≫
      HomologicalComplex.homologyMap (CochainComplex.mappingCone.descShortComplex
        (U.filtration.decalageTowerInterval a b hab)) m = _
  rw [← HomologicalComplex.homologyMap_comp]
  have hdesc : CochainComplex.mappingCone.inr f ≫
      CochainComplex.mappingCone.descShortComplex
        (U.filtration.decalageTowerInterval a b hab) =
      (U.filtration.decalageTowerInterval a b hab).g :=
    CochainComplex.mappingCone.inr_descShortComplex
      (U.filtration.decalageTowerInterval a b hab)
  rw [hdesc]
  change en.hom.app _ ≫ HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.descShortComplex S) n ≫ hS.δ n m hn ≫
      HomologicalComplex.homologyMap (U.filtration.decalageTowerInterval a b hab).g m =
    (en.hom.app _ ≫ HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.descShortComplex S) n) ≫ hS.δ n m hn ≫
      HomologicalComplex.homologyMap (U.filtration.decalageTowerInterval a b hab).g m
  simp only [Category.assoc]

private theorem quotient_connecting_representative
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (n m : ℤ) (hn : (ComplexShape.up ℤ).Rel n m)
    {A : C} (z : A ⟶ S.X₃.cycles n) (x : A ⟶ S.X₂.X n)
    (y : A ⟶ S.X₁.cycles m)
    (hx : x ≫ S.g.f n = z ≫ S.X₃.iCycles n)
    (hy : y ≫ S.X₁.iCycles m ≫ S.f.f m = x ≫ S.X₂.d n m) :
    z ≫ S.X₃.homologyπ n ≫ hS.δ n m hn = y ≫ S.X₁.homologyπ m := by
  rw [← Category.assoc]
  apply hS.δ_eq' n m hn (z ≫ S.X₃.homologyπ n) (x ≫ S.X₂.pOpcycles n) y
  · simp only [Category.assoc, HomologicalComplex.p_opcyclesMap,
      HomologicalComplex.homology_π_ι]
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ S.X₃.pOpcycles n) hx
  · apply (cancel_mono (S.X₂.iCycles m)).1
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.opcyclesToCycles_iCycles,
      HomologicalComplex.p_fromOpcycles]
    exact hy

private theorem interval_connecting_representative
    (U : FilteredObject (CochainComplex C ℤ))
    (a b c : EInt) (hab : a ≤ b) (hbc : b ≤ c) (n m : ℤ) (hn : n + 1 = m)
    {A : C}
    (z : A ⟶ (U.filtration.decalageTowerInterval b c hbc).X₃.cycles n)
    (x : A ⟶ (U.filtration.decalageTower.obj c).X n)
    (y : A ⟶ (U.filtration.decalageTower.obj b).cycles m)
    (hx : x ≫ (U.filtration.decalageTowerInterval b c hbc).g.f n =
      z ≫ (U.filtration.decalageTowerInterval b c hbc).X₃.iCycles n)
    (hy : y ≫ (U.filtration.decalageTower.obj b).iCycles m ≫
        (U.filtration.decalageTower.map (homOfLE hbc)).f m =
      x ≫ (U.filtration.decalageTower.obj c).d n m) :
    z ≫ (U.filtration.decalageTowerInterval b c hbc).X₃.homologyπ n ≫
        (filteredComplexDecalageIntervalIso U b c hbc n).inv ≫
        ((filteredComplexDecalageSpectralObjectFunctor C).obj U).δ
          (homOfLE hab) (homOfLE hbc) n m hn ≫
        (filteredComplexDecalageIntervalIso U a b hab m).hom =
      y ≫ (U.filtration.decalageTower.obj b).homologyπ m ≫
        HomologicalComplex.homologyMap (U.filtration.decalageTowerInterval a b hab).g m := by
  let S := U.filtration.decalageTowerInterval b c hbc
  let hS := U.filtration.decalageTowerInterval_shortExact b c hbc
  have hz := quotient_connecting_representative hS n m hn z x y hx hy
  rw [interval_connecting U a b c hab hbc n m hn]
  simp only [Iso.inv_hom_id_assoc]
  rw [reassoc_of% hz]
  rfl

private theorem representative_connecting
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    (a : EInt) (ha : a ≤ (q : EInt)) :
    ∃ y : (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
        (U.filtration.decalageTower.obj (q : EInt)).cycles (p + q + 1),
      y ≫ (U.filtration.decalage.step (1 - q) : CochainComplex C ℤ).iCycles (p + q + 1) ≫
          (U.filtration.decalage.step (1 - q)).arrow.f (p + q + 1) =
        (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
          (U.filtration.step p).arrow.f (p + q) ≫ U.obj.d (p + q) (p + q + 1) ∧
      filteredComplexDecalageRepresentativeClass U p q r hr ≫
          (filteredComplexDecalageIntervalIso U (q : EInt)
            ((q + (r - 1) : ℤ) : EInt) (by simp; omega) (p + q)).inv ≫
          ((filteredComplexDecalageSpectralObjectFunctor C).obj U).δ
            (homOfLE ha) (homOfLE (by simp; omega)) (p + q) (p + q + 1) rfl ≫
          (filteredComplexDecalageIntervalIso U a (q : EInt) ha (p + q + 1)).hom =
        y ≫ (U.filtration.decalageTower.obj (q : EInt)).homologyπ (p + q + 1) ≫
          HomologicalComplex.homologyMap
            (U.filtration.decalageTowerInterval a (q : EInt) ha).g (p + q + 1) := by
  obtain ⟨y, hy⟩ := representative_derivative_cycle U p q r hr
  let D := U.filtration.decalage
  let b := q + (r - 1)
  let k := filteredComplexDecalageRepresentative U p q r (by omega)
  let l := Subobject.ofLE (D.step (-q)) (D.step (1 - b))
    (D.antitone_step (by dsimp [b]; omega))
  let x := k ≫ l.f (p + q)
  let z := filteredComplexDecalageRepresentativeCycle U p q r hr (1 - b)
    (by dsimp [b]; omega)
  refine ⟨y, hy, ?_⟩
  simp only [filteredComplexDecalageRepresentativeClass, Category.assoc]
  apply interval_connecting_representative U a (q : EInt) (b : EInt) ha
    (by simp; dsimp [b]; omega) (p + q) (p + q + 1) rfl z x y
  · change (k ≫ l.f (p + q)) ≫
        (D.complexQuotientπ (1 - b) (1 - q) (by dsimp [b]; omega)).f (p + q) =
      z ≫ (D.complexQuotient (1 - b) (1 - q) (by dsimp [b]; omega)).iCycles (p + q)
    simpa only [k, l, z, D, Category.assoc] using
      (filteredComplexDecalageRepresentativeCycle_i U p q r hr (1 - b)
        (by dsimp [b]; omega)).symm
  · apply (cancel_mono ((D.step (1 - b)).arrow.f (p + q + 1))).1
    have ht : U.filtration.decalageTower.map
        (homOfLE (by simp; dsimp [b]; omega) : (q : EInt) ⟶ (b : EInt)) ≫
        (D.step (1 - b)).arrow = (D.step (1 - q)).arrow :=
      Subobject.ofLE_arrow _
    have ht' := congrArg (fun f ↦ f.f (p + q + 1)) ht
    simp only [HomologicalComplex.comp_f] at ht'
    rw [Category.assoc, Category.assoc, ht']
    change y ≫ (D.step (1 - q) : CochainComplex C ℤ).iCycles (p + q + 1) ≫
        (D.step (1 - q)).arrow.f (p + q + 1) =
      (x ≫ (D.step (1 - b) : CochainComplex C ℤ).d (p + q) (p + q + 1)) ≫
        (D.step (1 - b)).arrow.f (p + q + 1)
    rw [hy]
    change _ = ((k ≫ l.f (p + q)) ≫
      (D.step (1 - b) : CochainComplex C ℤ).d (p + q) (p + q + 1)) ≫
        (D.step (1 - b)).arrow.f (p + q + 1)
    simp only [Category.assoc]
    rw [← (D.step (1 - b)).arrow.comm]
    simp only [← Category.assoc, ← HomologicalComplex.comp_f, l, Subobject.ofLE_arrow]
    simpa only [Category.assoc, k] using
      (congrArg (fun f ↦ f ≫ U.obj.d (p + q) (p + q + 1))
        (filteredComplexDecalageRepresentative_arrow U p q r (by omega))).symm

private theorem representative_class_transition
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    (ρ : (U.filtration.complexCycleRepresentatives p (p + q) (r + 1) : C) ⟶
      (U.filtration.complexCycleRepresentatives p (p + q) r : C))
    (hρ : ρ ≫ (U.filtration.complexCycleRepresentatives p (p + q) r).arrow =
      (U.filtration.complexCycleRepresentatives p (p + q) (r + 1)).arrow) :
    let α := ComposableArrows.homMk₁
      (F := ComposableArrows.mk₁
        (homOfLE (by simp; omega : (q : EInt) ≤ ((q + (r - 1) : ℤ) : EInt))))
      (G := ComposableArrows.mk₁
        (homOfLE (by simp; omega : (q : EInt) ≤ ((q + ((r + 1) - 1) : ℤ) : EInt))))
      (𝟙 (q : EInt))
      (homOfLE (by simp : ((q + (r - 1) : ℤ) : EInt) ≤
        ((q + ((r + 1) - 1) : ℤ) : EInt))) (Subsingleton.elim _ _)
    ρ ≫ filteredComplexDecalageRepresentativeClass U p q r hr ≫
        HomologicalComplex.homologyMap
          (filteredComplexDecalageIntervalHom U (by simp; omega) (by simp; omega) α).τ₃
          (p + q) =
      filteredComplexDecalageRepresentativeClass U p q (r + 1) (by omega) := by
  dsimp only
  let D := U.filtration.decalage
  let a := 1 - (q + (r - 1))
  let a' := 1 - (q + ((r + 1) - 1))
  have hbound : a' ≤ 1 - q := by dsimp [a']; omega
  let Q := D.complexQuotient a (1 - q) (by dsimp [a]; omega)
  let Q' := D.complexQuotient a' (1 - q) (by dsimp [a']; omega)
  let α := ComposableArrows.homMk₁
    (F := ComposableArrows.mk₁
      (homOfLE (by simp; omega : (q : EInt) ≤ ((q + (r - 1) : ℤ) : EInt))))
    (G := ComposableArrows.mk₁
      (homOfLE (by simp; omega : (q : EInt) ≤ ((q + ((r + 1) - 1) : ℤ) : EInt))))
    (𝟙 (q : EInt))
    (homOfLE (by simp : ((q + (r - 1) : ℤ) : EInt) ≤
      ((q + ((r + 1) - 1) : ℤ) : EInt))) (Subsingleton.elim _ _)
  let T := filteredComplexDecalageIntervalHom U (by simp; omega) (by simp; omega) α
  let f : Q ⟶ Q' := T.τ₃
  let k := filteredComplexDecalageRepresentative U p q r (by omega)
  let k' := filteredComplexDecalageRepresentative U p q (r + 1) (by omega)
  let l := Subobject.ofLE (D.step (-q)) (D.step a) (D.antitone_step (by dsimp [a]; omega))
  let l' := Subobject.ofLE (D.step (-q)) (D.step a')
    (D.antitone_step (by dsimp [a']; omega))
  have hk : (ρ ≫ k ≫ l.f (p + q)) ≫ T.τ₂.f (p + q) = k' ≫ l'.f (p + q) := by
    apply (cancel_mono ((D.step a').arrow.f (p + q))).1
    have hτ : T.τ₂ ≫ (D.step a').arrow = (D.step a).arrow :=
      Subobject.ofLE_arrow _
    simp only [Category.assoc, ← HomologicalComplex.comp_f, hτ, l, l',
      Subobject.ofLE_arrow]
    rw [filteredComplexDecalageRepresentative_arrow,
      filteredComplexDecalageRepresentative_arrow]
    rw [← Category.assoc, hρ]
  have hf := congrArg (fun f ↦ f.f (p + q)) T.comm₂₃
  simp only [HomologicalComplex.comp_f] at hf
  let z := filteredComplexDecalageRepresentativeCycle U p q r hr a
    (by dsimp [a]; omega)
  let z' := filteredComplexDecalageRepresentativeCycle U p q (r + 1) (by omega) a'
    (by dsimp [a']; omega)
  have hz_i : z ≫ Q.iCycles (p + q) = k ≫ l.f (p + q) ≫
      (D.complexQuotientπ a (1 - q) (by dsimp [a]; omega)).f (p + q) :=
    filteredComplexDecalageRepresentativeCycle_i U p q r hr a (by dsimp [a]; omega)
  have hz'_i : z' ≫ Q'.iCycles (p + q) = k' ≫ l'.f (p + q) ≫
      (D.complexQuotientπ a' (1 - q) hbound).f (p + q) :=
    filteredComplexDecalageRepresentativeCycle_i U p q (r + 1) (by omega) a'
      (by dsimp [a']; omega)
  have hf' : (D.complexQuotientπ a (1 - q) (by dsimp [a]; omega)).f (p + q) ≫
      f.f (p + q) = T.τ₂.f (p + q) ≫
      (D.complexQuotientπ a' (1 - q) hbound).f (p + q) := hf.symm
  have hz : (ρ ≫ z) ≫ HomologicalComplex.cyclesMap f (p + q) = z' := by
    apply (cancel_mono (Q'.iCycles (p + q))).1
    calc
      _ = ρ ≫ (z ≫ Q.iCycles (p + q)) ≫ f.f (p + q) := by
        simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
      _ = ρ ≫ (k ≫ l.f (p + q) ≫
          (D.complexQuotientπ a (1 - q) (by dsimp [a]; omega)).f (p + q)) ≫
          f.f (p + q) := by rw [hz_i]
      _ = ((ρ ≫ k ≫ l.f (p + q)) ≫ T.τ₂.f (p + q)) ≫
          (D.complexQuotientπ a' (1 - q) hbound).f (p + q) := by
        simp only [Category.assoc]
        rw [hf']
      _ = (k' ≫ l'.f (p + q)) ≫
          (D.complexQuotientπ a' (1 - q) hbound).f (p + q) := by rw [hk]
      _ = z' ≫ Q'.iCycles (p + q) := by
        simpa only [Category.assoc] using hz'_i.symm
  have hclass : ρ ≫ (z ≫ Q.homologyπ (p + q)) ≫
      HomologicalComplex.homologyMap f (p + q) = z' ≫ Q'.homologyπ (p + q) := by
    simp only [Category.assoc, HomologicalComplex.homologyπ_naturality]
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ Q'.homologyπ (p + q)) hz
  exact hclass

/-- The two compatibility equations for the already fixed, normalized page isomorphisms. -/
structure FilteredComplexDecalagePageCoherence
    (U : FilteredObject (CochainComplex C ℤ)) : Prop where
  differential : ∀ (r : ℤ) (hr : 2 ≤ r) (i j : ℤ × ℤ),
    (filteredComplexDecalagePageIso U i.1 i.2 r hr).hom ≫
        ((((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence).page
          r hr).d i j =
      (((filteredComplexCanonicalModel C).S.obj U).page r hr).d i j ≫
        (filteredComplexDecalagePageIso U j.1 j.2 r hr).hom
  successor : ∀ (r : ℤ) (hr : 2 ≤ r)
    (f : ((filteredComplexCanonicalModel C).S.obj U).page r hr ⟶
      (((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence).page r hr),
    (∀ pq : ℤ × ℤ, f.f pq = (filteredComplexDecalagePageIso U pq.1 pq.2 r hr).hom) →
    ∀ pq : ℤ × ℤ,
      HomologicalComplex.homologyMap f pq ≫
          ((((filteredComplexDecalageSpectralObjectFunctor C).obj U).E₂SpectralSequence).iso
            r (r + 1) pq rfl hr).hom =
        (((filteredComplexCanonicalModel C).S.obj U).iso r (r + 1) pq rfl hr).hom ≫
          (filteredComplexDecalagePageIso U pq.1 pq.2 (r + 1) (by omega)).hom

/-- The normalized individual page comparisons preserve the differential and successor map.
Source: Stacks Project, Tag 012K, the differential and successor quotient construction;
Tag 015X, Remark 13.26.15, second filtration.
(blueprint: lem-sp-filtered-complex-decalage-page-coherence).

Proof. Put n=p+q and D=Dec(F). The spectral page has indices
(q-r+2,q,q+1,q+r-1); its monic interval embedding has target
H^n(D^(2-q-r)/D^(1-q)). For a related target (p+r,q+1-r), the relevant
connecting map is between the intervals (q,q+r-1) and (q+1-r,q).
Precompose the desired equation with the epic unquotiented representative
projection to the original page and postcompose with the target embedding.
Use spectralSequence_page_d_eq and d_ιE_fromOpcycles to express the composite
as the connecting map on these intervals. The proved interval_connecting
helper identifies it with the connecting map of
D^(1-q) -> D^(2-q-r) -> D^(2-q-r)/D^(1-q), followed by projection to the
target interval. The proved interval_connecting_representative calculates
this map: lift the source quotient cycle, differentiate it in D^(2-q-r),
and lift the result to cycles of D^(1-q). Its class followed by the target
projection is the image under the connecting map, with positive sign.
The proved representative_derivative_cycle constructs the cycle lift of the
ambient derivative in D^(1-q), and representative_connecting applies the
connecting-map equation to the original r-cycle representative itself. Thus
the target cycle is the ambient derivative, exactly as in the original page
differential's representative equation. The two normalized page equations identify the composites;
cancel the epi and mono. At r=2 the same calculation uses
spectralSequence_first_page_d_eq. At unrelated bidegrees both differentials
vanish by their shape conditions.

For the successor square fix (p,q) and put i0=q-r+2, i1=q, i2=q+1,
i3=q+r-1, i0'=i0-1 and i3'=i3+1. The epic cover of canonical cycles by
successor representatives exists by the successor-cycles-cover theorem.
The original successor homology isomorphism is characterized by sending
such a representative to its next-page quotient class. On the spectral
side use spectralSequenceHomologyData and spectralSequence_iso. Its kernel
map is mapFourδ₁Toδ₀' for i0'<=i0; its cokernel map is
mapFourδ₄Toδ₃' for i3<=i3'. The factorization identity HomologyData.fac
says that their composite is the epic-then-monic factorization through
E(i0',i1,i2,i3'). Each endpoint map takes the class of a fixed ambient
representative to its class in the new interval: cancel the cycle inclusion
and apply the quotient square. The right-endpoint instance of precisely
this calculation is the proved representative_class_transition helper.
Consequently the homology isomorphism specified by this factorization
sends a successor representative to its own class embedded in the right
interval (q,q+r). Apply the normalized page equations on r and r+1,
then cancel the epic successor-cycle cover followed by homologyπ and the
monic next-page interval embedding. Naturality of homologyπ shows that
this proves the equation for any chain map with the specified components.
No convergence, finite filtration or first-quadrant condition is used. -/
theorem filteredComplex_decalage_page_coherence
    (U : FilteredObject (CochainComplex C ℤ)) :
    FilteredComplexDecalagePageCoherence U := by
  sorry

end CategoryTheory
