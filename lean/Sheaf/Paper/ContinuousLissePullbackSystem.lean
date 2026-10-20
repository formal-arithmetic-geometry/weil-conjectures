/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
import Sheaf.Paper.ContinuousEtaleLocalLattices
import Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent
import Sheaf.AlgebraicGeometry.EtaleStratifiedFinite
import all Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality

/-! # Pullback systems for continuous lisse lattices

Source: Bhatt--Scholze, first paragraph of the proof of Lemma 6.8.13.
(blueprint: lem-weil-pbc-continuous-lisse-stratified-lattices)
-/

@[expose] public section


universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private abbrev LocallyFree {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) : Prop :=
  ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj R)
      (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod R).obj P)

private lemma locallyFree_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : P ≅ Q) (hP : LocallyFree R P) : LocallyFree R Q := by
  obtain ⟨C, hC⟩ := hP
  exact ⟨C, fun s ↦ ProEtale.free_of_iso (hC s)
    (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod R).mapIso e)⟩

private lemma locallyFree_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) T}
    (hP : LocallyFree T P) : LocallyFree R ((Mod.comap φ).obj P) := by
  obtain ⟨C, hC⟩ := hP
  refine ⟨C, fun s ↦ ?_⟩
  let G := ProEtale.upperStar Ab.{u + 1} (C.f s)
  exact ProEtale.free_of_iso (ProEtale.free_comap (G.map φ) (hC s))
    ((G.mapModComapIso φ).app P).symm

private lemma free_map {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : Mod.IsFree R P) : Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} g).obj R)
      (((ProEtale.upperStar Ab.{u + 1} g).mapMod R).obj P) := by
  let G := ProEtale.upperStar Ab.{u + 1} g
  obtain ⟨n, ⟨e⟩⟩ := hP
  exact ⟨n, ⟨(G.mapMod R).mapIso e ≪≫ (G.mapMod R).mapBiproduct _ ≪≫
    Limits.biproduct.mapIso (fun _ ↦ Mod.isoMk (Iso.refl _) (by simp [Mod.act]))⟩⟩

private lemma locallyFree_map {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : LocallyFree R P) : LocallyFree ((ProEtale.upperStar Ab.{u + 1} g).obj R)
      (((ProEtale.upperStar Ab.{u + 1} g).mapMod R).obj P) := by
  obtain ⟨C, hC⟩ := hP
  refine ⟨C.pullback₂ g, fun s ↦ ?_⟩
  have h := (ProEtale.free_pullback_comp_iff (Limits.pullback.fst (C.f s) g) (C.f s) P).mpr
    (free_map _ (hC s))
  rw [Limits.pullback.condition] at h
  exact (ProEtale.free_pullback_comp_iff (Limits.pullback.snd (C.f s) g) g P).mp h

private lemma locallyFree_upperStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hP : LocallyFree (condensedRingObj Λ X) P) :
    LocallyFree (condensedRingObj Λ Y) ((CondensedRing.upperStar Λ g).obj P) := by
  let φ := condensedPullbackHom Λ g
  let Q := ((ProEtale.upperStar Ab.{u + 1} g).mapMod _).obj P
  exact locallyFree_of_iso ((Mod.extendScalarsIsoComapInv φ).app Q).symm
    (locallyFree_comap (inv φ) (locallyFree_map g hP))

private lemma locallyFree_lfp {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : LocallyFree R P) : ProEtale.IsLocallyFinitelyPresented R P := by
  obtain ⟨C, hC⟩ := hP
  refine ⟨C, fun s ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hC s
  exact ⟨n, 0, 0, ⟨e ≪≫ Limits.cokernelZeroIsoTarget.symm⟩⟩

private lemma locallyFree_constructible {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (hP : LocallyFree R P) : ProEtale.IsConstructibleModuleObject R P := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  exact ⟨S, fun s ↦ locallyFree_lfp (locallyFree_map (S.immersion s) hP)⟩

private structure PullbackSystemCore
    (Λ₀ Λ₁ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    (φ : Λ₀ ⟶ Λ₁) [IsMonHom φ] where
  integral : ∀ {X Y : Scheme.{u}}, (Y ⟶ X) →
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Λ₀) X) ⥤
    Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Λ₀) Y)
  rational : ∀ {X Y : Scheme.{u}}, (Y ⟶ X) →
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Λ₁) X) ⥤
    Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Λ₁) Y)
  rationalIso : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
    rational f ≅ CondensedRing.upperStar (Λ₁) f
  scalar : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
    integral f ⋙ Mod.extendScalars (coefficientMap (φ) Y) ≅
      Mod.extendScalars (coefficientMap (φ) X) ⋙ rational f
  comp : ∀ {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X),
    rational (f ≫ g) ≅ rational g ⋙ rational f
  integralFree : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Λ₀) X)},
    LocallyFree _ M → LocallyFree _ ((integral f).obj M)
  rationalFree : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    {P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Λ₁) X)},
    LocallyFree _ P → LocallyFree _ ((rational f).obj P)

private noncomputable def canonicalPullbackSystemCore
    (Λ₀ Λ₁ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    (φ : Λ₀ ⟶ Λ₁) [IsMonHom φ] : PullbackSystemCore Λ₀ Λ₁ φ where
  integral := CondensedRing.upperStar Λ₀
  rational := CondensedRing.upperStar Λ₁
  rationalIso _ := Iso.refl _
  scalar := pullIso φ
  comp f g := upperStarComp Λ₁ f g
  integralFree := locallyFree_upperStar Λ₀
  rationalFree := locallyFree_upperStar Λ₁

private noncomputable def pullbackSystem_scalarSquareIso
    (Λ₀ Λ₁ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
    (φ : Λ₀ ⟶ Λ₁) [IsMonHom φ] (D : PullbackSystemCore Λ₀ Λ₁ φ)
    {X U V W : Scheme.{u}} (p : U ⟶ X) (j : W ⟶ X)
    (r : V ⟶ U) (q : V ⟶ W) (w : r ≫ p = q ≫ j)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₁ X))
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ₀ U))
    (P' : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ₁ W))
    (M' : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ₀ V))
    (iP : P' ≅ (D.rational j).obj P) (iM : M' ≅ (D.integral r).obj M)
    (e : (Mod.extendScalars (coefficientMap φ U)).obj M ≅
      (CondensedRing.upperStar Λ₁ p).obj P) :
    (Mod.extendScalars (coefficientMap φ V)).obj M' ≅ (D.rational q).obj P' :=
  (Mod.extendScalars (coefficientMap φ V)).mapIso iM ≪≫
    (D.scalar r).app M ≪≫
    (D.rational r).mapIso (e ≪≫ (D.rationalIso p).symm.app P) ≪≫
    (D.comp r p).symm.app P ≪≫
    eqToIso (congrArg (fun f ↦ (D.rational f).obj P) w) ≪≫
    (D.comp q j).app P ≪≫ (D.rational q).mapIso iP.symm

private abbrev PullbackSystem
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] :=
  PullbackSystemCore (integralCoeff ℓ E) (Profinite.continuousMapRingObj E)
    (integralScalarMap ℓ E)

private noncomputable def canonicalPullbackSystem
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] :
    PullbackSystem.{u} ℓ E :=
  canonicalPullbackSystemCore _ _ (integralScalarMap ℓ E)

end AlgebraicGeometry.ProEtale.CondensedRing
