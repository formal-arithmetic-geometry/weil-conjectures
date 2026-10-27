/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H9
-/
module

public import Sheaf.Paper.SmoothPurityTowerShriekData
public import Mathlib.Algebra.Homology.ExactSequence
import Sheaf.Paper.SmoothPurityTowerOrdinaryUnitEvaluation
import WeilConjectures.SixFunctors.ProEtale.OpenClosed.Sequence
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-! # Ordinary localization in the fixed constant coefficient coordinates

Source: Stacks 09AH and 09BM; blueprint operations proof (2c)
(blueprint: lem-sp-tower-ordinary-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section Transport

variable {C C' U U' Z Z' : Type*}
  [Category* C] [Category* C'] [Category* U] [Category* U']
  [Category* Z] [Category* Z']

private theorem transport_sequence [Abelian C]
    {A B D A' B' D' : C} (f : A ⟶ B) (g : B ⟶ D)
    (f' : A' ⟶ B') (g' : B' ⟶ D')
    (e₁ : A ≅ A') (e₂ : B ≅ B') (e₃ : D ≅ D')
    (hf : f ≫ e₂.hom = e₁.hom ≫ f') (hg : g ≫ e₃.hom = e₂.hom ≫ g')
    (hs : Mono f' ∧ Epi g' ∧ (ComposableArrows.mk₂ f' g').Exact) :
    Mono f ∧ Epi g ∧ (ComposableArrows.mk₂ f g).Exact := by
  have hz : f ≫ g = 0 := by
    apply (cancel_mono e₃.hom).1
    rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]
    have hz' : f' ≫ g' = 0 := hs.2.2.toIsComplex.zero 0 (by decide)
    rw [hz', comp_zero, zero_comp]
  let S := ShortComplex.mk f g hz
  let S' := ShortComplex.mk f' g' (hs.2.2.toIsComplex.zero 0 (by decide))
  have hS' : S'.ShortExact := { exact := hs.2.2.exact 0, mono_f := hs.1, epi_g := hs.2.1 }
  have hS : S.ShortExact := (ShortComplex.shortExact_iff_of_iso
    (ShortComplex.isoMk e₁ e₂ e₃ hf.symm hg.symm)).2 hS'
  exact ⟨hS.mono_f, hS.epi_g, hS.exact.exact_toComposableArrows⟩

private def counit_comparison {L : U ⥤ C} {R : C ⥤ U}
    {L' : U ⥤ C} {R' : C ⥤ U} (a : L ⊣ R) (a' : L' ⊣ R') (e : R ≅ R') :
    R ⋙ L ≅ R' ⋙ L' :=
  Functor.isoWhiskerRight e L ≪≫
    Functor.isoWhiskerLeft R' ((a.ofNatIsoRight e).leftAdjointUniq a')

private theorem counit_comparison_eq {L : U ⥤ C} {R : C ⥤ U}
    {L' : U ⥤ C} {R' : C ⥤ U} (a : L ⊣ R) (a' : L' ⊣ R') (e : R ≅ R')
    (M : C) : (counit_comparison a a' e).hom.app M ≫ a'.counit.app M =
      a.counit.app M := by
  change (L.map (e.hom.app M) ≫
    ((a.ofNatIsoRight e).leftAdjointUniq a').hom.app (R'.obj M)) ≫
      a'.counit.app M = a.counit.app M
  rw [Category.assoc, Adjunction.leftAdjointUniq_hom_app_counit]
  simp [Adjunction.ofNatIsoRight_counit, ← L.map_comp, ← Category.assoc]

private def unit_comparison {L : C ⥤ Z} {R : Z ⥤ C}
    {L' : C ⥤ Z} {R' : Z ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R') (e : R ≅ R') :
    L ⋙ R ≅ L' ⋙ R' :=
  Functor.isoWhiskerLeft L e ≪≫
    Functor.isoWhiskerRight ((a.ofNatIsoRight e).leftAdjointUniq a') R'

private theorem unit_comparison_eq {L : C ⥤ Z} {R : Z ⥤ C}
    {L' : C ⥤ Z} {R' : Z ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R') (e : R ≅ R')
    (M : C) : a.unit.app M ≫ (unit_comparison a a' e).hom.app M =
      a'.unit.app M := by
  dsimp only [unit_comparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← Category.assoc]
  exact (a.ofNatIsoRight e).unit_leftAdjointUniq_hom_app a' M

private theorem conjugate_sequence [Abelian C] [Abelian C']
    (e : C ≌ C') (eU : U ≌ U') (eZ : Z ≌ Z')
    [e.functor.Additive]
    {L : U ⥤ C} {R : C ⥤ U} (a : L ⊣ R)
    {P : C ⥤ Z} {Q : Z ⥤ C} (b : P ⊣ Q)
    (hs : ∀ M : C, Mono (a.counit.app M) ∧ Epi (b.unit.app M) ∧
      (ComposableArrows.mk₂ (a.counit.app M) (b.unit.app M)).Exact)
    (M : C') :
    let a' := (eU.symm.toAdjunction.comp a).comp e.toAdjunction
    let b' := (e.symm.toAdjunction.comp b).comp eZ.toAdjunction
    Mono (a'.counit.app M) ∧ Epi (b'.unit.app M) ∧
      (ComposableArrows.mk₂ (a'.counit.app M) (b'.unit.app M)).Exact := by
  dsimp only
  let N := e.inverse.obj M
  let f := e.functor.map (a.counit.app N)
  let g := e.functor.map (b.unit.app N)
  let S := ShortComplex.mk (a.counit.app N) (b.unit.app N)
    ((hs N).2.2.toIsComplex.zero 0 (by decide))
  have hS : S.ShortExact := { exact := (hs N).2.2.exact 0, mono_f := (hs N).1, epi_g := (hs N).2.1 }
  have hS' := hS.map_of_exact e.functor
  have hs' : Mono f ∧ Epi g ∧ (ComposableArrows.mk₂ f g).Exact :=
    ⟨hS'.mono_f, hS'.epi_g, hS'.exact.exact_toComposableArrows⟩
  let e₁ := e.functor.mapIso (L.mapIso (eU.unitIso.symm.app (R.obj N)))
  let e₂ := e.counitIso.symm.app M
  let e₃ := e.functor.mapIso (Q.mapIso (eZ.unitIso.symm.app (P.obj N)))
  apply transport_sequence _ _ f g e₁ e₂ e₃ _ _ hs'
  · simp [Adjunction.comp_counit_app, N, e₁, e₂, f, ← Functor.map_comp,
      Category.assoc]
  · simp only [Adjunction.comp_unit_app]
    change ((e.counitIso.inv.app M ≫ e.functor.map (b.unit.app N)) ≫
      e.functor.map (Q.map (eZ.unitIso.hom.app (P.obj N)))) ≫
        e.functor.map (Q.map (eZ.unitIso.inv.app (P.obj N))) =
      e.counitIso.inv.app M ≫ e.functor.map (b.unit.app N)
    rw [Category.assoc, Category.assoc, ← e.functor.map_comp, ← Q.map_comp,
      eZ.unitIso.hom_inv_id_app]
    rw [Q.map_id ((𝟭 Z).obj (P.obj N)),
      e.functor.map_id (Q.obj ((𝟭 Z).obj (P.obj N)))]
    exact congrArg (fun k ↦ e.counitIso.inv.app M ≫ k)
      (Category.comp_id (e.functor.map (b.unit.app N)))

end Transport

attribute [local irreducible] sfIntrinsicModuleEquivalence

private theorem finite_localization (b : Base l E)
    {Z U T : Scheme.{u}} (i : Z ⟶ T) (a : U ⟶ T)
    [IsClosedImmersion i] [IsOpenImmersion a] [QuasiCompact a]
    (complement : Set.range a = (Set.range i)ᶜ) (n : ℕ) :
    PreservesFiniteColimits (proEtaleConstantRingPushforward (R l E n) i) ∧
      ∀ M : proEtaleRingModules T (proEtaleConstantRing T (R l E n)),
        Mono ((finiteOpenAdjunction l E b a n).counit.app M) ∧
        Epi ((proEtaleConstantRingAdjunction (R l E n) i).unit.app M) ∧
        (ComposableArrows.mk₂ ((finiteOpenAdjunction l E b a n).counit.app M)
          ((proEtaleConstantRingAdjunction (R l E n) i).unit.app M)).Exact := by
  let : Finite (R l E n) := b.finite n
  let A := R l E n
  let eT := sfIntrinsicModuleEquivalence T A
  let eU := sfIntrinsicModuleEquivalence U A
  let eZ := sfIntrinsicModuleEquivalence Z A
  let aj := AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) a
  let ai := AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) i
  let aj' := (eU.symm.toAdjunction.comp aj).comp eT.toAdjunction
  let ai' := (eT.symm.toAdjunction.comp ai).comp eZ.toAdjunction
  have hic : IsCompl (Set.range i.base) (Set.range a.base) := by
    rw [complement]
    exact isCompl_compl
  let q := (ai'.ofNatIsoLeft (openSquarePullbackModel A i).symm).rightAdjointUniq
    (proEtaleConstantRingAdjunction A i)
  have hcol := AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isCompl
    (R := ULift.{u + 1} A) i a hic
  have : PreservesFiniteColimits
      (eZ.inverse ⋙ AlgebraicGeometry.ProEtale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) i ⋙ eT.functor) := by
    have := hcol
    infer_instance
  refine ⟨preservesFiniteColimits_of_natIso q, ?_⟩
  intro M
  have hs (N) := AlgebraicGeometry.ProEtale.shortExact_openClosedShortComplex
    (R := ULift.{u + 1} A) i a hic N
  have ht := conjugate_sequence eT eU eZ aj ai
    (fun N ↦ ⟨(hs N).mono_f, (hs N).epi_g,
      (hs N).exact.exact_toComposableArrows⟩) M
  let ej := counit_comparison aj' (finiteOpenAdjunction l E b a n)
    (openSquarePullbackModel A a).symm
  let ei := unit_comparison ai' (proEtaleConstantRingAdjunction A i) q
  apply transport_sequence _ _ (aj'.counit.app M) (ai'.unit.app M)
    (ej.symm.app M) (Iso.refl M) (ei.symm.app M) _ _ ht
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [← counit_comparison_eq aj' (finiteOpenAdjunction l E b a n)
      (openSquarePullbackModel A a).symm M]
    exact (ej.inv_hom_id_app_assoc M _).symm
  · simp only [Iso.refl_hom, Category.id_comp]
    rw [← unit_comparison_eq ai' (proEtaleConstantRingAdjunction A i) q M]
    simp only [Category.assoc]
    rw [show (unit_comparison ai' (proEtaleConstantRingAdjunction A i) q).hom.app M ≫
      (ei.symm.app M).hom = 𝟙 _ from ei.hom_inv_id_app M, Category.comp_id]

private theorem evaluation_faithful (T : Scheme.{u}) :
    JointlyFaithful (ev l E T) := by
  constructor
  intro M N f g h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  rintro ⟨n, V⟩
  ext x
  exact congrArg (fun k ↦ k.val.app (Opposite.op V) x) (h n)

/-- The ordinary closed pushforward is right exact and the specified ordinary open
counit and closed unit form a short exact sequence of strict systems.
Source: Stacks 09AH and 09BM; operations proof (2c), ordinary part of
lem-sp-tower-localization-realization
(blueprint: lem-sp-tower-ordinary-localization).

Proof: apply the source library's open-closed short exact sequence for sheaves of
modules over the finite ring R(n), and transport it through the intrinsic module
sheaf equivalences. Uniqueness of adjoints identifies its maps with the fixed
constant-ring counit and unit. The source closed pushforward preserves finite
colimits, so its conjugate and the isomorphic constant-ring pushforward do too.
Evaluation identifies the open system counit with the finite counit by
Open.counit_evaluation, and the closed system unit with the finite unit by
geometry_unit_evaluation. The family of exact evaluation functors is jointly
faithful, hence jointly conservative. It therefore reflects the zero composite,
short exactness and finite-colimit preservation. No passage to complexes or
derived categories is required. The same argument includes empty complementary
parts and zero systems. -/
theorem tower_ordinary_localization (b : Base l E) (o : Operations l E b)
    {Z U T : Scheme.{u}} (i : Z ⟶ T) (a : U ⟶ T)
    [IsClosedImmersion i] [IsOpenImmersion a] [QuasiCompact a]
    (complement : Set.range a = (Set.range i)ᶜ) :
    PreservesFiniteColimits (o.geometry i).push ∧
      ∀ M : S l E T,
        Mono ((o.openOp a).ordinaryAdjunction.counit.app M) ∧
        Epi ((o.geometry i).ordinaryAdjunction.unit.app M) ∧
        (ComposableArrows.mk₂ ((o.openOp a).ordinaryAdjunction.counit.app M)
          ((o.geometry i).ordinaryAdjunction.unit.app M)).Exact := by
  have hfaith := evaluation_faithful l E T
  have hdetect := hfaith.jointlyReflectsIsomorphisms
  have hfinite := finite_localization l E b i a complement
  have hcol : PreservesFiniteColimits (o.geometry i).push := by
    exact (hdetect.exactFunctor_of_iso (o.geometry i).push
      (fun n ↦ proEtaleConstantRingPushforward (R l E n) i)
      (fun n ↦ ⟨by
        change PreservesFiniteLimits _
        have := (proEtaleConstantRingAdjunction (R l E n) i).isRightAdjoint
        infer_instance, (hfinite n).1⟩)
      (o.geometry i).ordinaryPushEvaluation).2
  refine ⟨hcol, ?_⟩
  intro M
  let f := (o.openOp a).ordinaryAdjunction.counit.app M
  let g := (o.geometry i).ordinaryAdjunction.unit.app M
  have hn (n : ℕ) : Mono ((ev l E T n).map f) ∧ Epi ((ev l E T n).map g) ∧
      (ComposableArrows.mk₂ ((ev l E T n).map f) ((ev l E T n).map g)).Exact := by
    let : Finite (R l E n) := b.finite n
    let e₁ := ((o.openOp a).evaluation n).app ((o.geometry a).pull.obj M) ≪≫
      (sfIntrinsicExtensionByZero a (R l E n)).mapIso
        (((o.openOp a).ordinaryPullEvaluation n).app M)
    let e₃ := ((o.geometry i).ordinaryPushEvaluation n).app
        ((o.geometry i).pull.obj M) ≪≫
      (proEtaleConstantRingPushforward (R l E n) i).mapIso
        (((o.geometry i).ordinaryPullEvaluation n).app M)
    apply transport_sequence _ _
      ((finiteOpenAdjunction l E b a n).counit.app ((ev l E T n).obj M))
      ((proEtaleConstantRingAdjunction (R l E n) i).unit.app ((ev l E T n).obj M))
      e₁ (Iso.refl _) e₃ _ _ ((hfinite n).2 ((ev l E T n).obj M))
    · simp only [Iso.refl_hom, Category.comp_id]
      have h := (o.openOp a).counit_evaluation n M
      apply (cancel_epi (((o.openOp a).evaluation n).inv.app
        ((o.geometry a).pull.obj M))).1
      simpa only [e₁, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        Category.assoc, Iso.inv_hom_id_app_assoc] using h
    · simpa only [e₃, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        Iso.refl_hom, Category.id_comp, Category.assoc] using
        geometry_unit_evaluation l E b (o.geometry i) n M
  have hz : f ≫ g = 0 := hdetect.eq_zero_of_map_eq_zero _ (fun n ↦ by
    rw [Functor.map_comp]
    exact (hn n).2.2.toIsComplex.zero 0 (by decide))
  let S := ShortComplex.mk f g hz
  have hs : S.ShortExact := (hdetect.shortExact_iff S).2 (fun n ↦
    { mono_f := (hn n).1, epi_g := (hn n).2.1, exact := (hn n).2.2.exact 0 })
  exact ⟨hs.mono_f, hs.epi_g, hs.exact.exact_toComposableArrows⟩

end AlgebraicGeometry.ProEtale.SpTowerShriek
