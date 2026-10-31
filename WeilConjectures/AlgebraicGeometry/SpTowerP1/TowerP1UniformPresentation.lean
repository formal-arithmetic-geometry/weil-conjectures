/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Data
import WeilConjectures.AlgebraicGeometry.SpTowerP1Uniform.TowerP1UniformCtfDomains

/-! # Constructible tower bounds in the recorded presentation

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md
(blueprint: lem-sp-tower-p1-uniform-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerP1
open SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

private theorem constructible_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {F G : proEtaleRingModules T (proEtaleConstantRing T A)} (e : F ≅ G)
    (h : IsConstructibleProEtaleModuleSheaf T A F) :
    IsConstructibleProEtaleModuleSheaf T A G := by
  obtain ⟨strata, hn, hs⟩ := h
  refine ⟨strata, hn, fun i ↦ ?_⟩
  let e' := (proEtaleConstantRingPullback A (strata.immersion i)).mapIso e
  obtain ⟨I, U, f, hc, ht⟩ := (hs i).1
  refine ⟨⟨I, U, f, hc, fun j ↦ ?_⟩, ?_⟩
  · obtain ⟨P, ⟨hP⟩⟩ := ht j
    exact ⟨P, ⟨(SheafOfModules.overFunctor _ (U j)).mapIso e'.symm ≪≫ hP⟩⟩
  · intro Ω _ _ y
    let H := geometricRingModuleStalkFunctor y (proEtaleConstantRing (strata.domain i) A)
    have : Finite (H.obj ((proEtaleConstantRingPullback A
        (strata.immersion i)).obj F)) := (hs i).2 Ω y
    exact Finite.of_injective (H.mapIso e'.symm).toLinearEquiv
      (H.mapIso e'.symm).toLinearEquiv.injective

private theorem tor_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude T A K a b) : HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P he f hf hp M i hi
  exact h.2 C P (he.map (fun z ↦ z ≪≫ e.symm)) f hf hp M i hi

private theorem finite_ctf_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L)
    (h : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L := by
  obtain ⟨⟨a, b, hab, hb⟩, hc, c, d, ht⟩ := h
  refine ⟨⟨a, b, hab, fun i hi ↦ ?_⟩, fun i ↦ ?_, c, d, tor_iso T A e c d ht⟩
  · exact (hb i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  · exact constructible_iso T A ((DerivedCategory.homologyFunctor _ i).mapIso e) (hc i)

private theorem ctf_iso (T : Scheme.{u}) (a : SpCoefficientTowersAbelian l E T)
    {K L : spDerivedCoefficientTowers l E T a} (e : K ≅ L)
    (h : spConstructibleTorTowers l E T a K) : spConstructibleTorTowers l E T a L := by
  refine ⟨fun n ↦ finite_ctf_iso T _
    ((spDerivedCoefficientEvaluation l E T a n).mapIso e) (h.1 n), ?_⟩
  obtain ⟨r, s, c, d, hrs, hcd, hb⟩ := h.2
  refine ⟨r, s, c, d, hrs, hcd, fun n ↦ ⟨fun i hi ↦ ?_, ?_⟩⟩
  · exact ((hb n).1 i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso
        ((spDerivedCoefficientEvaluation l E T a n).mapIso e)).symm
  · exact tor_iso T _ ((spDerivedCoefficientEvaluation l E T a n).mapIso e) c d (hb n).2

private theorem domain_iso (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    {K L : SpTowerShriek.D l E T} (e : K ≅ L) (h : domain l E b T K) :
    domain l E b T L := by
  refine ⟨?_, fun n ↦ ?_⟩
  · obtain ⟨a, ha⟩ := h.1
    have := ha
    exact ⟨a, DerivedCategory.TStructure.t.isGE_of_iso e a⟩
  · obtain ⟨o⟩ := h.2 n
    exact ⟨{ o with realization := o.realization ≪≫ (SpTowerShriek.Ev l E T n).mapIso e }⟩

/-- Transport of the uniform-domain theorem to the section coordinates of p.
Source: standing-setting restriction, det-sp-tower-p1-adjunction steps 12--14
(blueprint: lem-sp-tower-p1-uniform-presentation).

Proof: apply towerP1_uniform_ctf_domains with c = p.classes and aS,aP. For an
ambient object M use the inverse realization and the counit isomorphism identifying
its forward realization with M. The first clause gives boundedness and all origin
witnesses, transported along this isomorphism. For direct image use the second clause,
rewrite the recorded geometry by p.q_geometry, and transport its input using the
realization counit. This identifies the output with the inverse realization of p.F M.
For twisted pullback use the third clause and the same counit and geometry equality;
its twist is literally the recorded shifted line in Presentation.G. Constructible
finite-Tor predicates are invariant under these isomorphisms: evaluation and homology
map isomorphisms to isomorphisms, constructibility transports its strata and local
trivializations, and Tor vanishing transports the tensor homology isomorphisms. The
same intervals are retained. No normalization of transitions or new bound is imposed.
In particular the zero object and the empty scheme are included. -/
theorem towerP1_uniform_in_presentation (p : Presentation l E S hS) :
    ∀ (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar], l ≠ pchar →
    ∀ [S.Over (Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
      [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
      (aS : SpCoefficientTowersAbelian l E S)
      (aP : SpCoefficientTowersAbelian l E (ProjectiveLine S)),
      (∀ M : SpTowerShriek.D l E (ProjectiveLine S),
        uniform l E p.classes.base (ProjectiveLine S) aP M →
          domain l E p.classes.base (ProjectiveLine S) M ∧
            uniform l E p.classes.base S aS ((p.F l E).obj M)) ∧
      (∀ K : SpTowerShriek.D l E S, uniform l E p.classes.base S aS K →
        domain l E p.classes.base S K ∧ uniform l E p.classes.base (ProjectiveLine S) aP
          ((p.G l E).obj K)) := by
  intro pchar _ k _ _ hlp _ _ _ _ aS aP
  obtain ⟨hdom, hpush, hpull, _⟩ :=
    SpTowerP1Uniform.towerP1_uniform_ctf_domains l E pchar k hlp S hS p.classes aS aP
  have hd (T : Scheme.{u}) (a : SpCoefficientTowersAbelian l E T)
      (hT : T = S ∨ T = ProjectiveLine S) (K : SpTowerShriek.D l E T)
      (hK : uniform l E p.classes.base T a K) : domain l E p.classes.base T K := by
    exact domain_iso l E p.classes.base T
      ((spTowerShriekRealization l E p.classes.base T a).counitIso.app K)
      (hdom T a hT _ hK)
  constructor
  · intro M hM
    refine ⟨hd _ aP (Or.inr rfl) M hM, ?_⟩
    have hm := hpush _ hM
    dsimp only [SpTowerP1Uniform.push, Functor.comp_obj] at hm
    dsimp only [uniform, Presentation.F]
    rw [p.q_geometry]
    exact ctf_iso l E S aS
      ((spTowerShriekRealization l E p.classes.base S aS).inverse.mapIso
        ((SpTowerShriek.push l E p.classes.base p.classes.projective.geometry).mapIso
          ((spTowerShriekRealization l E p.classes.base
            (ProjectiveLine S) aP).counitIso.app M))) hm
  · intro K hK
    refine ⟨hd _ aS (Or.inl rfl) K hK, ?_⟩
    have hk := hpull _ hK
    dsimp only [SpTowerP1Uniform.pullTwist, Functor.comp_obj] at hk
    dsimp only [uniform, Presentation.G, Functor.comp_obj]
    rw [p.q_geometry]
    exact ctf_iso l E (ProjectiveLine S) aP
      ((spTowerShriekRealization l E p.classes.base (ProjectiveLine S) aP).inverse.mapIso
        ((SpTowerShriek.tensor l E p.classes.base (ProjectiveLine S)).mapIso
          (Iso.prod
            ((SpTowerShriek.pull l E p.classes.base p.classes.projective.geometry).mapIso
              ((spTowerShriekRealization l E p.classes.base S aS).counitIso.app K))
            (Iso.refl _)))) hk

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
