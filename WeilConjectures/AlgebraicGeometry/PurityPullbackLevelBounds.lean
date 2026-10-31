/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma
import WeilConjectures.AlgebraicGeometry.OrderedLineLevelBounds
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleConstructibility

/-! # One-level bounds for the actual twisted pullback tower

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, (3).
The natural level n denotes the positive exponent n+1.
(blueprint: lem-sp-purity-pullback-level-bounds).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpPurityReduction

private theorem torAmplitude_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (h : HasProEtaleTorAmplitude T A K a b) :
    HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem etaleBounded_iff (T : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [Finite A] (K : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, _, hab⟩
    refine ⟨⟨⟨a, (DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hab i (.inl hi))⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hab i (.inr hi))⟩⟩, ?_⟩
    intro i
    exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨?_, min a b, b, min_le_right _ _, ?_⟩
    · intro i
      exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i)
    · intro i hi
      rcases hi with hi | hi
      · exact (DerivedCategory.isGE_iff K a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
      · exact (DerivedCategory.isLE_iff K b).1 hb i hi

private noncomputable def intrinsicComparisonPullbackIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :
    ProEtale.finiteCoefficientIntrinsicComparison Y A ⋙ proEtaleConstantRingPullback A f ≅
      Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X A :=
  Functor.isoWhiskerLeft _ (openSquarePullbackModel A f) ≪≫
    (Functor.isoWhiskerLeft
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y)
      ((sfIntrinsicModuleEquivalence Y A).funInvIdAssoc
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
          ProEtale.finiteCoefficientIntrinsicRealization X A))) ≪≫
    Functor.isoWhiskerRight
      (ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
      (ProEtale.finiteCoefficientIntrinsicRealization X A)

private noncomputable def intrinsicDerivedComparisonPullbackIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] [Finite A] :
    ProEtale.finiteCoefficientIntrinsicDerivedComparison Y A ⋙
        proEtaleConstantRingDerivedPullback A f ≅
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).mapDerivedCategory ⋙
        ProEtale.finiteCoefficientIntrinsicDerivedComparison X A :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (intrinsicComparisonPullbackIso f A) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

private theorem comparison_tor_iff (T : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (a b : ℤ) (hab : a ≤ b)
    (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T)
    (hK : DerivedCategory.TStructure.t.plus K) :
    Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} A) T a b K ↔
      HasProEtaleTorAmplitude T A
        ((ProEtale.finiteCoefficientIntrinsicDerivedComparison T A).obj K) a b := by
  let C := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T
  let R := ProEtale.finiteCoefficientIntrinsicRealization T A
  let e := (Functor.mapDerivedCategoryCompIso C R).app K
  have h := ProEtale.comparison_torAmplitudeIn_iff A T a b hab ⟨K, hK⟩
  exact h.trans ⟨fun h ↦ torAmplitude_of_iso T A e.symm a b h,
    fun h ↦ torAmplitude_of_iso T A e a b h⟩

/-- Pullback of an arbitrary finite constant coefficient ring preserves bounded
constructibility and the specified Tor interval. In particular it applies directly
to ell-power quotients, without changing the coefficient presentation.

Source: blueprint latest, sec-proetale-coefficients/sk-cor-pe-finite-tor-comparison/
lem-sf-pullback-tor-amplitude.proof.md; Stacks Tags 03D2, 0735 and 08FZ.
(blueprint: lem-sf-pullback-tor-amplitude).

Proof: descend the bounded constructible pro-etale complex through the finite-ring
intrinsic derived comparison. Exact etale inverse image preserves bounded
constructibility. The constant-ring comparison square identifies its realization
with the specified derived constant-ring pullback. Reflect the given Tor interval
through the comparison, pull a flat model back termwise, and reflect the same
interval back on X. Transport both conclusions along the comparison isomorphism.
The input finite-Tor witness is not used: the specified interval supplies one.
-/
private theorem finite_constant_pullback_bounds
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (A : Type u) [CommRing A] [Finite A] (f : X ⟶ Y)
    (K : proEtaleDerivedCategory Y A) (hK : spFiniteConstructibleTor Y A K)
    (a b : ℤ) (hTor : HasProEtaleTorAmplitude Y A K a b) :
    spFiniteConstructibleTor X A ((proEtaleConstantRingDerivedPullback A f).obj K) ∧
      HasProEtaleTorAmplitude X A ((proEtaleConstantRingDerivedPullback A f).obj K)
        a b := by
  classical
  let B := ULift.{u + 1, u} A
  let F := proEtaleConstantRingDerivedPullback A f
  obtain ⟨c, d, hcd, hvan⟩ := hK.1
  obtain ⟨L, ⟨eL⟩⟩ := ((finiteRing_constructibleDerived_origin Y A).2.2.1 K).mpr
    ⟨hK.2.1, c, d, hcd, hvan⟩
  have hbc := (etaleBounded_iff Y B L.obj).mp L.property
  let P := (Etale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.obj L.obj
  have hbcP : Etale.DerivedCategory.isBoundedConstructible B X P :=
    (etaleBounded_iff X B P).mpr (hbc.mapDerivedCategory_upperStar f)
  have hplus : DerivedCategory.TStructure.t.plus L.obj := hbc.1.1
  have hplusP : DerivedCategory.TStructure.t.plus P :=
    ((etaleBounded_iff X B P).mp hbcP).1.1
  have htL : Etale.DerivedCategory.hasTorAmplitudeIn B Y a b L.obj :=
    (comparison_tor_iff Y A a b hTor.1 L.obj hplus).mpr
      (torAmplitude_of_iso Y A eL.symm a b hTor)
  have htP : Etale.DerivedCategory.hasTorAmplitudeIn B X a b P := by
    apply Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
    exact (Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) X a b).prop_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} B) f).app L.obj)
      (Etale.torAmplitudeIn_leftDerivedUpperStar (ModuleCat.{u + 1} B) f a b
        (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp htL))
  let eP : (ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj P ≅
      F.obj K :=
    ((intrinsicDerivedComparisonPullbackIso f A).app L.obj).symm ≪≫ F.mapIso eL
  have himage := ((finiteRing_constructibleDerived_origin X A).2.2.1 (F.obj K)).mp
    ⟨⟨P, hbcP⟩, ⟨eP⟩⟩
  have ht : HasProEtaleTorAmplitude X A (F.obj K) a b :=
    torAmplitude_of_iso X A eP a b
      ((comparison_tor_iff X A a b hTor.1 P hplusP).mp htP)
  exact ⟨⟨himage.2, himage.1, a, b, ht⟩, ht⟩


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  [b : SpTowerShriek.Base l E] (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- At one finite level, actual strict-tower pullback and the ordered shifted Tate
line preserve constructibility and translate a specified Tor interval by -2d.
Only constructibility, finite Tor amplitude, and the specified Tor bound at this
level are assumed. K is an arbitrary derived strict tower: there is no global
constructibility, uniform bound, or normalization hypothesis.

Source: gamma proof (3), uniform-domain calculation, and
lem-sp-purity-conjugates-tower-reduction, proof Step 1.
(blueprint: lem-sp-purity-pullback-level-bounds).

Proof: use levelComparison and the realization counit to evaluate the inverse
realization in the original strict tower category. The pullEvaluation comparison
identifies the pulled-back evaluation with finite derived inverse image. Write
ell as a unit times the e-th power of a uniformizer, identifying the ell^(n+1)
quotient with the e(n+1)-st uniformizer quotient. Apply
lem-sf-pullback-tor-amplitude to the constructible finite-Tor evaluation supplied
by hK.
The ordered line is the d-fold tensor product of the positive Tate line shifted
by two. Its finite evaluations are locally free rank-one sheaves shifted by 2d:
evaluation commutes with tensor and shift, and w.level supplies the signed line
identifications. Tensor with these lines preserves constructibility and the
specified Tor interval, by prop-weil-twist-preserves. The shift formula
H^i(C[2d]) = H^(i+2d)(C), applied to every degree-zero module test, gives the
Tor interval [a-2d,z-2d]. Transport constructibility and this Tor bound along
the specified evaluation isomorphisms. Cohomological bounds are not part of this
lemma: the caller obtains those by testing Tor amplitude against the unit.
The argument includes d=0 (the tensor unit), equal
bounds, and the first positive coefficient level; it never uses a reduction map.
-/
theorem pullback_level_bounds
    (D : FiniteFieldDatum.{u}) [CharP D.k D.p] (hne : l ≠ D.p)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (w : SpChartAdmissibility.Twists l E X)
    (K : spDerivedCoefficientTowers l E Y (q.abelian Y)) (n : ℕ)
    (hK : spFiniteConstructibleTor Y (SpTowerShriek.R l E n)
      ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj K))
    (a z : ℤ) (haz : a ≤ z)
    (hTor : HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
      ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj K) a z) :
    let P := (SpTowerCalculus.realization l E b X (q.abelian X)).inverse.obj
      ((SpTowerShriek.tensor l E b X).obj
        ((SpTowerShriek.pull l E b (o.geometry f)).obj
          ((SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.obj K),
          SpTowerGamma.orderedLine l E b X w d))
    let Pn := (spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj P
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X (SpTowerShriek.R l E n)
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X (SpTowerShriek.R l E n))) i).obj Pn)) ∧
      HasProEtaleTorAmplitude X (SpTowerShriek.R l E n) Pn
        (a - 2 * d) (z - 2 * d) := by
  let R := SpTowerShriek.R l E n
  let FX := SpTowerCalculus.realization l E b X (q.abelian X)
  let FY := SpTowerCalculus.realization l E b Y (q.abelian Y)
  let V := (SpTowerShriek.tensor l E b X).obj
    ((SpTowerShriek.pull l E b (o.geometry f)).obj (FY.functor.obj K),
      SpTowerGamma.orderedLine l E b X w d)
  let eY := (SpTowerCalculus.levelComparison l E b q Y n).app K
  let ePull := ((o.geometry f).pullEvaluation n).app (FY.functor.obj K) ≪≫
    (proEtaleConstantRingDerivedPullback R f).mapIso eY
  let Pn := (spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj
    (FX.inverse.obj V)
  let e : Pn ≅ ((b.calculus X).levelClosed n).tensor.obj
      ((proEtaleConstantRingDerivedPullback R f).obj
        ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj K),
          (SpTowerShriek.Ev l E X n).obj (SpTowerGamma.orderedLine l E b X w d)) :=
    ((SpTowerCalculus.levelComparison l E b q X n).app (FX.inverse.obj V)).symm ≪≫
      (SpTowerShriek.Ev l E X n).mapIso (FX.counitIso.app V) ≪≫
      ((b.calculus X).tensorEvaluation n).app _ ≪≫
      ((b.calculus X).levelClosed n).tensor.mapIso (Iso.prod ePull (Iso.refl _))
  obtain ⟨hc, ht⟩ := finite_constant_pullback_bounds R f _ hK a z ⟨haz, hTor.2⟩
  obtain ⟨hc', ht'⟩ := ordered_line_level_bounds l E D hne X w d n _ hc a z ht
  refine ⟨?_, ?_⟩
  · intro i
    have hi := hc' i
    rw [proEtaleModuleRestriction_constructible_iff] at hi ⊢
    exact isConstructible_of_iso
      ((proEtaleModuleRestriction X R).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e.symm)) hi
  · refine ⟨ht'.1, ?_⟩
    intro L Q hL g hg hQ M i hi
    obtain ⟨eL⟩ := hL
    exact ht'.2 L Q ⟨eL ≪≫ e⟩ g hg hQ M i hi

end AlgebraicGeometry.ProEtale.SpPurityReduction

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
