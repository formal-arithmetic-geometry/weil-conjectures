/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTowerData
public import WeilConjectures.SixFunctors.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import all WeilConjectures.AlgebraicGeometry.EllAdicProperConstructibleCohomology
import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealizationSupplement
import WeilConjectures.AlgebraicGeometry.IntegralTowerGeometryLimits
import WeilConjectures.DeligneLaumon.NativeReductionProperComposition
import WeilConjectures.DeligneLaumon.NativeReductionProperFiniteComparison

/-!
# Native proper direct image and whole-system reduction

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-integral-adjunction/sk-prop-sp-integral-adjunction-direct-image.proof.md,
proper factor of clause (2) (blueprint: lem-dla1-native-reduction-proper-direct-image).

The existing `IntegralDirectImageTower` interface retains the ordinary derived category
of strict systems. Its `properReduction` is the actual counit mate, defined before finite
evaluation. `Presentation` contains the recorded coefficient constructions; it is not an
extra geometric hypothesis. `ReductionGeometry` fixes the maps on tensor generators and
flat-term K-flat representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.TwoSquare
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical strict-system direct-image compositor, conjugate to the recorded
pullback compositor, before evaluation.
Source: blueprint direct-image proof, paragraph (3); Mathlib adjunction mates
(blueprint: lem-dla1-native-reduction-proper-direct-image). -/
def nativeSystemPushComp (s : Presentation l E) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    SpTowerShriek.push l E s.base (s.operations.geometry f) ⋙
        SpTowerShriek.push l E s.base (s.operations.geometry g) ≅
      SpTowerShriek.push l E s.base (s.operations.geometry (f ≫ g)) :=
  conjugateIsoEquiv
    ((SpTowerShriek.adjunction l E s.base (s.operations.geometry g)).comp
      (SpTowerShriek.adjunction l E s.base (s.operations.geometry f)))
    (SpTowerShriek.adjunction l E s.base (s.operations.geometry (f ≫ g)))
    (s.operations.comp f g).symm

/-- The finite component of the specified whole-system counit mate, retaining the
finite coefficient action through the normalized pushforward evaluation comparison.
Source: blueprint direct-image proof, paragraph (1)
(blueprint: lem-dla1-native-reduction-proper-direct-image). -/
def nativeProperReductionEvaluation (s : Presentation l E) (q : ReductionGeometry l E s)
    {X Y : Scheme.{u}} (p : X ⟶ Y) (K : Integral l E X) (n : ℕ) :=
  (SpTowerShriek.Ev l E Y n).map (properReduction l E s q p K) ≫
    ((s.operations.geometry p).pushEvaluation n).hom.app
      ((derivedReduction l E s X).obj K)

private theorem properBoundedConstructible
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (p : X ⟶ Y) [IsProper p] (hl : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : Constructible l E X) :
    constantModelBoundedConstructible (spIntegralCondensed l E) Y
      ((CondensedRing.moduleObjectDerivedPushforward (spIntegralCondensed l E) p).obj K.obj) := by
  let assertion (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) : Prop :=
    ∀ [IsCommMonObj R.X] (K : ConstantModelBoundedConstructible R.X X),
      constantModelBoundedConstructible R.X Y
        ((CondensedRing.moduleObjectDerivedPushforward R.X p).obj K.obj)
  have h : assertion (sfbCondensedIntegers l E) := by
    rw [← IntegralConstantModel.pointEquality l E]
    intro _ K
    exact CondensedRing.proper_integralModel_bounded l E p hl K.obj K.property
  exact h K

private theorem reductionConstructible (s : Presentation l E) (T : Scheme.{u})
    [CompactSpace T] [QuasiSeparatedSpace T] (K : Integral l E T)
    (hK : constantModelBoundedConstructible (spIntegralCondensed l E) T K) :
    _root_.DerivedCategory.finiteTorAmplitude _ K ∧
      spConstructibleTorTowers l E T (s.towers T) ((red l E s T).obj K) := by
  let e := (sectionEquivalence l E T).unitIso.app K
  let := (constantModelConstructibleFiniteTor_wellDefined
    (spIntegralCondensed l E) T).2.1
  let := (constantModelConstructibleFiniteTor_wellDefined
    (spIntegralCondensed l E) T).2.2.2.1
  have hK' : constantModelBoundedConstructible (spIntegralCondensed l E) T
      ((spIntegralInternalization l E T).obj ((sectionEquivalence l E T).functor.obj K)) :=
    (constantModelBoundedConstructible (spIntegralCondensed l E) T).prop_of_iso e hK
  have h := (s.reduction T).constructible inferInstance inferInstance
    ((sectionEquivalence l E T).functor.obj K) hK'
  exact ⟨(_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e.symm h.1, h.2.1.1⟩

private theorem mateComponent
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (F : A ⥤ C) (G : B ⥤ D)
    (c : F ⋙ L' ⟶ L ⋙ G) (K : B) :
    (mateEquiv a b (TwoSquare.mk _ _ _ _ c)).app K =
      b.homEquiv _ _ (c.app (R.obj K) ≫ G.map (a.counit.app K)) := by
  apply (b.homEquiv (F.obj (R.obj K)) (G.obj K)).symm.injective
  exact (mateEquiv_counit a b (TwoSquare.mk _ _ _ _ c) K).trans
    ((b.homEquiv _ _).symm_apply_apply _).symm

private def reductionMate (s : Presentation l E) (q : ReductionGeometry l E s)
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    CondensedRing.moduleObjectDerivedPushforward (spIntegralCondensed l E) p ⋙
      derivedReduction l E s Y ⟶
    derivedReduction l E s X ⋙
      SpTowerShriek.push l E s.base (s.operations.geometry p) :=
  (mateEquiv
    (CondensedRing.derivedUpperStarLowerStarAdjunction (spIntegralCondensed l E) p)
    (SpTowerShriek.adjunction l E s.base (s.operations.geometry p))
    (TwoSquare.mk _ _ _ _ (q.pullback p).derived.inv)).natTrans

private theorem reductionMate_app (s : Presentation l E) (q : ReductionGeometry l E s)
    {X Y : Scheme.{u}} (p : X ⟶ Y) (K : Integral l E X) :
    (reductionMate l E s q p).app K = properReduction l E s q p K :=
  mateComponent _ _ _ _ _ _

set_option maxHeartbeats 1600000 in
-- Normalizing the derived adjunctions and their system coordinates needs this budget.
private theorem properReductionCompositionOfPullback (s : Presentation l E)
    (q : ReductionGeometry l E s)
    (hcoh : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      (((TwoSquare.mk _ _ _ _ (q.pullback g).derived.inv) ≫ᵥ
        (TwoSquare.mk _ _ _ _ (q.pullback f).derived.inv)).whiskerRight
          (s.operations.comp f g).inv).whiskerLeft
            (CondensedRing.leftDerivedUpperStarComp (spIntegralCondensed l E) f g).inv =
        TwoSquare.mk _ _ _ _ (q.pullback (f ≫ g)).derived.inv) :
(∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (K : Integral l E X),
        (derivedReduction l E s Z).map
            ((CondensedRing.CohomologyTransport.pushComp (spIntegralCondensed l E) f g).hom.app
              K) ≫ properReduction l E s q (f ≫ g) K =
          properReduction l E s q g
              ((CondensedRing.moduleObjectDerivedPushforward (spIntegralCondensed l E) f).obj K) ≫
            (SpTowerShriek.push l E s.base (s.operations.geometry g)).map
              (properReduction l E s q f K) ≫
            (conjugateIsoEquiv
              ((SpTowerShriek.adjunction l E s.base (s.operations.geometry g)).comp
                (SpTowerShriek.adjunction l E s.base (s.operations.geometry f)))
              (SpTowerShriek.adjunction l E s.base (s.operations.geometry (f ≫ g)))
              (s.operations.comp f g).symm).hom.app
              ((derivedReduction l E s X).obj K)) := by
  intro X Y Z f g K
  have h := congrArg (fun δ ↦
    (mateEquiv
      (CondensedRing.derivedUpperStarLowerStarAdjunction (spIntegralCondensed l E) (f ≫ g))
      (SpTowerShriek.adjunction l E s.base (s.operations.geometry (f ≫ g))) δ).app K)
    (hcoh f g)
  rw [conjugateEquiv_mateEquiv_vcomp, mateEquiv_conjugateEquiv_vcomp,
    mateEquiv_hcomp] at h
  have h' :
      (derivedReduction l E s Z).map
          ((CondensedRing.CohomologyTransport.pushComp (spIntegralCondensed l E) f g).inv.app K) ≫
        (properReduction l E s q g
            ((CondensedRing.moduleObjectDerivedPushforward (spIntegralCondensed l E) f).obj K) ≫
          (SpTowerShriek.push l E s.base (s.operations.geometry g)).map
            (properReduction l E s q f K) ≫
          (nativeSystemPushComp l E s f g).hom.app ((derivedReduction l E s X).obj K)) =
        properReduction l E s q (f ≫ g) K := by
    rw [← reductionMate_app l E s q g _, ← reductionMate_app l E s q f K,
      ← reductionMate_app l E s q (f ≫ g) K]
    simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, Category.assoc, reductionMate,
      nativeSystemPushComp, CondensedRing.CohomologyTransport.pushComp,
      conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_apply_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.id_obj, Functor.comp_obj,
      CondensedRing.moduleObjectDerivedPushforward, CondensedRing.CohomologyTransport.R,
      pull, CondensedRing.moduleObjectDerivedPullback, TwoSquare.natTrans] using h
  rw [← h']
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, nativeSystemPushComp]


/-- Proper native direct image preserves bounded constructibility and commutes with
reduction as a natural isomorphism in the ordinary derived category of strict systems.
The isomorphism is the specified counit mate, not a family assembled from evaluations.
The first two equations give its composition and actual-counit compatibilities before
any evaluation; composition includes precomposition and postcomposition by scheme
isomorphisms. The finite component is the evaluation of this same map. The final
predicate supplies one Tor and cohomological interval for all positive quotient levels.

Source: blueprint direct-image proof, paragraphs (1)--(3)
(blueprint: lem-dla1-native-reduction-proper-direct-image).

Proof: take the normalized q of normalized_geometry_limits
(lem-sp-integral-tower-geometry-limits). Composition: transpose the pullback-square
coherence of lem-dla1-native-reduction-proper-composition through the integral and system
adjunctions; the Mathlib conjugate/mate vertical-composition identities and mateEquiv_hcomp
give the component equation, the components are properReduction by the mate counit identity,
and cancelling the inverse integral compositor gives the first equation. The counit equation
is the inverse Hom bijection applied to the definition of properReduction. Over k, finite
type and quasi-compactness make X and Y Noetherian and l is a unit in every stalk of Y; the
proper integral-model constructibility theorem (lem-sfb-noetherian-proper-constructible-cohomology),
transported along IntegralConstantModel.pointEquality
(def-sfb-integral-constant-model-realization), gives native bounded constructibility. The
recorded normalized reduction tower (det-sp-reduction-tower-normalized,
det-def-sfb-constructible-tor-amplitude) gives finite Tor amplitude and the constructible
tower. The mate of the inverse normalized pullback square is a natural transformation before
evaluation with components properReduction; by
lem-dla1-native-reduction-proper-finite-comparison every finite evaluation of each
component is invertible, and joint detection by evaluations makes it a natural isomorphism.
No smoothness or absolute cohomological-dimension hypothesis is used. -/
theorem nativeReductionProperDirectImage (s : Presentation l E) :
    ∃ q : ReductionGeometry l E s,
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (K : Integral l E X),
        (derivedReduction l E s Z).map
            ((CondensedRing.CohomologyTransport.pushComp (spIntegralCondensed l E) f g).hom.app
              K) ≫ properReduction l E s q (f ≫ g) K =
          properReduction l E s q g
              ((CondensedRing.moduleObjectDerivedPushforward (spIntegralCondensed l E) f).obj K) ≫
            (SpTowerShriek.push l E s.base (s.operations.geometry g)).map
              (properReduction l E s q f K) ≫
            (nativeSystemPushComp l E s f g).hom.app ((derivedReduction l E s X).obj K)) ∧
      (∀ {X Y : Scheme.{u}} (p : X ⟶ Y) (K : Integral l E X),
        (SpTowerShriek.pull l E s.base (s.operations.geometry p)).map
            (properReduction l E s q p K) ≫
            (SpTowerShriek.adjunction l E s.base (s.operations.geometry p)).counit.app
              ((derivedReduction l E s X).obj K) =
          (q.pullback p).derived.inv.app
              ((CondensedRing.moduleObjectDerivedPushforward (spIntegralCondensed l E) p).obj K) ≫
            (derivedReduction l E s X).map
              ((CondensedRing.derivedUpperStarLowerStarAdjunction
                (spIntegralCondensed l E) p).counit.app K)) ∧
      ∀ (k : Type u) [Field k] [PerfectField k] (_hl : IsUnit (l : k))
        (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
        [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
        [QuasiCompact (X ↘ Spec (.of k))]
        [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
        [QuasiCompact (Y ↘ Spec (.of k))]
        (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p],
        (∀ K : Constructible l E X,
          constantModelBoundedConstructible (spIntegralCondensed l E) Y
            ((CondensedRing.moduleObjectDerivedPushforward (spIntegralCondensed l E) p).obj
              K.obj)) ∧
        ∃ β :
          (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙
              CondensedRing.moduleObjectDerivedPushforward (spIntegralCondensed l E) p ⋙
                derivedReduction l E s Y ≅
            (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙
              derivedReduction l E s X ⋙
                SpTowerShriek.push l E s.base (s.operations.geometry p),
          (∀ K : Constructible l E X, β.hom.app K = properReduction l E s q p K.obj) ∧
          ∀ K : Constructible l E X,
            (∀ n : ℕ, IsIso (nativeProperReductionEvaluation l E s q p K.obj n)) ∧
            DerivedCategory.finiteTorAmplitude _
              ((CondensedRing.moduleObjectDerivedPushforward (spIntegralCondensed l E) p).obj
                K.obj) ∧
            spConstructibleTorTowers l E Y (s.towers Y)
              ((red l E s Y).obj
                ((CondensedRing.moduleObjectDerivedPushforward (spIntegralCondensed l E) p).obj
                  K.obj)) := by
  obtain ⟨q, _, _⟩ := normalized_geometry_limits l E s
  refine ⟨q, properReductionCompositionOfPullback l E s q
    (nativeReductionPullbackComposition l E s q), ?_, ?_⟩
  · intro X Y p K
    exact ((SpTowerShriek.adjunction l E s.base (s.operations.geometry p)).homEquiv
      _ _).symm_apply_apply _
  · intro k _ _ hl X Y _ _ _ _ _ _ _ _ p _ _
    let : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    let : IsLocallyNoetherian Y :=
      LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
    let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
    let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
    let : IsNoetherian X := ⟨⟩
    let : IsNoetherian Y := ⟨⟩
    have hunit (y : Y) : IsUnit (l : Y.presheaf.stalk y) := by
      have h₁ : IsUnit (l : (Spec (.of k)).presheaf.stalk ((Y ↘ Spec (.of k)) y)) := by
        simpa using hl.map
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤
            ((Y ↘ Spec (.of k)) y) trivial).hom
      simpa using h₁.map ((Y ↘ Spec (.of k)).stalkMap y).hom
    have hbc := properBoundedConstructible l E p hunit
    have hfinite := nativeReductionProperFiniteComparison l E s q k hl X Y p
    refine ⟨hbc, ?_⟩
    let α := Functor.whiskerLeft
      (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι
      (reductionMate l E s q p)
    have hα (K : Constructible l E X) : IsIso (α.app K) := by
      apply (s.laws.detects Y _).2
      intro n
      have h := hfinite K n
      rw [← reductionMate_app l E s q p K.obj] at h
      exact (isIso_comp_right_iff _ _).mp h
    let : ∀ K, IsIso (α.app K) := hα
    let β := NatIso.ofComponents (fun K ↦ asIso (α.app K)) (fun f ↦ α.naturality f)
    refine ⟨β, ?_, ?_⟩
    · intro K
      exact reductionMate_app l E s q p K.obj
    · intro K
      refine ⟨?_, reductionConstructible l E s Y _ (hbc K)⟩
      exact hfinite K

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
