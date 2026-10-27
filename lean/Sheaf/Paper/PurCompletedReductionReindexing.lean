/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.Paper.CompletedCompactSupportExchange
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.StrictTowerOperations
public import Sheaf.Paper.CompletedDirectImageLimits
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Sheaf.Paper.PurCompletedReindexingData
import Sheaf.Paper.PurCompletedModuleReindexing
import Sheaf.Paper.PurReindexingLimitNormalization
import Sheaf.Paper.PurReindexingOrdinaryMate
import Sheaf.Paper.PurReindexingDerivedMates
import all Sheaf.Paper.CompletedDirectImageLimits
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Completed reduction reindexing under scheme isomorphisms

The concrete definitions are re-exported from PurCompletedReindexingData.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleDirectImage
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 2000] reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory

private def normalizedEquivalence
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (e : C ≌ D)
    (he : e.functor = F) (hi : e.inverse = G) : C ≌ D :=
  (e.changeFunctor (eqToIso he)).changeInverse (eqToIso hi)

private theorem inverseComparison_normalization
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f]
    {Z : D} (b : F.obj Y ≅ Z) :
    (b.symm ≪≫ (F.mapIso (asIso f)).symm).hom ≫ F.map f = b.inv := by
  change (b.inv ≫ F.map (inv f)) ≫ F.map f = b.inv
  rw [Category.assoc, ← F.map_comp, IsIso.inv_hom_id, F.map_id, Category.comp_id]

private theorem completeInverse_normalization
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {K L : C} (f : K ⟶ L) [IsIso f]
    {Z : D} (b : F.obj L ≅ Z) (a : F.obj K ⟶ Z)
    (ha : a = F.map f ≫ b.hom) :
    ∃ e : Z ≅ F.obj K, e.inv = a ∧ e.hom ≫ F.map f = b.inv := by
  refine ⟨b.symm ≪≫ (F.mapIso (asIso f)).symm, ha.symm, ?_⟩
  exact inverseComparison_normalization F f b

private theorem normalizedDerivedEquivalence
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : C ≌ D) (he : e.functor = F) (hi : e.inverse = G) :
    ∃ eD : DerivedCategory C ≌ DerivedCategory D,
      eD.functor = F.mapDerivedCategory ∧ eD.inverse = G.mapDerivedCategory := by
  let en := normalizedEquivalence F G e he hi
  have : en.functor.Additive := ‹F.Additive›
  have : en.inverse.Additive := ‹G.Additive›
  exact ⟨en.mapDerivedCategory, rfl, rfl⟩

private theorem normalizedTowerEquivalence
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (e : C ≌ D)
    (he : e.functor = F) (hi : e.inverse = G) :
    ∃ eT : (ℕᵒᵖ ⥤ C) ≌ (ℕᵒᵖ ⥤ D),
      eT.functor = (Functor.whiskeringRight ℕᵒᵖ C D).obj F ∧
      eT.inverse = (Functor.whiskeringRight ℕᵒᵖ D C).obj G := by
  exact ⟨(normalizedEquivalence F G e he hi).congrRight (E := ℕᵒᵖ), rfl, rfl⟩

private theorem reindexingAt {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] :
    PurCompletedReindexingAt d u := by
  classical
  have ho := purCompletedModuleReindexing d u
  have hsections := ho.1
  let e := ho.2.choose
  have he := ho.2.choose_spec.1
  have hi := ho.2.choose_spec.2
  let P := proEtaleRingModulePullback u (d.completedRing T)
    (d.completedRing T') (d.integralRingIso u)
  let R := proEtaleRingModulePullback (inv u) (d.completedRing T')
    (d.completedRing T) (d.integralRingIso (inv u))
  have htw := normalizedTowerEquivalence P R e he hi
  let et := htw.choose
  have ht := htw.choose_spec.1
  have hit := htw.choose_spec.2
  have hD := normalizedDerivedEquivalence P R e he hi
  have hTD := normalizedDerivedEquivalence (d.towerModulePull u)
    (d.towerModulePull (inv u)) et ht hit
  have hl := purReindexingLimitNormalization d u
  let beta := hl.choose
  have hbeta := hl.choose_spec.1
  let b := hl.choose_spec.2.choose
  have hb := hl.choose_spec.2.choose_spec.1
  have hunit := hl.choose_spec.2.choose_spec.2
  refine ⟨hsections, ⟨e, he, hi⟩,
    (show PreservesFiniteLimits P from inferInstance),
    (show PreservesFiniteColimits P from inferInstance),
    ⟨et, ht, hit⟩,
    (show PreservesFiniteLimits (d.towerModulePull u) from inferInstance),
    (show PreservesFiniteColimits (d.towerModulePull u) from inferInstance),
    hD, hTD,
    ⟨beta, hbeta, b, hb, ?_⟩, ?_, ?_, ?_⟩
  · intro K hK
    have : IsIso (d.completionUnit T K) := hK
    exact completeInverse_normalization (d.pull u) (d.completionUnit T K)
      (b.app ((completedReductionTower T d).obj K)) (d.ordinaryToCompleted u K) (hunit K)
  · exact (completedReductionPullbackIso_existsUnique d u).choose_spec.1
  · intro n M W x a
    exact levelPullIso_tensor d u n M W a x
  · intro M n m a
    exact completedReductionLevelPullbackIso_transition d u M a

private theorem whiskerCompositeMap_isIso
    {J C D D' E : Type*} [Category J] [Category C] [Category D] [Category D'] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E)
    (a : F ⋙ G ⟶ F' ⋙ G') [IsIso a] :
    IsIso (purWhiskerCompositeMap (J := J) F G F' G' a) := by
  unfold purWhiskerCompositeMap
  infer_instance

private theorem reindexingSquare {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    [IsIso v] [IsIso g] (sq : ChosenCartesianSquare v p' p g) :
    PurCompletedReindexingSquare d sq := by
  have ho := purReindexingOrdinaryMate d sq
  have : IsIso (purReindexingModuleMate d sq) := ho.1
  have ht : IsIso (purReindexingTowerModuleMate d sq) := by
    exact whiskerCompositeMap_isIso (J := ℕᵒᵖ) _ _ _ _ (purReindexingModuleMate d sq)
  have hd := purReindexingDerivedMates d sq
  exact ⟨ho.1, ht, hd.1, hd.2.1, ho.2, hd.2.2.1, hd.2.2.2⟩

/-- Scheme-isomorphism reindexing for completed coefficient modules, strict reduction
and the two canonical direct-image mates. There is no auxiliary base-linearity,
boundedness or constructibility assumption. The coefficient ring is the published
unlifted valuation ring O_E, and the ideal is its actual chosen uniformizer ideal.

Source: blueprint sec-six-functors/sk-thm-sf-package,
prop-pur-weil-equivariance-compatibilities.proof.md, constituent compatibility;
the extracted argument of lem-pur-weil-semilinear-exchange-reindexing, steps 9--11
(blueprint: lem-pur-isomorphism-completed-reduction-reindexing).

Proof:
1. Use the ordinary completed-module section reindexing and its reverse from
   purCompletedModuleReindexing. Whiskering gives the strict tower equivalence;
   Equivalence.mapDerivedCategory gives the two unbounded derived equivalences.
2. Use purReindexingLimitNormalization for the projection and K-injective unit
   equations. On TowerComplete K, compose the inverse comparison with the inverse
   pulled completion unit. Its augmentation equality identifies the inverse map
   with ordinaryToCompleted; cancellation gives the second normalization equation.
3. Use the existing completedReductionPullbackIso_existsUnique characterization,
   levelPullIso_tensor formula and completedReductionLevelPullbackIso_transition.
   These give the actual strict reduction comparison and every quotient transition.
4. The commutative square is Cartesian by IsPullback.of_horiz_isIso; take its
   projection-preserving isoPullback. Apply purReindexingOrdinaryMate for the
   ordinary section mate. Whiskering proves the ordinary tower mate invertible.
   purReindexingDerivedMates gives both derived mates and their unit equations.
-/
theorem purCompletedReductionReindexing (l : ℕ) [Fact l.Prime]
    (E : Type (t + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (∀ (T' T : Scheme.{t}) (u : T' ⟶ T) [IsIso u],
      (∀ x : T, IsUnit (l : T.presheaf.stalk x)) →
        PurCompletedReindexingAt (pbcPadicCoefficientDatum l E) u) ∧
    (∀ (X' X Y' Y : Scheme.{t}) (v : X' ⟶ X) (p' : X' ⟶ Y')
        (p : X ⟶ Y) (g : Y' ⟶ Y) [IsIso v] [IsIso g],
      (∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) →
      v ≫ p = p' ≫ g →
        ∃ sq : ChosenCartesianSquare v p' p g,
          PurCompletedReindexingSquare (pbcPadicCoefficientDatum l E) sq) := by
  constructor
  · intro T' T u _ _
    exact reindexingAt (pbcPadicCoefficientDatum l E) u
  · intro X' X Y' Y v p' p g _ _ _ w
    let h : IsPullback v p' p g := IsPullback.of_horiz_isIso ⟨w⟩
    let sq : ChosenCartesianSquare v p' p g :=
      { w := w
        isoPullback := h.isoPullback
        hom_fst := h.isoPullback_hom_fst
        hom_snd := h.isoPullback_hom_snd }
    exact ⟨sq, reindexingSquare (pbcPadicCoefficientDatum l E) sq⟩

end AlgebraicGeometry.Scheme
