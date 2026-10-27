/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q85 and U2
-/
module

public import Sheaf.Paper.PurCompletedReindexingData
public import Sheaf.Paper.BoundedConstructibleComplete
import Sheaf.Paper.PurCompletedModuleReindexing
import Sheaf.Paper.PurReindexingLimitNormalization
import Sheaf.Paper.PurReindexingOrdinaryMate
import Sheaf.Paper.PurReindexingDerivedMates
import all Sheaf.Paper.CompletedDirectImageLimits
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Reindexing for the lifted integral coefficient presentation

Source: the constituent-compatibility argument of
prop-pur-weil-equivariance-compatibilities.proof.md, steps 9--11
(blueprint: lem-pur-completed-reindexing-lifted-coefficients).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
  proEtaleRingModulePullback proEtaleRingModuleDirectImage
  Functor.mapDerivedCategory Functor.rightDerivedFunctor HasDerivedCategory.standard
  CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 2000] reductionModulesHasDerivedCategory
  reductionTowerHasDerivedCategory

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

/-- The quotient-projection-normalized reindexing theorem in the size-lifted
coefficient presentation used by compact support.

Source: constituent compatibility, semilinear-exchange steps 9--11; the argument
of lem-pur-isomorphism-completed-reduction-reindexing for the lifted datum
(blueprint: lem-pur-completed-reindexing-lifted-coefficients).

Proof: specialize the coefficient-independent helpers reindexingAt and
reindexingSquare of PurCompletedReductionReindexing to pbcIntegralDatum l E. The helpers
above reuse their proofs through the public module, limit and mate declarations.
The first helper proves all section, exact-equivalence, limit-unit and strict
reduction clauses for any adic datum. The second proves the ordinary, tower and
derived mate normalizations for every supplied chosen Cartesian identification.
Neither helper uses the size of the coefficient presentation or the invertibility
of l on stalks; the stated unit hypotheses are therefore retained but unused. -/
theorem purCompletedReductionReindexingLifted (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (∀ (T' T : Scheme.{u}) (g : T' ⟶ T) [IsIso g],
      (∀ x : T, IsUnit (l : T.presheaf.stalk x)) →
        PurCompletedReindexingAt (pbcIntegralDatum l E) g) ∧
    (∀ (X' X Y' Y : Scheme.{u}) (v : X' ⟶ X) (p' : X' ⟶ Y')
        (p : X ⟶ Y) (g : Y' ⟶ Y) [IsIso v] [IsIso g],
      (∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) →
      ∀ sq : ChosenCartesianSquare v p' p g,
        PurCompletedReindexingSquare (pbcIntegralDatum l E) sq) := by
  constructor
  · intro T' T g _ _
    exact reindexingAt (pbcIntegralDatum l E) g
  · intro X' X Y' Y v p' p g _ _ _ sq
    exact reindexingSquare (pbcIntegralDatum l E) sq

end AlgebraicGeometry.Scheme
