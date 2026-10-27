/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor

/-! # Canonical tower reductions commute with shifts

Source: blueprint, sec-smooth-purity, tower-geometric gamma proof (1),
"a map of tower sheaves after removing the shift"; Stacks Project, Tag 05SU
(blueprint: lem-sp-tower-reduction-shift-compatibility).

Index n denotes positive level n+1. The scalar shift is fixed by the universal
cochain comparison, without a flatness, boundedness or constructibility condition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

/-- The coherent scalar shift determined by its universal cochain comparison.
Its counit normalization determines this choice uniquely, by the right Kan property.
Source: Stacks 05SU, counit-normalized scalar shifts
(blueprint: lem-sp-tower-reduction-shift-compatibility). -/
@[instance_reducible]
def spTowerScalarShift (D : SpCoefficientTowersAbelian l E T) {m n : ℕ} (h : m ≤ n) :
    (systemDerivedTensor.{t + 1, t, max u (t + 1)} D.scalar
      (spCoefficientCommRings l E T) h).CommShift ℤ :=
  letI := (D.scalar ((spCoefficientCommRings l E T).map (homOfLE h).op)).model.universal
  (Functor.rightKanExtension_coherentShift
    ((D.scalar ((spCoefficientCommRings l E T).map (homOfLE h).op)).model.E.mapHomologicalComplex
      (.up ℤ) ⋙ DerivedCategory.Q)
    DerivedCategory.Q
    (systemDerivedTensor.{t + 1, t, max u (t + 1)} D.scalar (spCoefficientCommRings l E T) h)
    (D.scalar ((spCoefficientCommRings l E T).map (homOfLE h).op)).model.ε
    (Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomologicalComplex.quasiIso _ (.up ℤ)))).choose

/-- The displayed shift square, on every object of the ordinary derived tower category.
The local instance bindings in this definition only install the dependency's existing
exactness and localization structures; the proposition has no additional hypothesis.
Source: blueprint tower-geometric gamma proof (1); Stacks 05SU
(blueprint: lem-sp-tower-reduction-shift-compatibility). -/
def SpTowerReductionShiftCompatibility (D : SpCoefficientTowersAbelian l E T) : Prop :=
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits
  letI := D.evaluationColimits
  ∀ (C : DerivedCategory (spCoefficientTowers l E T)) (r : ℤ) (m n : ℕ) (h : m ≤ n),
    (D.reduction h).app (C⟦r⟧) ≫
        ((spCoefficientEvaluation l E T D.equivalence m).mapDerivedCategory.commShiftIso r).hom.app
          C =
      (systemDerivedTensor.{t + 1, t, max u (t + 1)} D.scalar (spCoefficientCommRings l E T) h).map
          (((spCoefficientEvaluation l E T D.equivalence n).mapDerivedCategory.commShiftIso
            r).hom.app C) ≫
        (Functor.commShiftIso _ (self := spTowerScalarShift l E T D h) r).hom.app _ ≫
          ((D.reduction h).app C)⟦r⟧'

private theorem commShift_of_localization
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    (L : A ⥤ B) (W : MorphismProperty A) [L.IsLocalization W] [L.CommShift ℤ]
    {F G : B ⥤ C} [F.CommShift ℤ] [G.CommShift ℤ] (α : F ⟶ G)
    [NatTrans.CommShift (Functor.whiskerLeft L α) ℤ] : NatTrans.CommShift α ℤ := by
  constructor
  intro r
  apply Localization.natTrans_ext L W
  intro X
  have h := NatTrans.shift_app_comm (Functor.whiskerLeft L α) r X
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
    Category.assoc] at h
  rw [← α.naturality_assoc] at h
  exact (cancel_epi (F.map ((L.commShiftIso r).hom.app X))).mp h

private theorem termwiseReductionCommShift
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) (H : B ⥤ C) (G : A ⥤ C)
    [F.Additive] [H.Additive] [G.Additive] (α : F ⋙ H ⟶ G) :
    NatTrans.CommShift
      (show F.mapHomologicalComplex (.up ℤ) ⋙ H.mapHomologicalComplex (.up ℤ) ⟶
        G.mapHomologicalComplex (.up ℤ) from α.mapHomologicalComplex (.up ℤ)) ℤ := by
  constructor
  intro r
  ext K j
  simp only [Functor.commShiftIso_comp_hom_app, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    NatTrans.mapHomologicalComplex_app_f, CochainComplex.shiftFunctor_map_f',
    Category.comp_id]
  change (H.map (𝟙 (F.obj (K.X (j + r)))) ≫ 𝟙 _) ≫ α.app (K.X (j + r)) =
    α.app (K.X (j + r))
  exact (congrArg (fun z ↦ (z ≫ 𝟙 _) ≫ α.app (K.X (j + r)))
    (H.map_id (F.obj (K.X (j + r))))).trans
      ((congrArg (fun z ↦ z ≫ α.app (K.X (j + r))) (Category.id_comp (𝟙 _))).trans
        (Category.id_comp _))

private theorem representedReductionCommShift
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (H : B ⥤ C) (G : A ⥤ C)
    [F.Additive] [H.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (S : DerivedCategory B ⥤ DerivedCategory C) [S.CommShift ℤ]
    (ε : DerivedCategory.Q ⋙ S ⟶ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [NatTrans.CommShift ε ℤ] (α : F ⋙ H ⟶ G)
    (ρ : F.mapDerivedCategory ⋙ S ⟶ G.mapDerivedCategory)
    (hρ : ∀ K : CochainComplex A ℤ,
      ρ.app (DerivedCategory.Q.obj K) =
        S.map (F.mapDerivedCategoryFactors.hom.app K) ≫
          ε.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((α.mapHomologicalComplex (.up ℤ)).app K) ≫
          G.mapDerivedCategoryFactors.inv.app K) : NatTrans.CommShift ρ ℤ := by
  let q : F.mapHomologicalComplex (.up ℤ) ⋙ H.mapHomologicalComplex (.up ℤ) ⟶
      G.mapHomologicalComplex (.up ℤ) := α.mapHomologicalComplex (.up ℤ)
  have : NatTrans.CommShift q ℤ := termwiseReductionCommShift F H G α
  let β : DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ S) ⟶
      DerivedCategory.Q ⋙ G.mapDerivedCategory :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight F.mapDerivedCategoryFactors.hom S ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ)) ε ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight q DerivedCategory.Q ≫ G.mapDerivedCategoryFactors.inv
  have hβ : NatTrans.CommShift β ℤ := by
    dsimp only [β]
    infer_instance
  have heq : Functor.whiskerLeft DerivedCategory.Q ρ = β := by
    ext K
    simpa only [β, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp] using hρ K
  have : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Q ρ) ℤ := by
    rw [heq]
    exact hβ
  exact commShift_of_localization DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) ρ

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  SheafOfModules.systemRingHasDerived spCoefficientCommRings spCoefficientRings
  spCoefficientTowerSheafCondition

/-- Canonical reduction commutes with every integer shift.
Source: blueprint tower-geometric gamma proof (1); Stacks 05SU
(blueprint: lem-sp-tower-reduction-shift-compatibility).

Proof:
1. For a tower complex K, exact-evaluation factorization gives p_i. Linearize its
   actual semilinear transition to q_K. The normalized derived Hom comparison
   identifies reduction with F(p_n), followed by the universal scalar comparison,
   Q(q_K), and p_m inverse. This holds for every K, without K-flatness of K_n.
2. Linearization commutes with shifts: in degree j both maps send c tensor x to
   c times the transition of x in degree j+r. The two differentials have the same
   sign (-1)^r, also for negative r.
3. The counit-normalized scalar shift commutes with the universal comparison.
   The exact-evaluation factorization also commutes with shifts. Substitute the
   representative formula, use naturality of the scalar shift at p_n, and cancel
   p_m[r]. These are the scalar shifts of lem-pur-coefficient-scalar-shifts and
   the universal pairs of lem-pur-derived-change-of-rings.
4. Both sides are natural in the derived tower. Fully faithful precomposition
   with quasi-isomorphism localization descends the equality from complexes.
   The universal comparison is never inverted, so no flatness, boundedness or
   constructibility assumption is introduced. -/
theorem sp_tower_reduction_shift_compatibility (D : SpCoefficientTowersAbelian l E T) :
    SpTowerReductionShiftCompatibility l E T D := by
  let := D.hasDerived
  let := D.equivalenceAdditive
  let := D.evaluationLimits
  let := D.evaluationColimits
  intro C r m n h
  let F := spCoefficientEvaluation l E T D.equivalence n
  let G := spCoefficientEvaluation l E T D.equivalence m
  let S := systemDerivedTensor.{t + 1, t, max u (t + 1)} D.scalar
    (spCoefficientCommRings l E T) h
  let : S.CommShift ℤ := spTowerScalarShift l E T D h
  let ε := (D.scalar ((spCoefficientCommRings l E T).map (homOfLE h).op)).model.ε
  have hε : NatTrans.CommShift ε ℤ := by
    exact (Functor.rightKanExtension_coherentShift
      ((D.scalar ((spCoefficientCommRings l E T).map (homOfLE h).op)).model.E.mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q)
      DerivedCategory.Q S ε
      (by
        let := (D.scalar ((spCoefficientCommRings l E T).map (homOfLE h).op)).model.universal
        exact Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
          (HomologicalComplex.quasiIso _ (.up ℤ)))).choose_spec
  have : NatTrans.CommShift (D.reduction h) ℤ :=
    representedReductionCommShift F
      (D.scalar ((spCoefficientCommRings l E T).map (homOfLE h).op)).model.E G
      S ε (D.ordinaryReduction h) (D.reduction h) (D.reduction_rep h)
  simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
    (NatTrans.shift_app_comm (D.reduction h) r C).symm

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
