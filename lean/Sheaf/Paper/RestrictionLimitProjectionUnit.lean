/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.PulledReductionComparisonData
import all Sheaf.CategoryTheory.DerivedExactSquareComposition
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction

/-! # Restriction of derived limits and constant units

Source: Stacks 06YY, 07A4, and 099N(5).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
private theorem normalized_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (α : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ R'.rightDerivedFunctor)
    (hα : ∀ P : CochainComplex B ℤ,
      G.mapDerivedCategory.map (_root_.chainDerivedUnit R P) ≫
          α.app (DerivedCategory.Q.obj P) ≫
          R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app P) =
        G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)).natTrans (.up ℤ)).app P) ≫
          _root_.chainDerivedUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj P)) :
    α = (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso s).hom)).natTrans := by
  apply _root_.derived_comp_ext R G
  intro P
  apply (cancel_mono (R'.rightDerivedFunctor.map
    (H.mapDerivedCategoryFactors.hom.app P))).mp
  simpa only [Functor.mapDerivedCategorySquareIso, Category.assoc] using
    (hα P).trans (_root_.derived_mate_factors adj adj' s P).symm

private theorem normalized_mate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (β : R ⋙ G ⟶ H ⋙ R')
    (hβ : (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)).natTrans = β)
    (α : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ R'.rightDerivedFunctor)
    (hα : ∀ P : CochainComplex B ℤ,
      G.mapDerivedCategory.map (_root_.chainDerivedUnit R P) ≫
          α.app (DerivedCategory.Q.obj P) ≫
          R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app P) =
        G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex β (.up ℤ)).app P) ≫
          _root_.chainDerivedUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj P)) :
    ∀ M : DerivedCategory A,
      G.mapDerivedCategory.map
          (adj.mapDerivedCategoryRightDerivedAdjunction.unit.app M) ≫
        α.app (L.mapDerivedCategory.obj M) =
      adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app (G.mapDerivedCategory.obj M) ≫
        R'.rightDerivedFunctor.map ((Functor.mapDerivedCategorySquareIso s).hom.app M) := by
  intro M
  have hn : α = (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso s).hom)).natTrans := by
    apply normalized_mate adj adj' s α
    intro P
    rw [hβ]
    exact hα P
  rw [hn]
  exact unit_mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso s).hom) M

private theorem derivedUnit_complex
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (P : CochainComplex C ℤ) :
    adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P) ≫
        R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
          ((L.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.inv.app P) := by
  have h : adj.mapDerivedCategoryRightDerivedAdjunction.unit.app
        (DerivedCategory.Q.obj P) ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ _).obj P)) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj P)) ≫
      R.rightDerivedFunctorUnit.app (((L.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P))) :=
    (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso _ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ _).obj P)
  apply (cancel_mono (R.rightDerivedFunctor.map
    (L.mapDerivedCategoryFactors.hom.app P))).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [R.rightDerivedFunctor.map_id, Category.comp_id]
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    _root_.quotient_hom_id, _root_.quotient_inv_id,
    _root_.homotopyFactors_inv_id] at h
  erw [L.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id] at h
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  have hu : (adj.mapHomologicalComplex (.up ℤ)).unit.app P =
      (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  change _ = DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫ _ at h
  rw [hu] at h
  erw [Category.comp_id] at h
  exact h

namespace AlgebraicGeometry.Scheme.PulledReduction
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private theorem lambda_normalized (T : Scheme.{t})
    (P : CochainComplex (d.towers T) ℤ) :
    (res d T).mapDerivedCategory.map
        (OrderedExchange.limitComplexUnit T (d.completedRing T) P) ≫
      (OrderedExchange.lambda d T).hom.app (DerivedCategory.Q.obj P) ≫
      (OrderedExchange.rlim (A := A) T).map
        ((tres d T).mapDerivedCategoryFactors.hom.app P) =
    (res d T).mapDerivedCategoryFactors.hom.app
        (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (OrderedExchange.ordinaryLambda d T) (.up ℤ)).hom.app
          P) ≫
      OrderedExchange.limitComplexUnit T (exchangeConstantRing T A)
        (((tres d T).mapHomologicalComplex (.up ℤ)).obj P) := by
  exact (OrderedExchange.lambda_existsUnique d T).exists.choose_spec P

attribute [local irreducible] OrderedExchange.lambda

private theorem projection_unit (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (J : CochainComplex (reductionTowerCategory T (reductionModuleRing T R)) ℤ)
    (n : ℕ) :
    (completedRlimUnit T R).app ((HomotopyCategory.quotient _ _).obj J) ≫
        (completedRlimProjection T R n).app (DerivedCategory.Q.obj J) =
      DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app J) ≫
        (reductionTowerEvaluation T (reductionModuleRing T R) n).mapDerivedCategoryFactors.inv.app
          J := by
  dsimp only [completedRlimUnit, completedRlimProjection, NatTrans.comp_app]
  rw [← Category.assoc]
  erw [Functor.rightDerivedNatTrans_app]
  rw [Category.assoc]
  have h := NatTrans.congr_app
    (Functor.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      (reductionTowerEvaluation T (reductionModuleRing T R) n))
    ((HomotopyCategory.quotient _ _).obj J)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  erw [h]
  simp only [Functor.mapDerivedCategoryFactorsh,
    Functor.mapHomologicalComplexUpToQuasiIsoFactorsh,
    NatTrans.mapHomotopyCategory, Functor.whiskerRight_app]
  simp
  rfl

private theorem complexProjection (T : Scheme.{t})
    (B : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (P : CochainComplex (exchangeTowers T B) ℤ) (n : ℕ) :
    OrderedExchange.limitComplexUnit T B P ≫
        (completedRlimProjection T B n).app (DerivedCategory.Q.obj P) ≫
        (reductionTowerEvaluation T (reductionModuleRing T B) n).mapDerivedCategoryFactors.hom.app
          P =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app P) := by
  simp only [OrderedExchange.limitComplexUnit, _root_.quotient_inv_id,
    _root_.quotient_hom_id, _root_.homotopyFactors_inv_id, Category.id_comp]
  erw [DerivedCategory.Qh.map_id, (completedRlim T B).map_id,
    Category.id_comp, Category.comp_id]
  change (completedRlimUnit T B).app ((HomotopyCategory.quotient _ _).obj P) ≫ _ ≫ _ = _
  rw [← Category.assoc, projection_unit]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem evaluationRes_computation (T : Scheme.{t})
    (P : CochainComplex (d.towers T) ℤ) (n : ℕ) :
    (evaluationRes d T n).hom.app (DerivedCategory.Q.obj P) ≫
        (res d T).mapDerivedCategory.map
          ((reductionTowerEvaluation T
            (reductionModuleRing T (d.completedRing T)) n).mapDerivedCategoryFactors.hom.app P) ≫
        (res d T).mapDerivedCategoryFactors.hom.app
          (((reductionTowerEvaluation T
            (reductionModuleRing T (d.completedRing T)) n).mapHomologicalComplex (.up ℤ)).obj P) =
      (reductionTowerDerivedEvaluation T
        (reductionModuleRing T (exchangeConstantRing T A)) n).map
          ((tres d T).mapDerivedCategoryFactors.hom.app P) ≫
        (reductionTowerEvaluation T
          (reductionModuleRing T (exchangeConstantRing T A)) n).mapDerivedCategoryFactors.hom.app
            (((tres d T).mapHomologicalComplex (.up ℤ)).obj P) := by
  have h := Functor.exactSquare_fac
    (R := tres d T)
    (G := reductionTowerEvaluation T (reductionModuleRing T (exchangeConstantRing T A)) n)
    (L := reductionTowerEvaluation T (reductionModuleRing T (d.completedRing T)) n)
    (S := res d T)
    (Iso.refl (tres d T ⋙ reductionTowerEvaluation T
      (reductionModuleRing T (exchangeConstantRing T A)) n)) P
  simp only [Iso.refl_hom, NatTrans.mapHomologicalComplex_id, NatTrans.id_app] at h
  erw [DerivedCategory.Q.map_id, Category.comp_id] at h
  exact h

private theorem ordinaryProjection (T : Scheme.{t})
    (P : CochainComplex (d.towers T) ℤ) (n : ℕ) :
    (NatIso.mapHomologicalComplex (OrderedExchange.ordinaryLambda d T) (.up ℤ)).hom.app P ≫
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
          (((tres d T).mapHomologicalComplex (.up ℤ)).obj P) =
      ((res d T).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app P) := by
  apply HomologicalComplex.hom_ext
  intro i
  exact (OrderedExchange.ordinaryLambda_existsUnique d T).exists.choose_spec (P.X i) n

set_option backward.isDefEq.respectTransparency false in
private theorem projectionOnComplex (T : Scheme.{t})
    (P : CochainComplex (d.towers T) ℤ) (n : ℕ) :
    (res d T).mapDerivedCategory.map
        (OrderedExchange.limitComplexUnit T (d.completedRing T) P) ≫
      ((OrderedExchange.lambda d T).hom.app (DerivedCategory.Q.obj P) ≫
        (completedRlimProjection T (exchangeConstantRing T A) n).app
          ((tres d T).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        (evaluationRes d T n).hom.app (DerivedCategory.Q.obj P)) =
    (res d T).mapDerivedCategory.map
        (OrderedExchange.limitComplexUnit T (d.completedRing T) P) ≫
      (res d T).mapDerivedCategory.map
        ((completedRlimProjection T (d.completedRing T) n).app
          (DerivedCategory.Q.obj P)) := by
  let evB := reductionTowerEvaluation T (reductionModuleRing T (d.completedRing T)) n
  let evR := reductionTowerEvaluation T (reductionModuleRing T (exchangeConstantRing T A)) n
  let TP := ((tres d T).mapHomologicalComplex (.up ℤ)).obj P
  apply (cancel_mono ((res d T).mapDerivedCategory.map
    (evB.mapDerivedCategoryFactors.hom.app P) ≫
      (res d T).mapDerivedCategoryFactors.hom.app
        ((evB.mapHomologicalComplex (.up ℤ)).obj P))).mp
  simp only [Category.assoc]
  rw [evaluationRes_computation]
  have hn := (completedRlimProjection T (exchangeConstantRing T A) n).naturality
    ((tres d T).mapDerivedCategoryFactors.hom.app P)
  rw [← reassoc_of% hn]
  slice_lhs 1 3 =>
    erw [lambda_normalized d T P]
  simp only [Category.assoc]
  rw [complexProjection]
  rw [← DerivedCategory.Q.map_comp, ordinaryProjection]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    complexProjection]
  exact ((res d T).mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app P)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem projectionNormalization (T : Scheme.{t})
    (Z : DerivedCategory (d.towers T)) (n : ℕ) :
    (OrderedExchange.lambda d T).hom.app Z ≫
        (completedRlimProjection T (exchangeConstantRing T A) n).app
          ((tres d T).mapDerivedCategory.obj Z) ≫
        (evaluationRes d T n).hom.app Z =
      (res d T).mapDerivedCategory.map
        ((completedRlimProjection T (d.completedRing T) n).app Z) := by
  let α := (OrderedExchange.lambda d T).hom ≫
    Functor.whiskerLeft (tres d T).mapDerivedCategory
      (completedRlimProjection T (exchangeConstantRing T A) n) ≫
    (evaluationRes d T n).hom
  let β := Functor.whiskerRight
    (completedRlimProjection T (d.completedRing T) n) (res d T).mapDerivedCategory
  have h (P : CochainComplex (d.towers T) ℤ) [P.IsKInjective] :
      α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P) := by
    have : IsIso (OrderedExchange.limitComplexUnit T (d.completedRing T) P) := by
      change IsIso (𝟙 _ ≫ _ ≫ _ ≫ _)
      infer_instance
    apply (cancel_epi ((res d T).mapDerivedCategory.map
      (OrderedExchange.limitComplexUnit T (d.completedRing T) P))).mp
    exact projectionOnComplex d T P n
  obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective Z
  have := hP
  change α.app Z = β.app Z
  apply (cancel_mono ((reductionTowerDerivedEvaluation T
    (reductionModuleRing T (d.completedRing T)) n ⋙ (res d T).mapDerivedCategory).map e.hom)).mp
  rw [← α.naturality, ← β.naturality, h P]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryLambda_mate (T : Scheme.{t}) :
    (mateEquiv
      (constLimAdj : d.constantTower T ⊣ completedTowerLimit T (d.completedRing T))
      (constLimAdj : (Functor.const ℕᵒᵖ : _ ⥤ exchangeTowers T
        (exchangeConstantRing T A)) ⊣ completedTowerLimit T (exchangeConstantRing T A))
      (TwoSquare.mk _ _ _ _ (OrderedExchange.ordinaryScalarDiagonal d T).inv)).natTrans =
        (OrderedExchange.ordinaryLambda d T).hom := by
  apply NatTrans.ext
  funext Z
  apply limit.hom_ext
  intro n
  obtain ⟨n⟩ := n
  erw [(OrderedExchange.ordinaryLambda_existsUnique d T).exists.choose_spec Z n]
  simp only [Functor.comp_obj, lim_obj, Functor.whiskeringRight_obj_obj,
    mateEquiv_apply, NatTrans.comp_app, Functor.id_obj, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, lim_map, Functor.comp_map, Functor.whiskeringRight_obj_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp, Category.assoc,
    limMap_π, Functor.const_obj_obj, limMap_π_assoc]
  erw [Category.id_comp]
  simp only [constLimAdj, Adjunction.mk'_unit, Adjunction.mk'_counit]
  erw [limit.lift_π_assoc]
  simp only [NatTrans.id_app]
  rfl

attribute [local irreducible] mateEquiv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantUnit_eq (T : Scheme.{t}) :
    completedConstantRlimUnit d T =
      (constLimAdj : d.constantTower T ⊣ completedTowerLimit T
          (d.completedRing T)).mapDerivedCategoryRightDerivedAdjunction.unit := by
  apply (completedConstantRlimUnit_exists d T).unique
    (completedConstantRlimUnit_exists d T).exists.choose_spec
  intro P
  exact derivedUnit_complex (d.constantTower T)
    (completedTowerLimit T (d.completedRing T)) constLimAdj P

/-- Restriction of derived strict limits respects their actual projections and the
constant-tower unit.

Source: Stacks 08BJ, 0940, and 0A07
(blueprint: lem-weil-pbc-restriction-limit-projection-unit).

Proof: on a K-injective tower the universal right-derived unit is invertible.
Compose the normalized equation in lambda_existsUnique with evaluation. The ordinary
comparison preserves every limit projection by ordinaryLambda_existsUnique, and the
right-derived projection is normalized by its universal unit. Exact evaluation and
restriction have the specified localization factors; their square is the identity
on ordinary evaluated modules. These equations give the first assertion on a
K-injective representative. Every derived tower has such a representative, so
naturality gives it for every tower. For the second assertion, the ordinary comparison
is the adjoint mate of the identity on constant diagrams: check this after each limit
projection. Derived adjoint mates satisfy the same universal-unit normalization as
lambda_existsUnique, hence give that comparison by uniqueness. The normalization in
completedConstantRlimUnit_exists identifies its unit with the derived constant-limit
adjunction unit. The adjoint-mate unit identity is exactly the second assertion. -/
theorem restrictionLimitNormalization (T : Scheme.{t}) :
    (∀ (Z : DerivedCategory (d.towers T)) (n : ℕ),
      (OrderedExchange.lambda d T).hom.app Z ≫
          (completedRlimProjection T (exchangeConstantRing T A) n).app
            ((tres d T).mapDerivedCategory.obj Z) ≫
          (evaluationRes d T n).hom.app Z =
        (res d T).mapDerivedCategory.map
          ((completedRlimProjection T (d.completedRing T) n).app Z)) ∧
    (∀ L : reductionDerivedCategory T (d.completedRing T),
      (res d T).mapDerivedCategory.map ((completedConstantRlimUnit d T).app L) ≫
          (OrderedExchange.lambda d T).hom.app ((completedDerivedConstant d T).obj L) =
        (OrderedExchange.diagonalAdjunction (A := A) T).unit.app
            ((res d T).mapDerivedCategory.obj L) ≫
          (OrderedExchange.rlim (A := A) T).map ((diagonalRes d T).hom.app L)) := by
  refine ⟨projectionNormalization d T, ?_⟩
  intro L
  have hs := Functor.square_symm_hom (OrderedExchange.ordinaryScalarDiagonal d T)
  change (Functor.mapDerivedCategorySquareIso
    (OrderedExchange.ordinaryScalarDiagonal d T).symm).hom =
      (diagonalRes d T).hom at hs
  rw [constantUnit_eq, ← hs]
  change (OrderedExchange.res d T).map
      ((constLimAdj : d.constantTower T ⊣ completedTowerLimit T
        (d.completedRing T)).mapDerivedCategoryRightDerivedAdjunction.unit.app L) ≫
      (OrderedExchange.lambda d T).hom.app ((d.derivedConstantTower T).obj L) = _
  apply normalized_mate_unit
    (G := reductionRestrict T (exchangeScalar d T))
    (H := exchangeTowerModuleRes d T)
    (constLimAdj : d.constantTower T ⊣ completedTowerLimit T (d.completedRing T))
    (constLimAdj : (Functor.const ℕᵒᵖ : _ ⥤ exchangeTowers T
      (exchangeConstantRing T A)) ⊣ completedTowerLimit T (exchangeConstantRing T A))
    (OrderedExchange.ordinaryScalarDiagonal d T).symm
    (OrderedExchange.ordinaryLambda d T).hom
    (ordinaryLambda_mate d T)
    (OrderedExchange.lambda d T).hom
  intro P
  have hunit (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
      (P : CochainComplex (exchangeTowers T R) ℤ) :
      OrderedExchange.limitComplexUnit T R P =
        _root_.chainDerivedUnit (completedTowerLimit T R) P := by
    simp only [OrderedExchange.limitComplexUnit, _root_.chainDerivedUnit,
      _root_.homotopyFactors_inv_id]
    erw [DerivedCategory.Qh.map_id, Category.id_comp]
    rfl
  have hLambda := lambda_normalized d T P
  rw [hunit, hunit] at hLambda
  exact hLambda


end AlgebraicGeometry.Scheme.PulledReduction
