/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Sheaf.Algebra.Homology.RingedTensorCohomologicalBounds
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.CompletedConstantSheafReduction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Levelwise truncations of an adic reduction tower

Source: blueprint sec-smooth-base-change/sk-rem-rest, order 1429;
Stacks Tags 0118, 08J5, 09C1, 09C7, 099M, 099N and 09C2
(blueprint: prop-weil-pbc-levelwise-truncations).

The strict tower and its quotient-linear levels remain distinct. Standard truncations
are Mathlib's canonical functors. The output data retain both exact evaluation comparisons
and the normalization of the entire truncation triangle. Higher Tor vanishing is required
only for normalization, never for the unconditional strict-tower cohomology formulas.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

-- Select the generic standard localizations before trying specialized coefficient instances.
attribute [local instance 2000] reductionRingModulesHasDerivedCategory
attribute [local instance 2000] pbcTowers_hasDerivedCategory

-- Keep the universal scalar-extension witnesses behind their functor/adjunction API.
attribute [local irreducible] completedAdicDerivedChange pbcDerivedScalarAdjunction

/-- Exact scalar restriction inherits the existing termwise derived shift comparison.
Source: Stacks Tag 03DA, blueprint order 1429
(blueprint: prop-weil-pbc-levelwise-truncations). -/
instance pbcLevelwiseRestrictionCommShift
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    (pbcDerivedRestrict φ).CommShift ℤ :=
  inferInstanceAs ((pbcRestrict φ).mapDerivedCategory.CommShift ℤ)

/-- The scalar-extension shift comparison is the canonical mate of exact restriction's
specified shift comparison under the tensor-unit normalized adjunction.
Source: Stacks Tag 06YY, blueprint order 1429
(blueprint: prop-weil-pbc-levelwise-truncations). -/
instance pbcLevelwiseScalarCommShift
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    (pbcDerivedExtend φ).CommShift ℤ :=
  (pbcDerivedScalarAdjunction φ).leftAdjointCommShift ℤ

/-- The higher-Tor condition at precisely the degrees above the cutoff. The module
H^q(M_(n+1)) is placed in degree zero before scalar extension; positive p means degree -p.
Source: blueprint order 1429, (TC); Stacks Tag 06YU
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def PbcLevelwiseTorVanishing (M : AdicTower T d) (m : ℤ) : Prop :=
  ∀ (n : ℕ) (q : ℤ), m + 1 ≤ q → ∀ p : ℕ, 0 < p →
    IsZero ((DerivedCategory.homologyFunctor _ (-(p : ℤ))).obj
      ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj (M.level (n + 1))))))

/-- Both adic truncations, retaining the actual strict tower, canonical quotient-linear
levels, and their canonical exact evaluation comparisons. These equalities specify
objects, not additional hypotheses on the input.
Source: blueprint order 1429, (1) and (3); Stacks Tags 0118 and 08J5
(blueprint: prop-weil-pbc-levelwise-truncations). -/
structure PbcLevelwiseTruncationData (M : AdicTower T d) (m : ℤ) where
  /-- The lower normalized tower, with its transitions and full quotient cocycle. -/
  lower : AdicTower T d
  /-- The upper normalized tower, with its transitions and full quotient cocycle. -/
  upper : AdicTower T d
  /-- The underlying strict tower is its canonical lower truncation. -/
  lowerTower : lower.tower = (DerivedCategory.TStructure.t.truncLE m).obj M.tower
  /-- The underlying strict tower is its canonical upper truncation. -/
  upperTower : upper.tower = (DerivedCategory.TStructure.t.truncGE (m + 1)).obj M.tower
  /-- The quotient-linear lower levels are the canonical truncations. -/
  lowerLevel : ∀ n : ℕ,
    lower.level n = (DerivedCategory.TStructure.t.truncLE m).obj (M.level n)
  /-- The quotient-linear upper levels are the canonical truncations. -/
  upperLevel : ∀ n : ℕ,
    upper.level n = (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level n)
  /-- Evaluation uses the specified exact-functor and original evaluation comparisons. -/
  lowerEvaluation : ∀ n : ℕ,
    lower.evaluation n ≪≫ (pbcTowerEvaluation T (pbcAdicCompletion T d) n).mapIso
        (eqToIso lowerTower) =
      (pbcDerivedRestrict (pbcAdicProjection T d n)).mapIso (eqToIso (lowerLevel n)) ≪≫
        ((pbcRestrict (pbcAdicProjection T d n)).mapDerivedCategoryTruncLEIso m).app
          (M.level n) ≪≫
        (DerivedCategory.TStructure.t.truncLE m).mapIso (M.evaluation n) ≪≫
        (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj
          (op n)).mapDerivedCategoryTruncLEIso m).symm.app M.tower
  /-- The same canonical evaluation normalization for the upper levels. -/
  upperEvaluation : ∀ n : ℕ,
    upper.evaluation n ≪≫ (pbcTowerEvaluation T (pbcAdicCompletion T d) n).mapIso
        (eqToIso upperTower) =
      (pbcDerivedRestrict (pbcAdicProjection T d n)).mapIso (eqToIso (upperLevel n)) ≪≫
        ((pbcRestrict (pbcAdicProjection T d n)).mapDerivedCategoryTruncGEIso (m + 1)).app
          (M.level n) ≪≫
        (DerivedCategory.TStructure.t.truncGE (m + 1)).mapIso (M.evaluation n) ≪≫
        (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj
          (op n)).mapDerivedCategoryTruncGEIso (m + 1)).symm.app M.tower

variable {T d}

/-- Lower normalization expressed at the canonical truncation objects.
Source: blueprint order 1429, (1) (blueprint: prop-weil-pbc-levelwise-truncations). -/
def PbcLevelwiseTruncationData.lowerNormalization {M : AdicTower T d} {m : ℤ}
    (N : PbcLevelwiseTruncationData T d M m) (b a : ℕ) (hab : a ≤ b) :
    (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).obj
        ((DerivedCategory.TStructure.t.truncLE m).obj (M.level b)) ≅
      (DerivedCategory.TStructure.t.truncLE m).obj (M.level a) :=
  (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).mapIso
      (eqToIso (N.lowerLevel b)).symm ≪≫
    N.lower.normalization b a hab ≪≫ eqToIso (N.lowerLevel a)

/-- Upper normalization expressed at the canonical truncation objects.
Source: blueprint order 1429, (1) (blueprint: prop-weil-pbc-levelwise-truncations). -/
def PbcLevelwiseTruncationData.upperNormalization {M : AdicTower T d} {m : ℤ}
    (N : PbcLevelwiseTruncationData T d M m) (b a : ℕ) (hab : a ≤ b) :
    (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level b)) ≅
      (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level a) :=
  (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).mapIso
      (eqToIso (N.upperLevel b)).symm ≪≫
    N.upper.normalization b a hab ≪≫ eqToIso (N.upperLevel a)

variable (T d)

/-- The end normalizations identify the entire reduced truncation triangle, including
its connecting arrow, with the canonical triangle at the lower level. Uniqueness with
the given middle normalization specifies the canonical comparison, also for equal levels.
Source: blueprint order 1429, (1); Stacks Tag 08J5; BBD 1.1.9 and 1.1.10(ii)
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def PbcIsLevelwiseTruncation {M : AdicTower T d} {m : ℤ}
    (N : PbcLevelwiseTruncationData T d M m) : Prop :=
  ∀ (b a : ℕ) (hab : a ≤ b),
    ∃! e : (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).mapTriangle.obj
          ((DerivedCategory.TStructure.t.triangleLEGE m (m + 1) rfl).obj (M.level b)) ≅
        (DerivedCategory.TStructure.t.triangleLEGE m (m + 1) rfl).obj (M.level a),
      e.hom.hom₁ = (N.lowerNormalization b a hab).hom ∧
      e.hom.hom₂ = (M.normalization b a hab).hom ∧
      e.hom.hom₃ = (N.upperNormalization b a hab).hom

/-- Under (TC), both canonical levelwise truncations are normalized adic towers.
Their stored tower/level/evaluation data and unique triangle comparisons retain all
strict transition equations, natural cohomology identifications and quotient cocycles.
Source: blueprint order 1429, (1) and (3)
(blueprint: prop-weil-pbc-levelwise-truncations).

Proof: compute good truncations in the levelwise abelian tower category
(lem-weil-tower-category-levelwise-abelian). Tensor the truncation triangle by the next
quotient. The upper bound follows from ringedTensorCohomologicalBounds(a); (TC) gives
the lower bound of its upper end by part (b). Orthogonality and
lem-weil-pbc-triangle-morphism-extension give the unique triangle comparison with the
specified middle normalization. Applying this successively gives every quotient pair.
Uniqueness gives its naturality and cocycle. The scalar-extension unit is x↦x⊗1 on
K-flat representatives, hence a map of triangles. After exact scalar restriction, the
same uniqueness identifies its end maps with the truncated strict transitions. This
also identifies the cohomology maps with those of the normalized triangles. -/
theorem pbc_adic_levelwise_truncations (M : AdicTower T d) (m : ℤ)
    (_hTor : PbcLevelwiseTorVanishing T d M m) :
    ∃ N : PbcLevelwiseTruncationData T d M m, PbcIsLevelwiseTruncation T d N := by
  sorry

/-- The lower-truncated strict semilinear transition, without (TC). Exact scalar
restriction supplies the canonical coefficient-linear truncation comparison.
Source: blueprint order 1429, (3) (blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcTruncatedTransitionLE (M : AdicTower T d) (m : ℤ) (b a : ℕ) (hab : a ≤ b) :
    (DerivedCategory.TStructure.t.truncLE m).obj (M.level b) ⟶
      (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).obj
        ((DerivedCategory.TStructure.t.truncLE m).obj (M.level a)) :=
  (DerivedCategory.TStructure.t.truncLE m).map
      (adicTowerSemilinearTransition T d M.level M.normalization b a hab) ≫
    ((pbcRestrict (pbcAdicQuotient T d b a hab)).mapDerivedCategoryTruncLEIso m).inv.app
      (M.level a)

/-- The upper-truncated strict semilinear transition, without (TC).
Source: blueprint order 1429, (3) (blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcTruncatedTransitionGE (M : AdicTower T d) (m : ℤ) (b a : ℕ) (hab : a ≤ b) :
    (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level b) ⟶
      (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level a)) :=
  (DerivedCategory.TStructure.t.truncGE (m + 1)).map
      (adicTowerSemilinearTransition T d M.level M.normalization b a hab) ≫
    ((pbcRestrict (pbcAdicQuotient T d b a hab)).mapDerivedCategoryTruncGEIso (m + 1)).inv.app
      (M.level a)

set_option backward.isDefEq.respectTransparency false in
private lemma truncLE_restriction_counit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C) (m : ℤ) :
    (F.mapDerivedCategoryTruncLEIso m).inv.app X ≫
        F.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncLEι m).app X) =
      (DerivedCategory.TStructure.t.truncLEι m).app (F.mapDerivedCategory.obj X) := by
  have := F.isLE_mapDerivedCategory_obj
    ((DerivedCategory.TStructure.t.truncLE m).obj X) m
  apply (cancel_epi ((F.mapDerivedCategoryTruncLEIso m).hom.app X)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  exact (DerivedCategory.TStructure.t.liftTruncLE_ι _ m).symm

private lemma truncLE_comparison_counit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C) (m : ℤ) :
    (F.mapDerivedCategoryTruncLEIso m).hom.app X ≫
        (DerivedCategory.TStructure.t.truncLEι m).app (F.mapDerivedCategory.obj X) =
      F.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncLEι m).app X) := by
  apply (cancel_epi ((F.mapDerivedCategoryTruncLEIso m).inv.app X)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  exact (truncLE_restriction_counit F X m).symm

set_option backward.isDefEq.respectTransparency false in
private lemma truncGE_restriction_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C) (m : ℤ) :
    (DerivedCategory.TStructure.t.truncGEπ m).app (F.mapDerivedCategory.obj X) ≫
        (F.mapDerivedCategoryTruncGEIso m).inv.app X =
      F.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncGEπ m).app X) := by
  have : DerivedCategory.TStructure.t.IsGE
      ((DerivedCategory.TStructure.t.truncGE m ⋙ F.mapDerivedCategory).obj X) m :=
    F.isGE_mapDerivedCategory_obj ((DerivedCategory.TStructure.t.truncGE m).obj X) m
  exact DerivedCategory.TStructure.t.π_descTruncGE _ m

set_option backward.isDefEq.respectTransparency false in
/-- Unconditional cohomology at the quotient-linear levels, and its naturality for
the strict transitions. The maps are H of the canonical truncation counit and unit;
their squares with all semilinear transitions commute before taking cohomology.
Source: blueprint order 1429, (3); Stacks Tag 0118
(blueprint: prop-weil-pbc-levelwise-truncations).
Proof: kernels and cokernels in the strict tower category are levelwise. Good truncation
therefore evaluates to good truncation at each level. Its cohomology formulas make
the indicated canonical maps invertible in the surviving range and give zero otherwise.
Functoriality of truncation and exact restriction prove both transition squares.
The formulas also show preservation of levelwise quasi-isomorphisms, so these are
statements in the derived category, not just in chosen complexes. -/
theorem pbc_levelwise_truncation_cohomology (M : AdicTower T d) (m : ℤ) :
    (∀ (n : ℕ) (i : ℤ), i ≤ m →
      IsIso ((DerivedCategory.homologyFunctor _ i).map
        ((DerivedCategory.TStructure.t.truncLEι m).app (M.level n)))) ∧
    (∀ (n : ℕ) (i : ℤ), m < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((DerivedCategory.TStructure.t.truncLE m).obj (M.level n)))) ∧
    (∀ (n : ℕ) (i : ℤ), m + 1 ≤ i →
      IsIso ((DerivedCategory.homologyFunctor _ i).map
        ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level n)))) ∧
    (∀ (n : ℕ) (i : ℤ), i ≤ m →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level n)))) ∧
    ∀ (b a : ℕ) (hab : a ≤ b),
      (DerivedCategory.TStructure.t.truncLEι m).app (M.level b) ≫
          adicTowerSemilinearTransition T d M.level M.normalization b a hab =
        pbcTruncatedTransitionLE T d M m b a hab ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map
            ((DerivedCategory.TStructure.t.truncLEι m).app (M.level a)) ∧
      adicTowerSemilinearTransition T d M.level M.normalization b a hab ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map
            ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level a)) =
        (DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level b) ≫
          pbcTruncatedTransitionGE T d M m b a hab := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n i hi
    exact DerivedCategory.isIso_homologyFunctor_map_truncLTι_app
      (M.level n) (m + 1) i (by omega)
  · intro n i hi
    exact DerivedCategory.isZero_of_isLE _ m i hi
  · intro n i hi
    exact DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app (M.level n) _ i hi
  · intro n i hi
    exact DerivedCategory.isZero_of_isGE _ (m + 1) i (by omega)
  · intro b a hab
    constructor
    · dsimp only [pbcTruncatedTransitionLE, pbcDerivedRestrict]
      rw [Category.assoc, truncLE_restriction_counit]
      exact ((DerivedCategory.TStructure.t.truncLEι m).naturality _).symm
    · dsimp only [pbcTruncatedTransitionGE, pbcDerivedRestrict]
      rw [← Category.assoc, ← NatTrans.naturality]
      simp only [Functor.id_map, Category.assoc]
      rw [truncGE_restriction_unit]

private lemma scalar_unit_transport
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {X X' : C} {Y Y' : D}
    (u : X ⟶ X') (f : F.obj X' ⟶ Y) (v : Y ⟶ Y') :
    adj.unit.app X ≫ G.map (F.map u ≫ f ≫ v) =
      u ≫ adj.unit.app X' ≫ G.map f ≫ G.map v := by
  have h := adj.unit.naturality_assoc u (G.map f ≫ G.map v)
  simpa only [Functor.id_map, Functor.comp_map, Functor.map_comp, Category.assoc] using h.symm

set_option backward.isDefEq.respectTransparency false in
/-- Under normalization, the strict transitions are exactly the adjuncts of the new
normalizations; thus the preceding cohomology identifications are also those of the
normalized truncation triangles. The AdicTower fields retain their full quotient cocycle.
Source: blueprint order 1429, (1) and (3)
(blueprint: prop-weil-pbc-levelwise-truncations).
Proof: on K-flat representatives the scalar-extension unit is x↦x⊗1 and respects
mapping cones and shifts, hence maps truncation triangles after exact restriction.
Compose with the uniquely normalized triangle comparison. Orthogonality and the
triangle-extension uniqueness identify its end maps with functorial truncation of
the original strict transition. Transport by the stored level equalities. -/
theorem pbc_levelwise_truncation_transitions {M : AdicTower T d} {m : ℤ}
    (N : PbcLevelwiseTruncationData T d M m) (_hN : PbcIsLevelwiseTruncation T d N)
    (b a : ℕ) (hab : a ≤ b) :
    eqToHom (N.lowerLevel b).symm ≫
        adicTowerSemilinearTransition T d N.lower.level N.lower.normalization b a hab ≫
        (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map
          (eqToHom (N.lowerLevel a)) = pbcTruncatedTransitionLE T d M m b a hab ∧
    eqToHom (N.upperLevel b).symm ≫
        adicTowerSemilinearTransition T d N.upper.level N.upper.normalization b a hab ≫
        (pbcDerivedRestrict (pbcAdicQuotient T d b a hab)).map
          (eqToHom (N.upperLevel a)) = pbcTruncatedTransitionGE T d M m b a hab := by
  obtain ⟨e, he, _⟩ := _hN b a hab
  let φ := pbcAdicQuotient T d b a hab
  let F := pbcDerivedExtend φ
  let G := pbcDerivedRestrict φ
  let adj := pbcDerivedScalarAdjunction φ
  have hLE : F.map ((DerivedCategory.TStructure.t.truncLEι m).app (M.level b)) ≫
      (M.normalization b a hab).hom =
      (N.lowerNormalization b a hab).hom ≫
        (DerivedCategory.TStructure.t.truncLEι m).app (M.level a) := by
    simpa only [Functor.mapTriangle_obj,
      CategoryTheory.Triangulated.TStructure.triangleLEGE_obj_mor₁, he.1, he.2.1]
      using! e.hom.comm₁
  have hGE : F.map ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level b)) ≫
      (N.upperNormalization b a hab).hom =
      (M.normalization b a hab).hom ≫
        (DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level a) := by
    simpa only [Functor.mapTriangle_obj,
      CategoryTheory.Triangulated.TStructure.triangleLEGE_obj_mor₂, he.2.1, he.2.2]
      using! e.hom.comm₂
  constructor
  · have h : adj.unit.app ((DerivedCategory.TStructure.t.truncLE m).obj (M.level b)) ≫
        G.map (N.lowerNormalization b a hab).hom =
        pbcTruncatedTransitionLE T d M m b a hab := by
      apply (cancel_mono
        (((pbcRestrict φ).mapDerivedCategoryTruncLEIso m).hom.app (M.level a))).mp
      have : DerivedCategory.TStructure.t.IsLE
          ((𝟭 (DerivedCategory _)).obj
            ((DerivedCategory.TStructure.t.truncLE m).obj (M.level b))) m := by
        dsimp
        infer_instance
      apply DerivedCategory.TStructure.t.to_truncLE_obj_ext
      have hcmp : ((pbcRestrict φ).mapDerivedCategoryTruncLEIso m).hom.app
            (M.level a) ≫
          (DerivedCategory.TStructure.t.truncLEι m).app (G.obj (M.level a)) =
          G.map ((DerivedCategory.TStructure.t.truncLEι m).app (M.level a)) := by
        apply (cancel_epi
          (((pbcRestrict φ).mapDerivedCategoryTruncLEIso m).inv.app (M.level a))).mp
        simp only [Iso.inv_hom_id_app_assoc]
        exact (truncLE_restriction_counit (pbcRestrict φ) (M.level a) m).symm
      simp only [pbcTruncatedTransitionLE, φ, Category.assoc,
        Iso.inv_hom_id_app_assoc]
      erw [hcmp, ← G.map_comp, ← hLE, G.map_comp]
      have hn := adj.unit.naturality
        ((DerivedCategory.TStructure.t.truncLEι m).app (M.level b))
      dsimp only [Functor.id_map, Functor.comp_map] at hn
      erw [← Category.assoc, ← hn]
      simpa only [Functor.id_map, adicTowerSemilinearTransition, adj, G,
        Category.assoc] using!
        ((DerivedCategory.TStructure.t.truncLEι m).naturality
          (adicTowerSemilinearTransition T d M.level M.normalization b a hab)).symm
    simpa only [adicTowerSemilinearTransition,
      PbcLevelwiseTruncationData.lowerNormalization, φ, F, G, adj,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, eqToIso.hom, eqToIso.inv,
      scalar_unit_transport, Category.assoc] using h
  · have h : adj.unit.app
          ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level b)) ≫
        G.map (N.upperNormalization b a hab).hom =
        pbcTruncatedTransitionGE T d M m b a hab := by
      have : DerivedCategory.TStructure.t.IsGE
          (G.obj ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M.level a)))
          (m + 1) :=
        (pbcRestrict φ).isGE_mapDerivedCategory_obj _ _
      apply DerivedCategory.TStructure.t.from_truncGE_obj_ext
      simp only [pbcTruncatedTransitionGE]
      have hn := adj.unit.naturality
        ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (M.level b))
      dsimp only [Functor.id_map, Functor.comp_map] at hn
      erw [← Category.assoc, hn]
      simp only [Category.assoc]
      erw [← G.map_comp, hGE, G.map_comp]
      erw [← NatTrans.naturality_assoc]
      simp only [Functor.id_map]
      erw [truncGE_restriction_unit]
      simp only [adicTowerSemilinearTransition, adj, G, Category.assoc, Functor.id_obj]
      rfl
    simpa only [adicTowerSemilinearTransition,
      PbcLevelwiseTruncationData.upperNormalization, φ, F, G, adj,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, eqToIso.hom, eqToIso.inv,
      scalar_unit_transport, Category.assoc] using h


set_option backward.isDefEq.respectTransparency false in
/-- Naturality of both canonical normalizations for maps of the input reduction towers.
Source: blueprint order 1429, (1)
(blueprint: prop-weil-pbc-levelwise-truncations).
Proof: apply functorial truncation and scalar extension to the level maps. The two
composites are triangle maps with the same middle component by the input square.
Triangle-extension uniqueness equates their end components. -/
theorem pbc_levelwise_truncation_naturality {M M' : AdicTower T d} {m : ℤ}
    (N : PbcLevelwiseTruncationData T d M m) (N' : PbcLevelwiseTruncationData T d M' m)
    (_hN : PbcIsLevelwiseTruncation T d N) (_hN' : PbcIsLevelwiseTruncation T d N')
    (f : ∀ n : ℕ, M.level n ⟶ M'.level n)
    (_hf : ∀ (b a : ℕ) (hab : a ≤ b),
      (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).map (f b) ≫
          (M'.normalization b a hab).hom = (M.normalization b a hab).hom ≫ f a)
    (b a : ℕ) (hab : a ≤ b) :
    (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).map
        ((DerivedCategory.TStructure.t.truncLE m).map (f b)) ≫
          (N'.lowerNormalization b a hab).hom =
      (N.lowerNormalization b a hab).hom ≫ (DerivedCategory.TStructure.t.truncLE m).map (f a) ∧
    (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).map
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).map (f b)) ≫
          (N'.upperNormalization b a hab).hom =
      (N.upperNormalization b a hab).hom ≫
        (DerivedCategory.TStructure.t.truncGE (m + 1)).map (f a) := by
  obtain ⟨e, he, _⟩ := _hN b a hab
  obtain ⟨e', he', _⟩ := _hN' b a hab
  let F := pbcDerivedExtend (pbcAdicQuotient T d b a hab)
  let Δb := (DerivedCategory.TStructure.t
    (C := pbcModules T ((pbcAdicRings T d).obj (op b)))).triangleLEGE m (m + 1) rfl
  let Δa := (DerivedCategory.TStructure.t
    (C := pbcModules T ((pbcAdicRings T d).obj (op a)))).triangleLEGE m (m + 1) rfl
  let τ₁ := F.mapTriangle.map (Δb.map (f b)) ≫ e'.hom
  let τ₂ := e.hom ≫ Δa.map (f a)
  have hLE : DerivedCategory.TStructure.t.IsLE (F.mapTriangle.obj (Δb.obj (M.level b))).obj₁
      m := DerivedCategory.TStructure.t.isLE_of_iso (N.lowerNormalization b a hab).symm m
  have hdist : F.mapTriangle.obj (Δb.obj (M.level b)) ∈ distTriang _ :=
    CategoryTheory.Pretriangulated.isomorphic_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished m (m + 1) rfl (M.level a))
      _ e
  have hmid : τ₁.hom₂ = τ₂.hom₂ := by
    change F.map (f b) ≫ e'.hom.hom₂ = e.hom.hom₂ ≫ f a
    rw [he.2.1, he'.2.1]
    exact _hf b a hab
  have hτ : τ₁ = τ₂ := by
    exact DerivedCategory.TStructure.t.triangle_map_ext hdist
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished m (m + 1) rfl (M'.level a))
      m (m + 1) hLE (by
        change DerivedCategory.TStructure.t.IsGE
          ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (M'.level a)) (m + 1)
        infer_instance) hmid (by omega)
  constructor
  · have h := congrArg (fun τ ↦ τ.hom₁) hτ
    change F.map ((DerivedCategory.TStructure.t.truncLE m).map (f b)) ≫ e'.hom.hom₁ =
      e.hom.hom₁ ≫ (DerivedCategory.TStructure.t.truncLE m).map (f a) at h
    simpa only [he.1, he'.1] using h
  · have h := congrArg (fun τ ↦ τ.hom₃) hτ
    change F.map ((DerivedCategory.TStructure.t.truncGE (m + 1)).map (f b)) ≫
      e'.hom.hom₃ = e.hom.hom₃ ≫
        (DerivedCategory.TStructure.t.truncGE (m + 1)).map (f a) at h
    simpa only [he.2.2, he'.2.2] using h

/-- Canonical cohomology of a strict-tower truncation evaluated at any level, without
(TC). These are precisely H of evaluation of its counit and unit, hence are natural
transformations both in strict tower maps and in the level index.
Source: blueprint order 1429, (3); Stacks Tag 0118
(blueprint: prop-weil-pbc-levelwise-truncations).
Proof: exact evaluation commutes with good truncations by its canonical truncation
isomorphisms. Apply their cohomology formulas; naturality of evaluation and of the
truncation counit/unit gives compatibility with every strict transition. -/
theorem pbc_strict_tower_truncation_cohomology
    (V : DerivedCategory (pbcTowers T (pbcAdicCompletion T d))) (m : ℤ) :
    (∀ (n : ℕ) (i : ℤ), i ≤ m → IsIso ((DerivedCategory.homologyFunctor _ i).map
      ((pbcTowerEvaluation T (pbcAdicCompletion T d) n).map
        ((DerivedCategory.TStructure.t.truncLEι m).app V)))) ∧
    (∀ (n : ℕ) (i : ℤ), m < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((pbcTowerEvaluation T (pbcAdicCompletion T d) n).obj
        ((DerivedCategory.TStructure.t.truncLE m).obj V)))) ∧
    (∀ (n : ℕ) (i : ℤ), m + 1 ≤ i → IsIso ((DerivedCategory.homologyFunctor _ i).map
      ((pbcTowerEvaluation T (pbcAdicCompletion T d) n).map
        ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app V)))) ∧
    (∀ (n : ℕ) (i : ℤ), i ≤ m → IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((pbcTowerEvaluation T (pbcAdicCompletion T d) n).obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj V)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n i hi
    let F := (CategoryTheory.evaluation ℕᵒᵖ
      (pbcModules T (pbcAdicCompletion T d))).obj (op n)
    have : IsIso ((DerivedCategory.homologyFunctor _ i).map
        ((DerivedCategory.TStructure.t.truncLEι m).app V)) :=
      DerivedCategory.isIso_homologyFunctor_map_truncLTι_app V (m + 1) i (by omega)
    exact (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso i) _).mp
      (by dsimp; infer_instance)
  · intro n i hi
    let F := (CategoryTheory.evaluation ℕᵒᵖ
      (pbcModules T (pbcAdicCompletion T d))).obj (op n)
    have := F.isLE_mapDerivedCategory_obj
      ((DerivedCategory.TStructure.t.truncLE m).obj V) m
    exact DerivedCategory.isZero_of_isLE _ m i hi
  · intro n i hi
    let F := (CategoryTheory.evaluation ℕᵒᵖ
      (pbcModules T (pbcAdicCompletion T d))).obj (op n)
    have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app V (m + 1) i hi
    exact (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso i) _).mp
      (by dsimp; infer_instance)
  · intro n i hi
    let F := (CategoryTheory.evaluation ℕᵒᵖ
      (pbcModules T (pbcAdicCompletion T d))).obj (op n)
    have := F.isGE_mapDerivedCategory_obj
      ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj V) (m + 1)
    exact DerivedCategory.isZero_of_isGE _ (m + 1) i (by omega)

/-- The fixed K-flat evaluation comparison for the reduction of one completed object.
Source: blueprint order 1429, opening paragraph; Stacks Tag 06YY
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcReductionEvaluationIso (K : PbcCompletedDerived T d) (n : ℕ) :
    (pbcDerivedRestrict (pbcAdicProjection T d n)).obj
        ((pbcCompletedReduction T d n).obj K) ≅
      (pbcTowerEvaluation T (pbcAdicCompletion T d) n).obj
        ((completedReductionTower T d).obj K) :=
  (asIso (completedReductionEvaluation T d n)).symm.app K

/-- The canonical reduction tower satisfies the strict-transition equation and full
quotient cocycle, before any truncation or Tor hypothesis.
Source: blueprint order 1429, opening paragraph; Stacks Tag 06YY
(blueprint: prop-weil-pbc-levelwise-truncations).
Proof: use one K-flat representative for K. The ordinary reduction tower, balancing
maps and evaluations from def-weil-pbc-adic-coefficient-datum are computed on this
same representative. The balancing formula s⊗(r⊗x)↦s q(r)⊗x gives the transition
square and its associativity gives the quotient cocycle. The universal derived counits
and the fixed evaluation comparison transport these equalities to K. -/
theorem pbc_reduction_adic_tower_laws (K : PbcCompletedDerived T d) :
    (∀ (b a : ℕ) (hab : a ≤ b),
      (pbcDerivedRestrict (pbcAdicProjection T d b)).map
          (adicTowerSemilinearTransition T d
            (fun n ↦ (pbcCompletedReduction T d n).obj K)
            (fun b a hab ↦ pbcReductionNormalization (pbcAdicProjection T d b)
              (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
              (pbcAdicProjection_comp T d b a hab) K) b a hab) ≫
        (pbcDerivedRestrictComp (pbcAdicProjection T d b)
          (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
          (pbcAdicProjection_comp T d b a hab)).hom.app
            ((pbcCompletedReduction T d a).obj K) ≫
        (pbcReductionEvaluationIso T d K a).hom =
      (pbcReductionEvaluationIso T d K b).hom ≫
        (pbcTowerTransition T (pbcAdicCompletion T d) b a hab).app
          ((completedReductionTower T d).obj K)) ∧
    ∀ (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
      adicTowerSemilinearTransition T d
          (fun n ↦ (pbcCompletedReduction T d n).obj K)
          (fun b a hab ↦ pbcReductionNormalization (pbcAdicProjection T d b)
            (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
            (pbcAdicProjection_comp T d b a hab) K) c a (hab.trans hbc) =
        adicTowerSemilinearTransition T d
          (fun n ↦ (pbcCompletedReduction T d n).obj K)
          (fun b a hab ↦ pbcReductionNormalization (pbcAdicProjection T d b)
            (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
            (pbcAdicProjection_comp T d b a hab) K) c b hbc ≫
          (pbcDerivedRestrict (pbcAdicQuotient T d c b hbc)).map
            (adicTowerSemilinearTransition T d
          (fun n ↦ (pbcCompletedReduction T d n).obj K)
          (fun b a hab ↦ pbcReductionNormalization (pbcAdicProjection T d b)
            (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
            (pbcAdicProjection_comp T d b a hab) K) b a hab) ≫
          (pbcDerivedRestrictComp (pbcAdicQuotient T d c b hbc)
            (pbcAdicQuotient T d b a hab) (pbcAdicQuotient T d c a (hab.trans hbc))
            (pbcAdicQuotient_comp T d c b a hab hbc)).hom.app
              ((pbcCompletedReduction T d a).obj K) := by
  sorry

/-- The actual reduction tower of K: all data come from the recorded K-flat universal
construction and balancing maps; only the two named proof fields are postponed.
Source: blueprint order 1429, opening paragraph
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcReductionAdicTower (K : PbcCompletedDerived T d) : AdicTower T d where
  tower := (completedReductionTower T d).obj K
  level n := (pbcCompletedReduction T d n).obj K
  evaluation := pbcReductionEvaluationIso T d K
  normalization b a hab := pbcReductionNormalization (pbcAdicProjection T d b)
    (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
    (pbcAdicProjection_comp T d b a hab) K
  transition := (pbc_reduction_adic_tower_laws T d K).1
  cocycle := (pbc_reduction_adic_tower_laws T d K).2

/-- A constant scalar as a section of the actual completed function coefficient ring.
The constant-to-completed map is followed by the canonical limit presentation comparison.
Source: blueprint order 1429, sufficient condition; Stacks Tag 093M
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcCompletedConstantSection (a : A) (U : T.ProEtᵒᵖ) :
    (pbcAdicCompletion T d).obj.obj U :=
  (pbcCompletedComparison T d).hom.hom.app U
    ((CompletedConstantReduction.base T d.ideal).hom.app U
      ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of A))).app U a))

/-- The residue module with its actual R_n-action, for use in the torsion counterexample.
Source: blueprint order 1429, counterexample (blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcTruncationResidueLevel (n : ℕ) :
    pbcModules T ((pbcAdicRings T d).obj (op n)) :=
  (pbcRestrict (pbcAdicQuotient T d n 0 (Nat.zero_le n))).obj
    (SheafOfModules.unit ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op 0))))

/-- The ambient residue module shifted to degree m+1. Its completed-ring action is
restriction along the actual first quotient projection.
Source: blueprint order 1429, counterexample (blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcTruncationCounterexample (m : ℤ) : PbcCompletedDerived T d :=
  ((DerivedCategory.singleFunctor _ 0).obj
    ((pbcRestrict (pbcAdicProjection T d 0)).obj
      (SheafOfModules.unit ((adicLisseForget T).obj ((pbcAdicRings T d).obj (op 0))))))
      ⟦(-(m + 1))⟧

section IntegralCoefficients

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Levelwise truncations of the reduction tower of a single completed object with
finite-extension integral coefficients, under exactly (TC).
Source: blueprint order 1429, (1) and (3)
(blueprint: prop-weil-pbc-levelwise-truncations).
Proof: use pbcReductionAdicTower, whose data are the single K-flat reduction construction.
Apply pbc_adic_levelwise_truncations: tensor the canonical triangle, use the upper
cohomological bound and the (TC) lower bound, and identify it uniquely with the next
canonical truncation triangle. Uniqueness gives naturality and the quotient cocycle;
the unit normalization gives the strict-transition and cohomology compatibility. -/
theorem pbc_levelwise_truncations
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) (m : ℤ)
    (_hTor : PbcLevelwiseTorVanishing T (pbcIntegralDatum l E)
      (pbcReductionAdicTower T (pbcIntegralDatum l E) K) m) :
    ∃ N : PbcLevelwiseTruncationData T (pbcIntegralDatum l E)
        (pbcReductionAdicTower T (pbcIntegralDatum l E) K) m,
      PbcIsLevelwiseTruncation T (pbcIntegralDatum l E) N := by
  exact pbc_adic_levelwise_truncations T (pbcIntegralDatum l E) _ m _hTor

/-- Injectivity of the uniformizer on H^q(K), q≥m+1, suffices for (TC). Injectivity
is tested on every site's sections, which is precisely monicity of scalar multiplication.
Source: blueprint order 1429, sufficient condition
(blueprint: prop-weil-pbc-levelwise-truncations).
Proof: the two-term free resolution [B --varpi^a--> B] of R_a gives the multiplication
triangle and 0→H^q(K)/varpi^a→H^q(K_a)→H^(q+1)(K)[varpi^a]→0. In the stated range the
last term vanishes. Resolve R_n over R_(n+1) by the periodic free resolution with
alternating maps varpi^n and varpi. After tensoring with H^q(K)/varpi^(n+1), injectivity
of varpi on H^q(K) identifies each kernel with the preceding image. The resolution
is K-flat because it is bounded above and flat. All its negative cohomology is zero,
giving every positive Tor, with no unbounded spectral-sequence convergence claim. -/
theorem pbc_levelwise_tor_of_uniformizer_injective
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) (m : ℤ)
    (_hinj : ∀ q : ℤ, m + 1 ≤ q → ∀ U : T.ProEtᵒᵖ,
      Function.Injective (fun x :
        ((DerivedCategory.homologyFunctor _ q).obj K).val.obj U ↦
          pbcCompletedConstantSection T (pbcIntegralDatum l E) (pbcUniformizer l E) U • x)) :
    PbcLevelwiseTorVanishing T (pbcIntegralDatum l E)
      (pbcReductionAdicTower T (pbcIntegralDatum l E) K) m := by
  sorry

/-- Uniform bounded constructibility is preserved under (TC), with the stated sharp
cohomological windows. The conclusion uses the full common-local-model predicate;
it does not claim that the original model truncations have finite free terms.
Source: blueprint order 1429, (2); Stacks Tags 09C1, 09C7 and 09C2
(blueprint: prop-weil-pbc-levelwise-truncations).
Proof: pull the two-term completed quotient resolution back to each common model domain,
retaining the actual inverse-image completed ring. A model in [d0,d1] reduces into
[d0-1,d1]. Exact restriction and the constructible etale-origin stalk comparison make
these bounds global. Canonical truncation intersects this interval with its surviving
range. Its cohomology remains intrinsically constructible. Under (TC) the preceding
normalization theorem supplies adic towers. Apply normalizedConstructibleTower_local_effectivity
to their constructible cohomology and common finite bounds to obtain new finite
stratifications and bounded common adic-lisse finite-type models, with compatible
reductions. This is existence of models; no assertion about a raw cone's term support
or local freeness of kernels is used. Empty surviving intervals mean zero. -/
theorem pbc_levelwise_truncations_constructible [IsNoetherian T]
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) (m d₀ d₁ : ℤ)
    (N : PbcLevelwiseTruncationData T (pbcIntegralDatum l E)
      (pbcReductionAdicTower T (pbcIntegralDatum l E) K) m)
    (_hN : PbcIsLevelwiseTruncation T (pbcIntegralDatum l E) N)
    (_hTor : PbcLevelwiseTorVanishing T (pbcIntegralDatum l E)
      (pbcReductionAdicTower T (pbcIntegralDatum l E) K) m)
    (_hmodels : d₀ ≤ d₁ ∧ ∃ S : Stratification T,
      ∀ α : Fin S.n, ∃ V : Sieve (⊤_ (S.domain α).ProEt),
        V ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt) ∧
        ∀ (U : (S.domain α).ProEt) (f : U ⟶ ⊤_ (S.domain α).ProEt), V f →
          Nonempty (AdicTowerLocalModel (pbcIntegralDatum l E)
            (U.hom ≫ S.immersion α)
            (pbcReductionAdicTower T (pbcIntegralDatum l E) K) d₀ d₁)) :
    IsUniformlyBoundedConstructibleAdicTower (pbcIntegralDatum l E) N.lower ∧
    IsUniformlyBoundedConstructibleAdicTower (pbcIntegralDatum l E) N.upper ∧
    (∀ (n : ℕ) (q : ℤ), (q < d₀ - 1 ∨ min m d₁ < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (N.lower.level n))) ∧
    (∀ (n : ℕ) (q : ℤ), (q < max (m + 1) (d₀ - 1) ∨ d₁ < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (N.upper.level n))) := by
  sorry

/-- On a nonempty scheme, the shifted residue example has exactly the two asserted
cohomology sheaves at each level. Its lower truncation has one cohomology sheaf, but
its next derived reduction has residue cohomology in every degree at most m, so no
normalization is possible. No splitting of the original two-degree R_n-object is claimed.
Source: blueprint order 1429, counterexample in (1)
(blueprint: prop-weil-pbc-levelwise-truncations).
Proof: over B the two-term resolution of R_n becomes [k --0--> k] after tensoring
with the shifted residue. This computes the two cohomology sheaves without an R_n-linear
splitting. The concentrated-single theorem identifies its lower truncation with k[-m].
The periodic free R_(n+1)-resolution of R_n alternates varpi^n and varpi; both maps
become zero after tensoring with k. Hence every nonpositive-degree cohomology is k. On a nonempty
scheme k is nonzero, since 0 and 1 remain distinct on some member of every cover.
At degree m-1 the derived reduction is therefore nonzero while the lower truncation
at level n is zero. They cannot be isomorphic. On the empty scheme this obstruction
vanishes, which is why nonemptiness is an explicit hypothesis. -/
theorem pbc_levelwise_truncation_counterexample (_hT : Nonempty T) (m : ℤ) :
    (∀ n : ℕ,
      Nonempty ((DerivedCategory.homologyFunctor _ m).obj
          ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj
            (pbcTruncationCounterexample T (pbcIntegralDatum l E) m)) ≅
        pbcTruncationResidueLevel T (pbcIntegralDatum l E) n) ∧
      Nonempty ((DerivedCategory.homologyFunctor _ (m + 1)).obj
          ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj
            (pbcTruncationCounterexample T (pbcIntegralDatum l E) m)) ≅
        pbcTruncationResidueLevel T (pbcIntegralDatum l E) n) ∧
      (∀ q : ℤ, q ≠ m → q ≠ m + 1 →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj
            (pbcTruncationCounterexample T (pbcIntegralDatum l E) m)))) ∧
      Nonempty ((DerivedCategory.TStructure.t.truncLE m).obj
          ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj
            (pbcTruncationCounterexample T (pbcIntegralDatum l E) m)) ≅
        ((DerivedCategory.singleFunctor _ 0).obj
          (pbcTruncationResidueLevel T (pbcIntegralDatum l E) n))⟦(-m)⟧)) ∧
    (∀ (n p : ℕ), Nonempty ((DerivedCategory.homologyFunctor _ (m - (p : ℤ))).obj
        ((pbcDerivedExtend
          (pbcAdicQuotient T (pbcIntegralDatum l E) (n + 1) n (Nat.le_succ n))).obj
            ((DerivedCategory.TStructure.t.truncLE m).obj
              ((pbcCompletedReduction T (pbcIntegralDatum l E) (n + 1)).obj
                (pbcTruncationCounterexample T (pbcIntegralDatum l E) m)))) ≅
      pbcTruncationResidueLevel T (pbcIntegralDatum l E) n)) ∧
    ∀ n : ℕ, ¬ Nonempty ((pbcDerivedExtend
        (pbcAdicQuotient T (pbcIntegralDatum l E) (n + 1) n (Nat.le_succ n))).obj
          ((DerivedCategory.TStructure.t.truncLE m).obj
            ((pbcCompletedReduction T (pbcIntegralDatum l E) (n + 1)).obj
              (pbcTruncationCounterexample T (pbcIntegralDatum l E) m))) ≅
      (DerivedCategory.TStructure.t.truncLE m).obj
        ((pbcCompletedReduction T (pbcIntegralDatum l E) n).obj
          (pbcTruncationCounterexample T (pbcIntegralDatum l E) m))) := by
  sorry

end IntegralCoefficients

open AlgebraicGeometry.ProEtale

/-- The etale reduction's shift comparison is the mate of exact scalar restriction's
specified shift comparison. No arbitrary shift structure is chosen.
Source: blueprint order 1429, final paragraph; Stacks Tag 06YY
(blueprint: prop-weil-pbc-levelwise-truncations). -/
instance pbcLevelwiseEtaleReductionCommShift (n : ℕ) :
    (pbcWitnessEtaleReduction T d n).CommShift ℤ :=
  (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology
    (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)))).leftAdjointCommShift ℤ

/-- The canonical tensor comparison for the actual etale-to-pro-etale realization and
quotient coefficient map, formed from the two published, unit-normalized mates.
Source: blueprint order 1429, final paragraph; Stacks Tag 07A4
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcLevelwiseOriginReduction (n : ℕ) :
    ((comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d (n + 1))) T).mapDerivedCategory ⋙
        pbcDerivedFunctionRealization T d (n + 1)) ⋙
        pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) ≅
      pbcWitnessEtaleReduction T d n ⋙
        ((comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory ⋙
          pbcDerivedFunctionRealization T d n) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pbcFunctionReduction T d n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pbcComparisonReduction T
          (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))) _ ≪≫
          Functor.associator _ _ _

/-- Truncate the retained origin isomorphism and precede it with the canonical
exact-comparison truncation isomorphism. This is defined without (TC).
Source: blueprint order 1429, final paragraph; Stacks Tags 0118 and 099R
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcLevelwiseOriginLE (W : PbcWitnessedTower T d) (m : ℤ) (n : ℕ) :
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.obj
        ((DerivedCategory.TStructure.t.truncLE m).obj (W.origin n).L.obj) ≅
      (DerivedCategory.TStructure.t.truncLE m).obj (W.K n) :=
  ((comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategoryTruncLEIso m).app
      (W.origin n).L.obj ≪≫
    (DerivedCategory.TStructure.t.truncLE m).mapIso (W.alpha n)

/-- Truncate the retained origin isomorphism and precede it with the canonical
exact-comparison truncation isomorphism. This is defined without (TC).
Source: blueprint order 1429, final paragraph; Stacks Tags 0118 and 099R
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcLevelwiseOriginGE (W : PbcWitnessedTower T d) (m : ℤ) (n : ℕ) :
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.origin n).L.obj) ≅
      (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.K n) :=
  ((comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategoryTruncGEIso
      (m + 1)).app
      (W.origin n).L.obj ≪≫
    (DerivedCategory.TStructure.t.truncGE (m + 1)).mapIso (W.alpha n)

/-- Functorial truncation of the original Etale semilinear step, with the
canonical exact scalar-restriction comparison; defined without (TC).
Source: blueprint order 1429, (3) and final paragraph
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcLevelwiseEtaleStepLE (W : PbcWitnessedTower T d) (m : ℤ) (n : ℕ) :
    (DerivedCategory.TStructure.t.truncLE m).obj ((W.origin (n + 1)).L.obj) ⟶
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).obj
          ((DerivedCategory.TStructure.t.truncLE m).obj (W.origin n).L.obj) :=
  (DerivedCategory.TStructure.t.truncLE m).map
      ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)))).unit.app ((W.origin (n + 1)).L.obj) ≫
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology
          (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).map (W.beta n).hom) ≫
    ((Sheaf.restrictScalars T.smallEtaleTopology
      (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).mapDerivedCategoryTruncLEIso m).inv.app
        (W.origin n).L.obj

/-- Functorial truncation of the original Etale semilinear step, with the
canonical exact scalar-restriction comparison; defined without (TC).
Source: blueprint order 1429, (3) and final paragraph
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcLevelwiseEtaleStepGE (W : PbcWitnessedTower T d) (m : ℤ) (n : ℕ) :
    (DerivedCategory.TStructure.t.truncGE (m + 1)).obj ((W.origin (n + 1)).L.obj) ⟶
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).obj
          ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.origin n).L.obj) :=
  (DerivedCategory.TStructure.t.truncGE (m + 1)).map
      ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)))).unit.app ((W.origin (n + 1)).L.obj) ≫
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology
          (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).map (W.beta n).hom) ≫
    ((Sheaf.restrictScalars T.smallEtaleTopology
      (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).mapDerivedCategoryTruncGEIso
        (m + 1)).inv.app
        (W.origin n).L.obj

/-- Functorial truncation of the original ProEtale semilinear step, with the
canonical exact scalar-restriction comparison; defined without (TC).
Source: blueprint order 1429, (3) and final paragraph
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcLevelwiseProEtaleStepLE (W : PbcWitnessedTower T d) (m : ℤ) (n : ℕ) :
    (DerivedCategory.TStructure.t.truncLE m).obj (W.K (n + 1)) ⟶
      (Sheaf.derivedRestrictScalars (ProEt.topology T)
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).obj
          ((DerivedCategory.TStructure.t.truncLE m).obj (W.K n)) :=
  (DerivedCategory.TStructure.t.truncLE m).map
      ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (ProEt.topology T)
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)))).unit.app (W.K (n + 1)) ≫
        (Sheaf.derivedRestrictScalars (ProEt.topology T)
          (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).map (W.theta n).hom) ≫
    ((Sheaf.restrictScalars (ProEt.topology T)
      (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).mapDerivedCategoryTruncLEIso m).inv.app
        (W.K n)

/-- Functorial truncation of the original ProEtale semilinear step, with the
canonical exact scalar-restriction comparison; defined without (TC).
Source: blueprint order 1429, (3) and final paragraph
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcLevelwiseProEtaleStepGE (W : PbcWitnessedTower T d) (m : ℤ) (n : ℕ) :
    (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.K (n + 1)) ⟶
      (Sheaf.derivedRestrictScalars (ProEt.topology T)
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).obj
          ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.K n)) :=
  (DerivedCategory.TStructure.t.truncGE (m + 1)).map
      ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (ProEt.topology T)
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)))).unit.app (W.K (n + 1)) ≫
        (Sheaf.derivedRestrictScalars (ProEt.topology T)
          (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).map (W.theta n).hom) ≫
    ((Sheaf.restrictScalars (ProEt.topology T)
      (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).mapDerivedCategoryTruncGEIso
        (m + 1)).inv.app
        (W.K n)

set_option backward.isDefEq.respectTransparency false in
private lemma witness_semilinear_compatibility (W : PbcWitnessedTower T d) (n : ℕ) :
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d (n + 1))) T).mapDerivedCategory.map
        ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology
          (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)))).unit.app
            (W.origin (n + 1)).L.obj ≫
          (Sheaf.derivedRestrictScalars T.smallEtaleTopology
            (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).map (W.beta n).hom) ≫
      (pbcDerivedComparisonRestrict T
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).inv.app (W.origin n).L.obj ≫
      (Sheaf.derivedRestrictScalars (ProEt.topology T)
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).map (W.alpha n).hom =
    (W.alpha (n + 1)).hom ≫
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (ProEt.topology T)
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)))).unit.app (W.K (n + 1)) ≫
      (Sheaf.derivedRestrictScalars (ProEt.topology T)
        (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).map (W.theta n).hom := by
  -- Taking adjuncts turns the normalization square into the semilinear square.
  let φ := pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)
  let adjE := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
  let adjP := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (ProEt.topology T) φ)
  have hu := unit_mateEquiv_symm adjE adjP
    (TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict T φ).inv)
    (W.origin (n + 1)).L.obj
  simp only [Functor.map_comp, Category.assoc]
  have hn := (pbcDerivedComparisonRestrict T φ).inv.naturality (W.beta n).hom
  dsimp only [Functor.comp_map, φ] at hn
  rw [reassoc_of% hn]
  change _ ≫ (pbcDerivedComparisonRestrict T φ).inv.app _ =
    _ ≫ (Sheaf.derivedRestrictScalars (ProEt.topology T) φ).map
      ((pbcComparisonReduction T φ).hom.app (W.origin (n + 1)).L.obj) at hu
  dsimp only [φ, adjE, adjP] at hu
  dsimp only [pbcWitnessEtaleReduction]
  rw [reassoc_of% hu]
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hc := W.compatibility n
  change _ = (pbcComparisonReduction T φ).inv.app _ ≫ _ at hc
  change _ ≫ (W.alpha n).hom = _ at hc
  dsimp only [φ] at hc
  rw [hc]
  simp only [Iso.hom_inv_id_app_assoc, Functor.map_comp]
  have ha := adjP.unit.naturality (W.alpha (n + 1)).hom
  dsimp only [Functor.comp_map, Functor.id_map, φ, adjP, PbcWitnessedTower.alpha] at ha
  dsimp only [pbcWitnessReduction, pbcFixedScalarExtension, PbcWitnessedTower.alpha]
  rw [← reassoc_of% ha]

private lemma truncGE_comparison_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : DerivedCategory C) (m : ℤ) :
    F.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncGEπ m).app X) ≫
        (F.mapDerivedCategoryTruncGEIso m).hom.app X =
      (DerivedCategory.TStructure.t.truncGEπ m).app (F.mapDerivedCategory.obj X) := by
  apply (cancel_mono ((F.mapDerivedCategoryTruncGEIso m).inv.app X)).mp
  simp only [Category.assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  simpa only [Category.comp_id] using (truncGE_restriction_unit F X m).symm

private lemma originGE_unit (W : PbcWitnessedTower T d) (m : ℤ) (n : ℕ) :
    (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
        ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (W.origin n).L.obj) ≫
      (pbcLevelwiseOriginGE T d W m n).hom =
        (W.alpha n).hom ≫ (DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (W.K n) := by
  simp only [pbcLevelwiseOriginGE, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Category.assoc, truncGE_comparison_unit]
  exact ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).naturality (W.alpha n).hom).symm

private lemma truncated_stepGE_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : C ⥤ D) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {X : DerivedCategory D} {Y : DerivedCategory C}
    (f : X ⟶ U.mapDerivedCategory.obj Y) (m : ℤ) :
    (DerivedCategory.TStructure.t.truncGEπ m).app X ≫
        (DerivedCategory.TStructure.t.truncGE m).map f ≫
          (U.mapDerivedCategoryTruncGEIso m).inv.app Y =
      f ≫ U.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncGEπ m).app Y) := by
  rw [← Category.assoc, ← (DerivedCategory.TStructure.t.truncGEπ m).naturality f]
  rw [Category.assoc, truncGE_restriction_unit]
  rfl

private lemma originLE_counit (W : PbcWitnessedTower T d) (m : ℤ) (n : ℕ) :
    (pbcLevelwiseOriginLE T d W m n).hom ≫
        (DerivedCategory.TStructure.t.truncLEι m).app (W.K n) =
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
        ((DerivedCategory.TStructure.t.truncLEι m).app (W.origin n).L.obj) ≫
          (W.alpha n).hom := by
  simp only [pbcLevelwiseOriginLE, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [(DerivedCategory.TStructure.t.truncLEι m).naturality]
  simp only [Iso.app_hom, Functor.id_map]
  rw [← Category.assoc, truncLE_comparison_counit]

private lemma truncated_stepLE_counit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : C ⥤ D) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {X : DerivedCategory D} {Y : DerivedCategory C}
    (f : X ⟶ U.mapDerivedCategory.obj Y) (m : ℤ) :
    (DerivedCategory.TStructure.t.truncLE m).map f ≫
        (U.mapDerivedCategoryTruncLEIso m).inv.app Y ≫
          U.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncLEι m).app Y) =
      (DerivedCategory.TStructure.t.truncLEι m).app X ≫ f := by
  rw [truncLE_restriction_counit]
  exact (DerivedCategory.TStructure.t.truncLEι m).naturality f

set_option backward.isDefEq.respectTransparency false in
/-- Without (TC), the truncated etale antecedents give the retained levelwise origin
pairs, with the stated isomorphisms and compatibility with strict transitions only.
Source: blueprint order 1429, final paragraph
(blueprint: prop-weil-pbc-levelwise-truncations).
Proof: exact comparison inverse image preserves the kernels and cokernels in good
truncation. Its canonical truncation isomorphisms therefore commute with all chain
maps and descend through quasi-isomorphisms. Compose with the truncated original alpha.
Truncation of a bounded-below object stays bounded below, giving the retained pairs.
Apply naturality to the original semilinear steps. The comparison/restriction square
is the specified derived restriction comparison, so both displayed transition squares
commute. No scalar-extension normalization of the truncated objects is asserted. -/
theorem pbc_levelwise_truncation_origins (W : PbcWitnessedTower T d) (m : ℤ) :
    (∀ n : ℕ,
      ∃ h : DerivedCategory.TStructure.t.plus
          ((finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj
            ((DerivedCategory.TStructure.t.truncLE m).obj (W.K n))),
        ∃ V : ProEtale.EtaleOriginWitness T (PbcQuotient d n)
            ⟨(finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj
              ((DerivedCategory.TStructure.t.truncLE m).obj (W.K n)), h⟩,
          ∃ hL : V.L.obj = (DerivedCategory.TStructure.t.truncLE m).obj (W.origin n).L.obj,
            (pbcFixedOriginAlpha T (PbcQuotient d n)
              ((DerivedCategory.TStructure.t.truncLE m).obj (W.K n)) h V).hom =
              (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
                (eqToHom hL) ≫ (pbcLevelwiseOriginLE T d W m n).hom) ∧
    (∀ n : ℕ,
      ∃ h : DerivedCategory.TStructure.t.plus
          ((finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj
            ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.K n))),
        ∃ V : ProEtale.EtaleOriginWitness T (PbcQuotient d n)
            ⟨(finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj
              ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.K n)), h⟩,
          ∃ hL : V.L.obj = (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.origin n).L.obj,
            (pbcFixedOriginAlpha T (PbcQuotient d n)
              ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.K n)) h V).hom =
              (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
                (eqToHom hL) ≫ (pbcLevelwiseOriginGE T d W m n).hom) ∧
    (∀ n : ℕ,
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d (n + 1))) T).mapDerivedCategory.map
          (pbcLevelwiseEtaleStepLE T d W m n) ≫
        (pbcDerivedComparisonRestrict T
          (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).inv.app
            ((DerivedCategory.TStructure.t.truncLE m).obj (W.origin n).L.obj) ≫
        (Sheaf.derivedRestrictScalars (ProEt.topology T)
          (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).map
            (pbcLevelwiseOriginLE T d W m n).hom =
      (pbcLevelwiseOriginLE T d W m (n + 1)).hom ≫
        pbcLevelwiseProEtaleStepLE T d W m n) ∧
    (∀ n : ℕ,
      (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d (n + 1))) T).mapDerivedCategory.map
          (pbcLevelwiseEtaleStepGE T d W m n) ≫
        (pbcDerivedComparisonRestrict T
          (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).inv.app
            ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.origin n).L.obj) ≫
        (Sheaf.derivedRestrictScalars (ProEt.topology T)
          (pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n))).map
            (pbcLevelwiseOriginGE T d W m n).hom =
      (pbcLevelwiseOriginGE T d W m (n + 1)).hom ≫
        pbcLevelwiseProEtaleStepGE T d W m n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    -- Choose only bounds; both the object and its origin isomorphism are explicit.
    obtain ⟨k, hk⟩ := W.boundedBelow n
    let F := finiteCoefficientRealization T (PbcQuotient d n)
    have htr : (DerivedCategory.TStructure.t.IsGE (F.mapDerivedCategory.obj
        ((DerivedCategory.TStructure.t.truncLE m).obj (W.K n))) k) := by
      have : DerivedCategory.TStructure.t.IsGE (F.mapDerivedCategory.obj (W.K n)) k := hk
      have : DerivedCategory.TStructure.t.IsGE
          ((DerivedCategory.TStructure.t.truncLE m).obj (F.mapDerivedCategory.obj (W.K n))) k :=
        inferInstance
      let e : F.mapDerivedCategory.obj
          ((DerivedCategory.TStructure.t.truncLE m).obj (W.K n)) ≅
          (DerivedCategory.TStructure.t.truncLE m).obj (F.mapDerivedCategory.obj (W.K n)) :=
        (F.mapDerivedCategoryTruncLEIso m).app (W.K n)
      exact DerivedCategory.TStructure.t.isGE_of_iso e.symm k
    let h : DerivedCategory.TStructure.t.plus (F.mapDerivedCategory.obj
        ((DerivedCategory.TStructure.t.truncLE m).obj (W.K n))) := ⟨k, htr⟩
    let L : DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (PbcQuotient d n))) :=
      ⟨(DerivedCategory.TStructure.t.truncLE m).obj (W.origin n).L.obj, by
        obtain ⟨j, hj⟩ := (W.origin n).L.property
        have := hj
        exact ⟨j, inferInstance⟩⟩
    let V : ProEtale.EtaleOriginWitness T (PbcQuotient d n)
        ⟨F.mapDerivedCategory.obj ((DerivedCategory.TStructure.t.truncLE m).obj (W.K n)), h⟩ :=
      { L := L
        alpha := DerivedCategory.Plus.ι.preimageIso
          ((Functor.mapDerivedCategoryCompIso
            (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T) F).app L.obj ≪≫
              F.mapDerivedCategory.mapIso (pbcLevelwiseOriginLE T d W m n)) }
    refine ⟨h, V, rfl, ?_⟩
    simp only [eqToHom_refl]
    apply F.mapDerivedCategory.map_injective
    dsimp [pbcFixedOriginAlpha, V]
    change F.mapDerivedCategory.map (F.mapDerivedCategory.preimage _) = _
    rw [Functor.map_preimage]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.preimageIso_hom]
    rw [Functor.map_preimage]
    simp [F]
  · intro n
    obtain ⟨k, hk⟩ := W.boundedBelow n
    let F := finiteCoefficientRealization T (PbcQuotient d n)
    have htr : (DerivedCategory.TStructure.t.IsGE (F.mapDerivedCategory.obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.K n))) k) := by
      have : DerivedCategory.TStructure.t.IsGE (F.mapDerivedCategory.obj (W.K n)) k := hk
      have : DerivedCategory.TStructure.t.IsGE
          ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj
            (F.mapDerivedCategory.obj (W.K n))) k :=
        inferInstance
      let e : F.mapDerivedCategory.obj
          ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.K n)) ≅
          (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (F.mapDerivedCategory.obj (W.K n)) :=
        (F.mapDerivedCategoryTruncGEIso (m + 1)).app (W.K n)
      exact DerivedCategory.TStructure.t.isGE_of_iso e.symm k
    let h : DerivedCategory.TStructure.t.plus (F.mapDerivedCategory.obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.K n))) := ⟨k, htr⟩
    let L : DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (PbcQuotient d n))) :=
      ⟨(DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.origin n).L.obj, by
        obtain ⟨j, hj⟩ := (W.origin n).L.property
        have := hj
        exact ⟨j, inferInstance⟩⟩
    let V : ProEtale.EtaleOriginWitness T (PbcQuotient d n)
        ⟨F.mapDerivedCategory.obj
          ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.K n)), h⟩ :=
      { L := L
        alpha := DerivedCategory.Plus.ι.preimageIso
          ((Functor.mapDerivedCategoryCompIso
            (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T) F).app L.obj ≪≫
              F.mapDerivedCategory.mapIso (pbcLevelwiseOriginGE T d W m n)) }
    refine ⟨h, V, rfl, ?_⟩
    simp only [eqToHom_refl]
    apply F.mapDerivedCategory.map_injective
    dsimp [pbcFixedOriginAlpha, V]
    change F.mapDerivedCategory.map (F.mapDerivedCategory.preimage _) = _
    rw [Functor.map_preimage]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.preimageIso_hom]
    rw [Functor.map_preimage]
    simp [F]
  · intro n
    let φ := pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)
    let F := comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d (n + 1))) T
    let U := Sheaf.restrictScalars (ProEt.topology T) φ
    have : DerivedCategory.TStructure.t.IsLE
        (F.mapDerivedCategory.obj
          ((DerivedCategory.TStructure.t.truncLE m).obj (W.origin (n + 1)).L.obj)) m :=
      F.isLE_mapDerivedCategory_obj _ m
    apply (cancel_mono ((U.mapDerivedCategoryTruncLEIso m).hom.app (W.K n))).mp
    -- The counit characterizes a map into the lower truncation.
    apply DerivedCategory.TStructure.t.to_truncLE_obj_ext
    simp only [Category.assoc, truncLE_comparison_counit]
    dsimp only [U, φ]
    simp only [← Functor.map_comp, originLE_counit]
    dsimp only [pbcLevelwiseProEtaleStepLE]
    simp only [Category.assoc]
    rw [truncated_stepLE_counit]
    rw [reassoc_of% originLE_counit T d W m (n + 1)]
    simp only [Functor.map_comp]
    have hn := (pbcDerivedComparisonRestrict T φ).inv.naturality
      ((DerivedCategory.TStructure.t.truncLEι m).app (W.origin n).L.obj)
    dsimp only [Functor.comp_map, φ] at hn
    rw [← reassoc_of% hn]
    rw [← Category.assoc, ← Functor.map_comp]
    dsimp only [pbcLevelwiseEtaleStepLE]
    rw [Category.assoc, truncated_stepLE_counit]
    simp only [Functor.map_comp, Category.assoc]
    have hs := witness_semilinear_compatibility T d W n
    simp only [Functor.map_comp, Category.assoc] at hs
    rw [hs]
  · intro n
    let φ := pbcWitnessQuotientMap d (n + 1) n (Nat.le_succ n)
    let F := comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d (n + 1))) T
    let U := Sheaf.restrictScalars (ProEt.topology T) φ
    have : DerivedCategory.TStructure.t.IsGE
        (U.mapDerivedCategory.obj
          ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.K n))) (m + 1) :=
      U.isGE_mapDerivedCategory_obj _ (m + 1)
    apply (cancel_epi
      ((F.mapDerivedCategoryTruncGEIso (m + 1)).inv.app (W.origin (n + 1)).L.obj)).mp
    -- Dually, the unit characterizes a map from the upper truncation.
    apply DerivedCategory.TStructure.t.from_truncGE_obj_ext
    simp only [← Category.assoc, truncGE_restriction_unit]
    dsimp only [F]
    rw [originGE_unit]
    simp only [Category.assoc]
    dsimp only [pbcLevelwiseProEtaleStepGE]
    rw [truncated_stepGE_unit]
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp]
    dsimp only [pbcLevelwiseEtaleStepGE]
    rw [Category.assoc, truncated_stepGE_unit]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (pbcDerivedComparisonRestrict T φ).inv.naturality
      ((DerivedCategory.TStructure.t.truncGEπ (m + 1)).app (W.origin n).L.obj)
    dsimp only [Functor.comp_map, φ] at hn
    rw [reassoc_of% hn]
    rw [← Functor.map_comp, originGE_unit]
    simp only [Functor.map_comp]
    have hs := witness_semilinear_compatibility T d W n
    simp only [Functor.map_comp, Category.assoc] at hs
    rw [← reassoc_of% hs]

/-- The canonical realization of a truncated witnessed level, transported to the
specified quotient-linear truncation of M. All four factors are recorded canonical maps.
Source: blueprint order 1429, final paragraph
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcTruncatedRealizationLE {M : AdicTower T d} {m : ℤ}
    (N : PbcLevelwiseTruncationData T d M m) (W V : PbcWitnessedTower T d)
    (hV : ∀ n : ℕ, V.K n = (DerivedCategory.TStructure.t.truncLE m).obj (W.K n))
    (e : ∀ n : ℕ, (pbcDerivedFunctionRealization T d n).obj (W.K n) ≅ M.level n) (n : ℕ) :
    (pbcDerivedFunctionRealization T d n).obj (V.K n) ≅ N.lower.level n :=
  (pbcDerivedFunctionRealization T d n).mapIso (eqToIso (hV n)) ≪≫
    ((pbcFunctionRealization T d n).mapDerivedCategoryTruncLEIso m).app (W.K n) ≪≫
      (DerivedCategory.TStructure.t.truncLE m).mapIso (e n) ≪≫
        (eqToIso (N.lowerLevel n)).symm

/-- The truncated etale normalization in the actual canonical truncation objects.
Source: blueprint order 1429, final paragraph
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcTruncatedEtaleNormalizationLE (W V : PbcWitnessedTower T d) (m : ℤ)
    (hV : ∀ n : ℕ,
      (V.origin n).L.obj = (DerivedCategory.TStructure.t.truncLE m).obj (W.origin n).L.obj)
    (n : ℕ) :
    (pbcWitnessEtaleReduction T d n).obj
        ((DerivedCategory.TStructure.t.truncLE m).obj (W.origin (n + 1)).L.obj) ≅
      (DerivedCategory.TStructure.t.truncLE m).obj (W.origin n).L.obj :=
  (pbcWitnessEtaleReduction T d n).mapIso (eqToIso (hV (n + 1))).symm ≪≫
    V.beta n ≪≫ eqToIso (hV n)

/-- The canonical realization of a truncated witnessed level, transported to the
specified quotient-linear truncation of M. All four factors are recorded canonical maps.
Source: blueprint order 1429, final paragraph
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcTruncatedRealizationGE {M : AdicTower T d} {m : ℤ}
    (N : PbcLevelwiseTruncationData T d M m) (W V : PbcWitnessedTower T d)
    (hV : ∀ n : ℕ, V.K n = (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.K n))
    (e : ∀ n : ℕ, (pbcDerivedFunctionRealization T d n).obj (W.K n) ≅ M.level n) (n : ℕ) :
    (pbcDerivedFunctionRealization T d n).obj (V.K n) ≅ N.upper.level n :=
  (pbcDerivedFunctionRealization T d n).mapIso (eqToIso (hV n)) ≪≫
    ((pbcFunctionRealization T d n).mapDerivedCategoryTruncGEIso (m + 1)).app (W.K n) ≪≫
      (DerivedCategory.TStructure.t.truncGE (m + 1)).mapIso (e n) ≪≫
        (eqToIso (N.upperLevel n)).symm

/-- The truncated etale normalization in the actual canonical truncation objects.
Source: blueprint order 1429, final paragraph
(blueprint: prop-weil-pbc-levelwise-truncations). -/
def pbcTruncatedEtaleNormalizationGE (W V : PbcWitnessedTower T d) (m : ℤ)
    (hV : ∀ n : ℕ,
      (V.origin n).L.obj = (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.origin n).L.obj)
    (n : ℕ) :
    (pbcWitnessEtaleReduction T d n).obj
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.origin (n + 1)).L.obj) ≅
      (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.origin n).L.obj :=
  (pbcWitnessEtaleReduction T d n).mapIso (eqToIso (hV (n + 1))).symm ≪≫
    V.beta n ≪≫ eqToIso (hV n)

/-- Under (TC), the levelwise retained origins are normalized compatibly with both
adic truncations. Their alpha maps are exactly the truncated original maps, and their
beta maps identify the entire reduced etale truncation triangle with the next one.
All longer quotient maps are iterated composites, so both identity and quotient
cocycles are retained by PbcWitnessedTower. This theorem makes no normalization claim
without (TC); that case is pbc_levelwise_truncation_origins.
Source: blueprint order 1429, final paragraph; Stacks Tags 099R, 06YY and 07A4
(blueprint: prop-weil-pbc-levelwise-truncations).

Proof: exact comparison commutes with cohomology and truncation. The canonical tensor
comparison, characterized by balancing on K-flat representatives, identifies the
pullbacks of the etale higher Tor sheaves with those of the pro-etale levels. The latter
vanish by (TC). The comparison unit is an isomorphism, so inverse image reflects their
vanishing. Apply the tensor-bound and triangle-uniqueness argument to the etale beta
maps. This supplies normalized truncated etale triangles and quotient cocycles. Pull
them back and compose with the truncated alpha. The input normalization compatibility
identifies the middle component with the original one; uniqueness then identifies both
end components with the pro-etale truncation normalizations. The fixed function-ring
realization and tensor mates transport precisely these equations. On pure tensors all
three-quotient comparisons multiply the same residues, so the full cocycles agree. -/
theorem pbc_levelwise_truncation_compatible_origins {M : AdicTower T d} {m : ℤ}
    (_hTor : PbcLevelwiseTorVanishing T d M m)
    (N : PbcLevelwiseTruncationData T d M m) (_hN : PbcIsLevelwiseTruncation T d N)
    (W : PbcWitnessedTower T d)
    (e : ∀ n : ℕ, (pbcDerivedFunctionRealization T d n).obj (W.K n) ≅ M.level n)
    (_he : ∀ n : ℕ,
      (pbcDerivedFunctionRealization T d n).map (W.theta n).hom ≫ (e n).hom =
        (pbcFunctionReduction T d n).inv.app (W.K (n + 1)) ≫
          (pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).map
            (e (n + 1)).hom ≫ (M.normalization (n + 1) n (Nat.le_succ n)).hom) :
    ∃ (Wminus Wplus : PbcWitnessedTower T d)
      (hKminus : ∀ n : ℕ, Wminus.K n = (DerivedCategory.TStructure.t.truncLE m).obj (W.K n))
      (hKplus : ∀ n : ℕ,
        Wplus.K n = (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.K n))
      (hLminus : ∀ n : ℕ,
        (Wminus.origin n).L.obj = (DerivedCategory.TStructure.t.truncLE m).obj (W.origin n).L.obj)
      (hLplus : ∀ n : ℕ, (Wplus.origin n).L.obj =
        (DerivedCategory.TStructure.t.truncGE (m + 1)).obj (W.origin n).L.obj),
      (∀ n : ℕ,
        (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
            (eqToHom (hLminus n)) ≫ (pbcLevelwiseOriginLE T d W m n).hom =
          (Wminus.alpha n).hom ≫ eqToHom (hKminus n)) ∧
      (∀ n : ℕ,
        (pbcDerivedFunctionRealization T d n).map (Wminus.theta n).hom ≫
            (pbcTruncatedRealizationLE T d N W Wminus hKminus e n).hom =
          (pbcFunctionReduction T d n).inv.app (Wminus.K (n + 1)) ≫
            (pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).map
              (pbcTruncatedRealizationLE T d N W Wminus hKminus e (n + 1)).hom ≫
                (N.lower.normalization (n + 1) n (Nat.le_succ n)).hom) ∧
      (∀ n : ℕ,
        (comparisonUpperStar (ModuleCat.{u + 1} (PbcQuotient d n)) T).mapDerivedCategory.map
            (eqToHom (hLplus n)) ≫ (pbcLevelwiseOriginGE T d W m n).hom =
          (Wplus.alpha n).hom ≫ eqToHom (hKplus n)) ∧
      (∀ n : ℕ,
        (pbcDerivedFunctionRealization T d n).map (Wplus.theta n).hom ≫
            (pbcTruncatedRealizationGE T d N W Wplus hKplus e n).hom =
          (pbcFunctionReduction T d n).inv.app (Wplus.K (n + 1)) ≫
            (pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).map
              (pbcTruncatedRealizationGE T d N W Wplus hKplus e (n + 1)).hom ≫
                (N.upper.normalization (n + 1) n (Nat.le_succ n)).hom) ∧
      (∀ n : ℕ, ∃! τ : (pbcWitnessEtaleReduction T d n).mapTriangle.obj
          ((DerivedCategory.TStructure.t.triangleLEGE m (m + 1) rfl).obj
            (W.origin (n + 1)).L.obj) ≅
          (DerivedCategory.TStructure.t.triangleLEGE m (m + 1) rfl).obj (W.origin n).L.obj,
        τ.hom.hom₁ = (pbcTruncatedEtaleNormalizationLE T d W Wminus m hLminus n).hom ∧
        τ.hom.hom₂ = (W.beta n).hom ∧
        τ.hom.hom₃ = (pbcTruncatedEtaleNormalizationGE T d W Wplus m hLplus n).hom) := by
  sorry

end AlgebraicGeometry.Scheme
