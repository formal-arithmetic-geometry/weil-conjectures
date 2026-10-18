/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Sheaf.CategoryTheory.Triangulated.MilnorSequence
public import Sheaf.Paper.PbcRoosTriangle
public import Sheaf.Paper.SequentialDerivedInverseLimit
import Sheaf.AlgebraicGeometry.MLSetsTowerLimitNonempty
import Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups
import WeilConjectures.AlgebraicGeometry.MLSetsTowerLimitNonempty

/-!
# Mittag--Leffler vanishing for finite abelian groups

Source: blueprint sec-deligne-laumon-a1/sk-l-dl-a1-endpoints, order 2731;
Stacks Project, Tags 07KW and 07KY (blueprint: lem-weil-pbc-mittag-leffler).
The natural index n denotes positive level n+1. Canonical maps in D(Ab) are specified
by their limit-projection equations, exactly as in `milnor_shortExact`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v t
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- The first right derived inverse limit with the recorded canonical instance parameters.
This abbreviates the existing right derived functor; it does not replace it by a cokernel.
Source: Stacks Tag 07KW (blueprint: lem-weil-pbc-mittag-leffler). -/
abbrev firstDerivedLimitAb (B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) : AddCommGrpCat.{u} :=
  letI := roosTowerEnoughInjectives
  letI := roosLimitAdditive
  ((lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived 1).obj B

/-- Finite abelian groups form an ML tower and its first derived inverse limit vanishes.
Source: Stacks Tags 02N0, 0597 and 07KW (blueprint: lem-weil-pbc-mittag-leffler).
Proof: for a fixed level the descending images are subgroups of a finite group.
Choose an image of minimum cardinality; all later images equal it. For any tuple y,
the finite nonempty sets of prefix solutions x_j-f_j(x_(j+1))=y_j form an ML tower:
choose the last x to be zero and solve backwards; descending finite images stabilize.
By lem-weil-pbc-ml-sets-tower-limit-nonempty there is a compatible family of prefixes,
hence a full solution. Thus roosMap is surjective. The cokernel description in
lem-pc-derived-limit-roos-abelian-groups identifies R¹ lim with zero. -/
theorem finiteTower_mittagLeffler_vanishing (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hA : ∀ n : ℕᵒᵖ, Finite (A.obj n)) :
    (A ⋙ forget AddCommGrpCat).IsMittagLeffler ∧
      IsZero (firstDerivedLimitAb A) := by
  sorry

/-- Finiteness one degree earlier makes the canonical Milnor projection invertible.
Source: Stacks Tag 07KY (blueprint: lem-weil-pbc-mittag-leffler).
Proof: apply finiteTower_mittagLeffler_vanishing to H^(i-1)(K_n). In the short exact
sequence of lem-pc-derived-limit-milnor-sequence the first term is zero. Thus its
right arrow is mono and epi, hence an isomorphism. The equations hπ identify b with
that canonical right arrow, since the limit projections jointly determine a map. -/
theorem milnorMap_isIso_of_finite [HasDerivedCategory.{v} AddCommGrpCat.{u}]
    (K : ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u})
    [HasProduct (fun n : ℕ ↦ K.obj (op n))]
    (L : DerivedCategory AddCommGrpCat.{u})
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj (op n))
    (δ : (∏ᶜ fun n : ℕ ↦ K.obj (op n)) ⟶ L⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op) L p δ)
    (i : ℤ)
    (hfinite : ∀ n : ℕᵒᵖ,
      Finite ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)).obj (K.obj n)))
    (b : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj L ⟶
      limit (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i))
    (hπ : ∀ n : ℕ, b ≫ limit.π
      (K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) (op n) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
        (p ≫ Pi.π (fun n : ℕ ↦ K.obj (op n)) n)) : IsIso b := by
  sorry

/-- For finite groups in degree zero the Milnor projection is invertible in every degree.
Source: Stacks Tag 07KY (blueprint: lem-weil-pbc-mittag-leffler).
Proof: the cohomology in degree i-1 of each single-degree object is either the finite
group itself or zero. Apply milnorMap_isIso_of_finite in each integer degree. -/
theorem milnorMap_single_isIso_of_finite [HasDerivedCategory.{v} AddCommGrpCat.{u}]
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (hA : ∀ n : ℕᵒᵖ, Finite (A.obj n))
    [HasProduct (fun n : ℕ ↦
      (DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (A.obj (op n)))]
    (L : DerivedCategory AddCommGrpCat.{u})
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦
      (DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (A.obj (op n)))
    (δ : (∏ᶜ fun n : ℕ ↦
      (DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (A.obj (op n))) ⟶ L⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle
      (fun n ↦ (DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).map
        (A.map (homOfLE (Nat.le_succ n)).op)) L p δ)
    (i : ℤ)
    (b : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj L ⟶
      limit (A ⋙ DerivedCategory.singleFunctor AddCommGrpCat.{u} 0 ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i))
    (hπ : ∀ n : ℕ, b ≫ limit.π
      (A ⋙ DerivedCategory.singleFunctor AddCommGrpCat.{u} 0 ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) (op n) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
        (p ≫ Pi.π (fun n : ℕ ↦
          (DerivedCategory.singleFunctor AddCommGrpCat.{u} 0).obj (A.obj (op n))) n)) :
    IsIso b := by
  sorry

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Finiteness in degree i-1 makes the evaluated pro-etale Milnor map invertible.
Source: blueprint order 2731; Stacks Tags 07KW and 07KY
(blueprint: lem-weil-pbc-mittag-leffler).
Proof: exact evaluation yields the tower of finite groups H^(i-1)(U,M_n).
Apply finiteTower_mittagLeffler_vanishing to annihilate its first derived limit.
The evaluated exact sequence of prop-weil-pbc-roos-triangle then has zero left term,
so its right arrow is mono and epi. Its projection equations identify it with b,
since the limit projections jointly determine a map. The same argument applies to
any specified Roos triangle: evaluate its long exact sequence, identify the product
cohomology with the product of the cohomology groups, and identify its kernel and
cokernel using lem-pc-derived-limit-roos-abelian-groups. Thus b is invertible.
The weak-contractibility condition on U makes sections exact, so the recorded
cohomology presheaf computes hypercohomology, also for unbounded towers. -/
theorem completedMilnorMap_isIso_of_finite
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : Scheme.AdicCoefficientDatum A)
    (M : DerivedCategory (Scheme.CompletedAdicTowers T d))
    (L : DerivedCategory (Scheme.CompletedAdicModules T d))
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ ((adicDerivedTowerEvaluation T d).obj M).obj (op n))
    (δ : (∏ᶜ fun n : ℕ ↦ ((adicDerivedTowerEvaluation T d).obj M).obj (op n)) ⟶
      L⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle
      (fun n : ℕ ↦ ((adicDerivedTowerEvaluation T d).obj M).map
        (homOfLE (Nat.le_succ n)).op) L p δ)
    (U : (pbcMilnorTests T).FullSubcategory) (i : ℤ)
    (hfinite : ∀ n : ℕᵒᵖ, Finite
      ((((pbcCohomologyTowers T d (i - 1)).obj M).obj (op U)).obj n))
    (b : ((pbcCohomologyPresheaf T d i).obj L).obj (op U) ⟶
      limit (((pbcCohomologyTowers T d i).obj M).obj (op U)))
    (hπ : ∀ n : ℕ, b ≫ limit.π
      (((pbcCohomologyTowers T d i).obj M).obj (op U)) (op n) =
      ((pbcCohomologyPresheaf T d i).map
        (p ≫ Pi.π (fun n : ℕ ↦ ((adicDerivedTowerEvaluation T d).obj M).obj (op n)) n)).app
          (op U)) : IsIso b := by
  sorry

end AlgebraicGeometry.ProEtale
