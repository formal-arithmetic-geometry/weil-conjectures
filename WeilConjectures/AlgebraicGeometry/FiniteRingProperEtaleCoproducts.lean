/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.FiniteRingEtaleDerivedComparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeTorsionCohomologicalDimension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-! # Proper pushforward preserves coproducts for arbitrary finite rings

Source: Stacks Project, Tags 0F0D, 0F11 and 095U.
(blueprint: lem-sfb-finite-proper-derived-coproducts)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits ZeroObject
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem abelian_pointwise_bound {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (t : Y) :
    ∃ d : ℕ, ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      F.IsTorsion → ∀ q : ℕ, d < q →
      IsZero ((upperStar AddCommGrpCat.{u + 1} (Y.algClosurePoint t)).obj
        (((lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj F)) := by
  let y := Y.algClosurePoint t
  let a := pullback.snd f y
  let i := pullback.fst f y
  have : IsProper a := IsProper.pullback_snd f y
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le a
  refine ⟨2 * d, fun F hF q hq ↦ ?_⟩
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let R := (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj K
  have hvan := isZero_higherDirectImage_over_algClosed
    (AlgebraicClosure (Y.residueField t)) a d hd
    ((upperStar AddCommGrpCat.{u + 1} i).obj F) (isTorsion_upperStar i hF) q hq
  have hbc := isIso_baseChange_of_isProper (IsPullback.of_hasPullback f y) K
    (torsionHomology_single F hF)
  rw [baseChange_eq_derivedBaseChangeMapPlus] at hbc
  have := hbc
  exact hvan.of_iso
    ((upperStar AddCommGrpCat.{u + 1} y).mapIso
      ((lowerStar AddCommGrpCat.{u + 1} f).homologyRightDerivedFunctorPlusObjSingleFunctorIso
        F q).symm ≪≫
    ((upperStar AddCommGrpCat.{u + 1} y).mapDerivedCategoryPlusHomologyFunctorIso q).app R ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (asIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f y).toCommSq).app K)) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((lowerStar AddCommGrpCat.{u + 1} a).rightDerivedFunctorPlus.mapIso
        (((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlusSingleFunctor 0).app F)))

private theorem abelian_higher_coproducts {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (q : ℕ) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      ((lowerStar AddCommGrpCat.{u + 1} f).rightDerived q) := by
  let U := ringAbelianForget (ULift.{u + 1} ℤ) X
  let V := ringAbelianForget (ULift.{u + 1} ℤ) Y
  let F := (lowerStar AddCommGrpCat.{u + 1} f).rightDerived q
  have : U.IsEquivalence := inferInstance
  have : PreservesColimitsOfShape (Discrete I) (U ⋙ F) :=
    preservesColimitsOfShape_of_natIso
      (ringAbelianHigherDirectImageIso (ULift.{u + 1} ℤ) f q)
  have : PreservesColimitsOfShape (Discrete I) (U.asEquivalence.functor ⋙ F) := by
    change PreservesColimitsOfShape (Discrete I) (U ⋙ F)
    infer_instance
  have : PreservesColimitsOfShape (Discrete I)
      (U.asEquivalence.inverse ⋙ U.asEquivalence.functor ⋙ F) :=
    comp_preservesColimitsOfShape _ _
  exact preservesColimitsOfShape_of_natIso (U.asEquivalence.invFunIdAssoc F)

private theorem ring_higher_coproducts
    (Λ : Type (u + 1)) [Ring Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (q : ℕ) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerived q) := by
  have := abelian_higher_coproducts f q I
  have : PreservesColimitsOfShape (Discrete I)
      ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerived q ⋙ ringAbelianForget Λ Y) :=
    preservesColimitsOfShape_of_natIso (ringAbelianHigherDirectImageIso Λ f q).symm
  have : ReflectsColimitsOfShape (Discrete I) (ringAbelianForget Λ Y) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (ringAbelianForget Λ Y)

private theorem ring_forget_torsion
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((ringAbelianForget Λ X).obj F).IsTorsion := by
  refine Sheaf.IsTorsion.of_forall_isAddTorsion fun U x ↦ ?_
  have := Fintype.ofFinite Λ
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨Fintype.card Λ, Fintype.card_pos, ?_⟩
  let y : F.obj.obj U := x
  change Fintype.card Λ • y = 0
  rw [← one_smul Λ y, ← smul_assoc, card_nsmul_eq_zero, zero_smul]

private theorem ring_forget_reflects_zero
    (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hM : IsZero ((ringAbelianForget Λ X).obj M)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).2
  apply (ringAbelianForget Λ X).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hM.eq_of_src _ _

private theorem ring_geometric_detects_zero
    (Λ : Type (u + 1)) [Ring Λ] (Y : Scheme.{u})
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hM : ∀ t : Y, IsZero
      (((ringAbelianForget Λ Y) ⋙ upperStar AddCommGrpCat.{u + 1}
        (Y.algClosurePoint t)).obj M)) : IsZero M := by
  apply ring_forget_reflects_zero Λ Y M
  let N := (ringAbelianForget Λ Y).obj M
  have hz : IsZero (0 : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) := isZero_zero _
  have : IsIso (hz.from_ N) := by
    refine isIso_of_isIso_upperStar_map_of_jointlySurjective AddCommGrpCat.{u + 1}
      (fun t ↦ Y.algClosurePoint t)
      (fun t ↦ ⟨t, IsLocalRing.closedPoint _, Scheme.algClosurePoint_base _ _ _⟩) _
      fun t ↦ ?_
    have hz' := Functor.map_isZero (upperStar AddCommGrpCat.{u + 1} (Y.algClosurePoint t)) hz
    exact ⟨⟨hz'.to_ _, (hM t).eq_of_src _ _, hz'.eq_of_src _ _⟩⟩
  exact IsZero.of_iso hz (asIso (hz.from_ N))

/-- Proper derived direct image preserves arbitrary coproducts over a finite ring.
Source: Stacks Project, Tags 0F0D, 0F11, 095U.
(blueprint: lem-sfb-finite-proper-derived-coproducts)

Proof: forgetting coefficients is exact, conservative and preserves coproducts.
Its bounded derived comparison identifies every higher direct image with the
abelian one after forgetting. Abelian higher direct images commute with coproducts
by the integer-module case. At each geometric point proper base change and the
finite-dimensional geometric fibre give a bound on higher direct images of torsion
sheaves. Finite rings make all underlying sheaves torsion, including the zero ring.
Dimension shifting with these jointly conservative geometric point functors shows
that direct image takes exact complexes of acyclic objects to exact complexes.
Coproducts of acyclic objects remain acyclic since every higher direct image
preserves coproducts. The abstract unbounded coproduct criterion applies. No uniform
bound on the dimensions of the fibres, or quasi-compactness of Y, is used. -/
theorem finiteRing_preservesCoproducts_rightDerivedLowerStar
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor := by
  choose d hd using abelian_pointwise_bound f
  refine Functor.preservesColimitsOfShape_rightDerivedFunctor_of_map_acyclic_of_rightDerived
    (lowerStar (ModuleCat.{u + 1} Λ) f) I
      (fun M hM hM' ↦ ?_) (fun n ↦ ring_higher_coproducts Λ f n I)
  refine hM.map_of_rightAcyclic_of_forall_isZero _
    (fun t : Y ↦ ringAbelianForget Λ Y ⋙
      upperStar AddCommGrpCat.{u + 1} (Y.algClosurePoint t))
    (ring_geometric_detects_zero Λ Y) d (fun t G q hq ↦ ?_) hM'
  exact (hd t ((ringAbelianForget Λ X).obj G) (ring_forget_torsion Λ X G) q hq).of_iso
    ((upperStar AddCommGrpCat.{u + 1} (Y.algClosurePoint t)).mapIso
      ((ringAbelianHigherDirectImageIso Λ f q).app G))

end AlgebraicGeometry.Etale
