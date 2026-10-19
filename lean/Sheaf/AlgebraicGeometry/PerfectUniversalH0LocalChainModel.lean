/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel
import Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Local chain models for the lowest truncation arrow

Source: Stacks Project, Tags 0BDL, 0BCD, 0EWY and 08CR.
(blueprint: lem-sc-perfect-universal-h0-local-chain-model).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem bottom_component_isIso
    {C : Type*} [Category C] [Abelian C]
    {A B : CochainComplex C ℤ} (α : A ⟶ B)
    (hfA : (A.sc 0).f = 0) (hgA : (A.sc 0).g = 0)
    (hfB : (B.sc 0).f = 0) (hgB : (B.sc 0).g = 0)
    (hα : IsIso (HomologicalComplex.homologyMap α 0)) : IsIso (α.f 0) := by
  let φ := (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map α
  change IsIso (ShortComplex.homologyMap φ) at hα
  have hfac :=
    (ShortComplex.LeftHomologyMapData.ofZeros φ hfA hgA hfB hgB).homologyMap_eq
  let eA := (ShortComplex.LeftHomologyData.ofZeros (A.sc 0) hfA hgA).homologyIso
  let eB := (ShortComplex.LeftHomologyData.ofZeros (B.sc 0) hfB hgB).homologyIso
  have heq : α.f 0 = eA.inv ≫ ShortComplex.homologyMap φ ≫ eB.hom := by
    rw [hfac]
    simp [eA, eB, ShortComplex.LeftHomologyMapData.ofZeros, φ]
  rw [heq]
  infer_instance


set_option maxHeartbeats 400000 in
-- The composed derived restriction and homology comparisons need extra unfolding.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified truncation arrow admits a finite-free local chain representative
with no negative terms, zero outgoing differential in degree zero, and invertible
component in degree zero.

Source: Stacks Project, Tag 0BDL, matrix-chart argument; Tags 0BCD, 0EWY, 08CR.
(blueprint: lem-sc-perfect-universal-h0-local-chain-model).

Proof: At s choose the universal rank-r neighbourhood and test its condition on
Spec kappa(s). Use the finite-free residue model of 0BCD and shrink its affine
neighbourhood into that neighbourhood. Negative fibre cohomology vanishes, so
all negative terms of the residue model vanish; the first term has rank r.
The identity test gives a rank-r locally free kernel of its first differential.
Shrink again to trivialize the kernel. Its inclusion into the first term is an
injective square matrix. The transpose is injective by 0EWY, equivalently the
dual of the cokernel vanishes. Each coordinate of the outgoing differential
factors through that cokernel, hence is zero. This argument does not require a
reduced base. The isomorphism H0(a) identifies M locally with that kernel, so
M is finite free on a further affine neighbourhood. Represent M[0] by its
single finite-free complex A and K by the model B. The affine perfect map
representative theorem (08CR) represents the conjugate of the restricted a by
an actual chain map alpha. Since both incoming and outgoing differentials at
zero vanish, H0(alpha) is alpha.f 0, so the latter is invertible. The chosen
object identifications give the stated square in the derived category.
For rank zero these are zero first terms; an empty scheme has no points. -/
theorem perfect_universalH0_local_chain_model
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (K : schemeDerivedCategory S) (hK : IsPerfect S K)
    (hnegative : ∀ (Y : Scheme.{u}) (k : Y ⟶ S) (i : ℤ), i < 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj
          ((derivedPullback k).obj K)))
    (hloc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ r : ℕ,
      ∀ (Y : Scheme.{u}) (k : Y ⟶ U.toScheme),
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((derivedPullback (k ≫ U.ι)).obj K)) r)
    (M : S.Modules)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj M ⟶ K)
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map a))
    (s : S) :
    ∃ U : S.Opens, s ∈ U ∧
      ∃ A B : CochainComplex
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ,
        IsStrictlyPerfect S U A ∧ IsStrictlyPerfect S U B ∧
        (∀ i : ℤ, i ≠ 0 → IsZero (A.X i)) ∧
        (∀ i : ℤ, i < 0 → IsZero (B.X i)) ∧ B.d 0 1 = 0 ∧
        ∃ α : A ⟶ B, IsIso (α.f 0) ∧
          ∃ (eA : (SheafOfModules.overFunctor.{u}
                (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj M) ≅
                DerivedCategory.Q.obj A)
            (eB : (SheafOfModules.overFunctor.{u}
                (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj K ≅
                DerivedCategory.Q.obj B),
            (SheafOfModules.overFunctor.{u}
              (moduleRings S.toRingedSpace) U).mapDerivedCategory.map a ≫ eB.hom =
                eA.hom ≫ DerivedCategory.Q.map α := by
  classical
  obtain ⟨U, hsU, hU, B, hB, hBnegative, hBzero, ⟨eB⟩⟩ :=
    perfect_universalH0_bottom_model S K hK hnegative hloc s
  let C := SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)
  let F := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
  let H := DerivedCategory.homologyFunctor C 0
  have hrestriction : IsIso (H.map (F.mapDerivedCategory.map a)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso 0) a).1
      (by dsimp; infer_instance)
  have hfB : (B.sc 0).f = 0 := by
    change B.d ((ComplexShape.up ℤ).prev 0) 0 = 0
    rw [(ComplexShape.up ℤ).prev_eq' (by decide : (-1 : ℤ) + 1 = 0)]
    exact (hBnegative (-1) (by decide)).eq_of_src _ _
  have hgB : (B.sc 0).g = 0 := by
    change B.d 0 ((ComplexShape.up ℤ).next 0) = 0
    rw [(ComplexShape.up ℤ).next_eq' (by decide : (0 : ℤ) + 1 = 1)]
    exact hBzero
  -- Restriction is exact, and the bottom homology of B is its degree-zero term.
  let eM : F.obj M ≅ B.X 0 :=
    (F.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).app M)).symm ≪≫
    (F.mapDerivedCategoryHomologyFunctorIso 0).app _ ≪≫
    asIso (H.map (F.mapDerivedCategory.map a)) ≪≫ H.mapIso eB ≪≫
    (DerivedCategory.homologyFunctorFactors C 0).app B ≪≫
    (ShortComplex.HomologyData.ofZeros (B.sc 0) hfB hgB).left.homologyIso
  let A := (HomologicalComplex.single C (.up ℤ) 0).obj (B.X 0)
  have hAzero : ∀ i : ℤ, i ≠ 0 → IsZero (A.X i) :=
    fun i hi ↦ HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
  have hA : IsStrictlyPerfect S U A := by
    refine ⟨⟨0, 0, fun i hi ↦ hAzero i (by omega)⟩, ?_⟩
    intro i
    by_cases hi : i = 0
    · subst i
      obtain ⟨r, ι, π, hιπ⟩ := hB.2 0
      let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 (B.X 0)
      exact ⟨r, e.hom ≫ ι, π ≫ e.inv, by
        calc
          _ = e.hom ≫ (ι ≫ π) ≫ e.inv := by simp [Category.assoc]
          _ = _ := by rw [hιπ]; simp; rfl⟩
    · refine ⟨0, 0, 0, ?_⟩
      exact (hAzero i hi).eq_of_src _ _
  let eA : F.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj M) ≅
        DerivedCategory.Q.obj A :=
    (F.mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor C 0).mapIso eM ≪≫
      (DerivedCategory.singleFunctorIsoCompQ C 0).app (B.X 0)
  -- Represent the specified arrow after conjugating by the endpoint identifications.
  let f := eA.inv ≫ F.mapDerivedCategory.map a ≫ eB.hom
  obtain ⟨α, hα⟩ := perfect_affine_map_representative S U hU A B hA hB f
  have hf : IsIso (H.map f) := by
    dsimp [f]
    simp only [Functor.map_comp]
    infer_instance
  have hHα : IsIso (HomologicalComplex.homologyMap α 0) := by
    have : IsIso (H.map (DerivedCategory.Q.map α)) := by rw [hα]; exact hf
    exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors C 0) α).1 this
  have hfA : (A.sc 0).f = 0 := by simp [A, HomologicalComplex.sc]
  have hgA : (A.sc 0).g = 0 := by simp [A, HomologicalComplex.sc]
  have hα0 : IsIso (α.f 0) := bottom_component_isIso α hfA hgA hfB hgB hHα
  refine ⟨U, hsU, A, B, hA, hB, hAzero, hBnegative, hBzero, α, hα0, eA, eB, ?_⟩
  rw [hα]
  simp [f]
  rfl

end AlgebraicGeometry.Scheme
