/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations
import WeilConjectures.DeligneLaumon.CondensedScalarPullback
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Étale descent of pulled-back scalar cokernels -/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.LisseQlbar

/-- Scalar cokernels with étale origins commute with inverse image.
Source: blueprint `thm-lisse-qlbar-representations`, normalized finite quotients.
(blueprint: lem-dl-a1-condensed-scalar-cokernel-pullback).

Proof: the coefficient isomorphism identifies pullback of scalar multiplication
with scalar multiplication on the pulled module. Inverse image preserves the
cokernel colimit. Uniqueness of cokernels gives the comparison of pro-étale
objects; the étale/pro-étale comparison commutes with inverse image and is fully
faithful, so that comparison descends to an isomorphism of étale abelian sheaves. -/
theorem scalar_cokernel_pullback_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U C : Scheme.{u}} (j : U ⟶ C)
    (a : condensedScalarRing Λ)
    (N : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1}) (condensedRingObj Λ C))
    (FC : Sheaf C.smallEtaleTopology Ab.{u + 1})
    (FU : Sheaf U.smallEtaleTopology Ab.{u + 1})
    (qC : N.X ⟶ (comparisonUpperStar Ab.{u + 1} C).obj FC)
    (qU : ((CondensedRing.upperStar Λ j).obj N).X ⟶
      (comparisonUpperStar Ab.{u + 1} U).obj FU)
    (hC : scalarEnd Λ C a N ≫ qC = 0)
    (hU : scalarEnd Λ U a ((CondensedRing.upperStar Λ j).obj N) ≫ qU = 0)
    (cC : IsColimit (CokernelCofork.ofπ qC hC))
    (cU : IsColimit (CokernelCofork.ofπ qU hU)) :
    Nonempty (FU ≅ (Etale.upperStar Ab.{u + 1} j).obj FC) := by
  let F := ProEtale.upperStar Ab.{u + 1} j
  let T := (F.mapMod (condensedRingObj Λ C)).obj N
  let e := (Mod.forget _).mapIso
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ j)).app T)
  let α : Arrow.mk (scalarEnd Λ U a ((CondensedRing.upperStar Λ j).obj N)) ≅
      Arrow.mk (F.map (scalarEnd Λ C a N)) :=
    Arrow.isoMk e e (scalarEnd_pullback Λ j a N).symm
  let β := CokernelCofork.mapIsoOfIsColimit cU
    ((CokernelCofork.ofπ qC hC).mapIsColimit cC F) α
  let γ : (comparisonUpperStar Ab.{u + 1} U).obj FU ≅
      (comparisonUpperStar Ab.{u + 1} U).obj ((Etale.upperStar Ab.{u + 1} j).obj FC) :=
    β ≪≫ (comparisonUpperStarUpperStarIso Ab.{u + 1} j).app FC
  exact ⟨(comparisonUpperStar Ab.{u + 1} U).preimageIso γ⟩

end AlgebraicGeometry.ProEtale.LisseQlbar
