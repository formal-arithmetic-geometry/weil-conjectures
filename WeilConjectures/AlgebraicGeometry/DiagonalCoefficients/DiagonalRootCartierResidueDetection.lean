/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassRootLimitProjection
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalFiniteCartierEndomorphismDetection
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalPulledFiniteCartierCoordinates
import all Mathlib.Logic.Small.Defs
import WeilConjectures.CategoryTheory.EvaluatedClassMapDetection

/-! # Detection of root maps by the finite diagonal Cartier classes

Source: diagonal coefficient changes, paragraph (3). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor diagonalCompletedSource

variable {l : ℕ} [Fact l.Prime] {Y Y' : Scheme.{u}} {g : Y' ⟶ Y}
  [DiagonalTraceLocalizations l (diagonalSurface Y)]
  [DiagonalTraceLocalizations l (diagonalSurface Y')]
  {hY : IsUnit (l : Γ(Y, ⊤))} {hY' : IsUnit (l : Γ(Y', ⊤))}
  {D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))}
  {D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y'))}
  {d : ClassLimitPresentation l Y hY D} {d' : ClassLimitPresentation l Y' hY' D'}
  {e : CompletedRealization l (diagonalSurface Y)}
  {e' : CompletedRealization l (diagonalSurface Y')}

-- The chosen derived models and the two evaluated single comparisons need extra elaboration.
set_option maxHeartbeats 2000000 in
-- The coordinate detector expands several derived-category comparisons; retain the larger budget.
/-- Equality after the finite positive supported Cartier classes forces equality
of the ordinary root maps after restriction to the diagonal.
Source: diagonal coefficient changes (3), positive Kummer normalization.
(blueprint: lem-diagonal-root-cartier-residue-detection).

Proof: at each index put the evaluated pulled class in canonical finite Cartier
coordinates. The target presentation's finite normalization identifies its roots
object with the same finite roots line. Exact-single and shift naturality turn
the assumed equality into equality of postcompositions of the canonical class.
Finite Cartier endomorphism detection and cancellation of the coordinates give
equality of the evaluated ordinary maps. Natural-transformation extensionality
gives equality of the tower maps, hence of their diagonal restrictions.
The coordinate and finite etale residue calculations are separate geometric
steps; the categorical assembly does not assume faithfulness on derived arrows. -/
theorem diagonalRootCartierResidueDetection
    (h k : (diagonalClassTowerPull l (baseW g)).obj d.H ⟶ d'.H)
    (heq : ∀ n : ℕ,
      let G := (diagonalClassTowerPull l (baseW g)).mapDerivedCategory
      let V := (evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y'))).obj (op n)
      V.mapDerivedCategory.map
        (G.map d.c.hom ≫
          (G.commShiftIso (2 : ℤ)).hom.app ((DerivedCategory.singleFunctor _ 0).obj d.H) ≫
          (((diagonalClassTowerPull l (baseW g)).mapDerivedCategorySingleFunctor 0).hom.app
            d.H ≫ (DerivedCategory.singleFunctor _ 0).map h)⟦(2 : ℤ)⟧') =
        V.mapDerivedCategory.map
          (G.map d.c.hom ≫
            (G.commShiftIso (2 : ℤ)).hom.app ((DerivedCategory.singleFunctor _ 0).obj d.H) ≫
            (((diagonalClassTowerPull l (baseW g)).mapDerivedCategorySingleFunctor 0).hom.app
              d.H ≫ (DerivedCategory.singleFunctor _ 0).map k)⟦(2 : ℤ)⟧')) :
    Functor.whiskerRight h
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (diagonalImmersion Y')) =
      Functor.whiskerRight k
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (diagonalImmersion Y')) := by
  have hh : h = k := by
    apply NatTrans.ext
    funext n
    let F := diagonalClassTowerPull l (baseW g)
    let G := F.mapDerivedCategory
    let V := (evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y'))).obj (op n.unop)
    obtain ⟨s, t, ht⟩ := diagonalPulledFiniteCartier_coordinates g hY' d n.unop
    have hn := d'.finite_normalization
    unfold FiniteCartierNormalization diagonalFiniteCycleNormalization at hn
    obtain ⟨_, v, _, _, _⟩ := hn n.unop
    have he := heq n.unop
    apply Functor.detect_evaluated_single_maps V
      (G.map d.c.hom ≫
        (G.commShiftIso (2 : ℤ)).hom.app ((DerivedCategory.singleFunctor _ 0).obj d.H) ≫
        (((F.mapDerivedCategorySingleFunctor 0).hom.app d.H)⟦(2 : ℤ)⟧'))
      s t v (finiteCartierClass l Y' hY' n.unop).hom ht
      (finiteCartierClass_endomorphism_injective l Y' hY' n.unop) h k
    simpa only [F, G, V, Functor.map_comp, Category.assoc] using he
  exact congrArg (fun f ↦ Functor.whiskerRight f
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) (diagonalImmersion Y'))) hh

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
