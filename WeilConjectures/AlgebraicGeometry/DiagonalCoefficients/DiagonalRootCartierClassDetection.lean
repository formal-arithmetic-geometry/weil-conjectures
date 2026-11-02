/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassRootLimitProjection
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalRootCartierResidueDetection
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalRootTowerRigidity

/-! # Detection of root maps by the finite diagonal Cartier classes

Source: diagonal coefficient changes, paragraph (3). -/
@[expose] public noncomputable section
set_option autoImplicit false
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

/-- Positive finite diagonal classes detect ordinary maps between root towers.
Source: diagonal coefficient changes, paragraph (3), positive residue and
connected geometric fibres of the product of projective lines.
(blueprint: lem-diagonal-root-cartier-class-detection).

Proof: at each n use the given finite Cartier normalizations to identify the
source with the supported residue constant sheaf and the root endpoint with
the residue Tate line. Forgetting finite scalars is fully faithful on the
ordinary killed module sheaves, so the two ordinary maps are maps between
etale-origin rank-one root lines. Pullback of the diagonal class is the
positive supported class of the base-changed diagonal. Equality after
postcomposition with this class forces equality on the diagonal: on a regular
relative chart t=a-b the pole generator t^(-1) has residue +1. After a geometric
base change this residue generates the cyclic coefficient module, so the
difference of the two maps has zero scalar there. Rank-one endomorphisms are
locally constant. Projection onto the first projective line has geometrically
connected fibres and the diagonal is a section, so restriction to that section
detects these etale-origin maps. Consequently the maps agree at n. Finally
natural-transformation extensionality identifies the ordinary tower maps.
This uses conservativity on etale-origin sheaves only, not geometric-point
conservativity on all pro-etale sheaves, and applies to empty bases and n=0. -/
theorem diagonalRootCartierClassDetection
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
    h = k := by
  apply diagonalPulledRootTower_restriction_injective l (baseW g) hY hY'
    d.H d'.H d.roots d'.roots
  exact diagonalRootCartierResidueDetection h k heq

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
