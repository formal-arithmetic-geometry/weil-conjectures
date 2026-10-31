/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullback

/-! # Separate class and trace equations for fixed pullback endpoints

Source: diagonal coefficient changes, paragraph (3), the class and trace squares.
(blueprint: def-diagonal-pullback-squares).

The small proposition wrappers keep concrete coefficient constructions out of
elaboration of the derived equation types. They contain exactly the published
fields of PullbackCompatibility and add no mathematical assumptions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
  (L : ∀ X : Scheme.{u}, Modules R X) (d : Diagram R Y L) (d' : Diagram R Y' L)
  (mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
    (L (ProjectiveLine Y')).X)
  (mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
    (L (diagonalSurface Y')).X)
  (s : SourcePullback R g L mP mW)

/-- Just the diagonal class equation for fixed ordinary pullback data.
Source: blueprint diagonal coefficient changes, paragraph (3).
(blueprint: def-diagonal-pullback-squares). -/
structure ClassPullbackSquare : Prop where
  comm :
      (derivedUpper
          R (baseW g)).map
          d.delta ≫ s.endpoints.lineW.shift =
        (singlePullback
          R
          (baseW g) (source _ Y)).hom ≫
          (DerivedCategory.singleFunctor
            (Modules R
              (diagonalSurface Y')) 0).map s.supported.hom ≫ d'.delta

/-- Just the three canonical trace squares for fixed ordinary pullback data,
including exchange invertibility on their specified lines.
Source: blueprint diagonal coefficient changes, paragraph (3).
(blueprint: def-diagonal-pullback-squares). -/
structure TracePullbackSquares : Prop where
  q :
      TracePullback
        R
        (ProjectiveLine Y ↘ Y) (ProjectiveLine Y' ↘ Y')
        (baseP g) g (ProjectiveSpace.map_over (ULift.{u} (Fin 2)) g).symm
        d.Rq d'.Rq d.q_canonical d'.q_canonical
        s.endpoints.lineP s.endpoints.cY d.traceq d'.traceq
  p₁ :
      TracePullback
        R
        (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
        (pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
        (baseW g) (baseP g) s.geometry.first_square
        d.R₁ d'.R₁ d.p₁_canonical d'.p₁_canonical
        s.endpoints.lineW s.endpoints.cP d.trace₁ d'.trace₁
  p₂ :
      TracePullback
        R
        (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
        (pullback.snd (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
        (baseW g) (baseP g) s.geometry.second_square
        d.R₂ d'.R₂ d.p₂_canonical d'.p₂_canonical
        s.endpoints.lineW s.endpoints.cP d.trace₂ d'.trace₂

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
