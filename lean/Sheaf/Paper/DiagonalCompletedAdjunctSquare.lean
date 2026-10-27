/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.Paper.DiagonalUniformizerAdjunctConditions
public import Sheaf.Paper.DiagonalCoefficientUnitPush

/-! # The completed first square for a normalized Chern adjunct

Source: diagonal tower coefficient changes (1), passage from the canonical model to
completed coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint derivedScalars RestrictionSquare.mate
  CompletedRealization.singleUnit CompletedRealization.shiftedLine
  FiniteRealization.derivedUnit

/-- Realizing the normalized completed adjunct gives the condensed adjunct of the local arrow.
Source: diagonal tower coefficient changes (1), and diagonal tower trace proof (1).
(blueprint: lem-diagonal-completed-adjunct-square).

Proof: the model identity makes its Picard pullback O(1). The coefficient-one
normalization identifies the coefficient pullback unit with the canonical unit.
The varying ordinary section equation and full derived-unit normalization transport
model.chernAdjoint to the strict constant-coefficient system. Naturality of the
constant-system/limit adjunction and the limit-square normalization show that the
completed adjunct of z has exactly the sourceMap equation defining c. Restriction
on complete objects is fully faithful; the unit, shifted root line and its direct
image are complete, so that equation identifies the two completed arrows. Finally
apply the normalized completed realization square and its ordinary unit equation.
Only this first realization is involved: there is no integral extension, quotient,
finite realization, finite Kummer class or trace identity in this conclusion. The
argument also applies on the empty scheme. -/
theorem completed_adjunct_square
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    (s : UniformizerChernNormalizationData l Y) (p : NormalizedAdjunctPair l Y s) :
    let uP := (s.completedP.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso s.completedP.unitIso
    s.completedY.F.mapDerivedCategory.map p.c ≫
        (s.q_square.derived.iso.hom.app _ ≫
          s.zl.Rq.R.map (s.completedP.shiftedLine l (ProjectiveLine Y))) =
      s.completedY.singleUnit l Y ≫
        (coefficientUnitPush _ Y s.zl.Rq ≫ s.zl.Rq.R.map
          ((uP.inv ≫ s.completedP.F.mapDerivedCategory.map p.z) ≫
            s.completedP.shiftedLine l (ProjectiveLine Y))) := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
