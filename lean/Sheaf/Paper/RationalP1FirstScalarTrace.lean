/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.Paper.RationalP1FirstTraceData
public import Sheaf.Paper.RationalP1SectionEvaluation
public import Sheaf.Paper.RationalP1SecondPretraceData
public import Sheaf.Paper.DiagonalCoefficientReference

/-! # Scalar base change for the first projective-line trace

Source: the First identity in the current rational projective-line triangle proof.
(blueprint: lem-sfb-rational-p1-first-scalar-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] condensedAmbientPullbackComparison

/-- Base change of the normalized q trace to the first projection.

Source: current blueprint, rational projective-line triangle proof, First identity,
"The trace in epsilon becomes, under base change, Tr_p1."
(blueprint: lem-sfb-rational-p1-first-scalar-trace).

Proof: pull back the unit/Chern splitting of the completed projective-line direct
image along q. The opposite square mate preserves the unit by the adjunction
triangle and the positive Chern class by Kummer pullback. Both completed traces
are zero on the shifted unit and one on the Chern summand, so their square
commutes. Transport it through the full-unit-normalized realization squares of
reference, then the integral, rational and closure scalar squares of family.
The root-normalized secondLineComparison identifies the pulled coefficient line
with the line on the product. The canonical comparison of the derived direct
images gives firstNativeFunctional. Finally the monoidal unit comparison and
singleUnitIso convert the coefficient units to tensor units. This argument uses
only the scalar line, not an arbitrary M, its projections, or a diagonal class. -/
theorem first_scalar_trace
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (reference : Reference l Y δ family) :
    firstTraceExchange (coefficient l c).X Y
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (ProjectiveLine Y))
          0).obj (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
          0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
        (secondLineComparison l c k p hpl Y) ≫
      firstNativeFunctional (coefficient l c).X Y (line l c) (diagram l c Y family)
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
          0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
        (diagram l c Y family).trace₁ ≫
      (singleUnitIso (coefficient l c).X (ProjectiveLine Y)).hom =
    (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
      (trace (coefficient l c).X Y (line l c) (diagram l c Y family) ≫
        (singleUnitIso (coefficient l c).X Y).hom) ≫
      (secondTraceUnitIso (coefficient l c).X Y).hom := by sorry

end AlgebraicGeometry.ProEtale.RationalP1
