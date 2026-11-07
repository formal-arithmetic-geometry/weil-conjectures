/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1SectionEvaluation
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData

import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstTraceTransportCounitExpandedForDiagram
import WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstScalarTrace

/-! # Expanded counit equality for the terminal first projective-line trace

Source: the Kunneth and trace base-change calculation in the first rational projective-line
triangle identity, before the diagonal class is inserted.
(blueprint: lem-sfb-rational-p1-first-trace-transport-counit-expanded).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] unitComponent counitComponent twistProjectionMap
attribute [local irreducible] coefficient line diagram secondLineComparison
attribute [local irreducible] moduleObjectDerivedPushforward moduleObjectDerivedPullback
attribute [local irreducible] twist projectionMap singleUnitIso
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] condensedAmbientExchange

-- Keep the fixed geometric coefficient and derived interfaces folded during elaboration.
/-- Expand the normalized counit into its projection and trace factors.
This is the counit-expansion step of the terminal first-trace transport proof.
This core equation has source Rq_*Rp₂*(p₁*M tensor T_W), rather than Rq_*M, and contains
neither a diagonal class insertion nor a unit component.

Source: current blueprint, sec-six-functors-basics/sk-prop-p1-adjunction-rational/
sk-prop-p1-adjunction-rational-triangle.proof.md, First identity, trace and path change
(blueprint: lem-sfb-rational-p1-first-trace-transport-counit-expanded).

Proof: this obligation is split from the parent theorem. Expand `counitComponent` using its
projection part, trace, and right-unitor factors; the remaining Kunneth and scalar
transport calculation is the parent obligation.
Expand the twisted projection and counit and cancel the native tensor-shift
comparisons. Apply the two Kunneth factorizations to M and the shifted Tate coefficient.
They identify the inverse exchange/projection composite followed by the q trace with
the first direct-image path followed by the inverse first projection and its trace.
For this step the trace square is obtained by pulling back the normalized unit/Chern
splitting defining the completed trace: the canonical base-change mate preserves the
unit summand by the adjunction triangle, and the positive Chern summand by Cartier/Kummer
pullback. Projection to that summand gives the completed trace square. The full-unit
squares in reference identify its traces with the Z_l member of family. The fixed scalar
squares of family transport the square to the selected rational or closure coefficient.
The exchange/tensor coherence and module/ringed-topos comparison identify these maps
with the literal native maps here. Properness and the localizing projection formula
supply invertibility of the first projection on M and the shifted Tate object; this
proof is the existential witness h₁. Uniqueness of conjugate right adjoints identifies
the path change with firstPathComparison. This argument never inserts delta and never
uses either integration identity. It remains valid for M = 0 and for a zero diagonal
class whenever a reference exists. -/
theorem rationalP1_first_trace_transport_counit_expanded
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
    (family : Family l Y) (reference : Reference l Y δ family)
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (hM : CategoryTheory.localizingClosure
      (constantModelBoundedConstructible (coefficient l c).X (ProjectiveLine Y)) M)
    (hq : IsIso (projectionMap (coefficient l c).X (ProjectiveLine Y ↘ Y)
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
          (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧)))
    (hb : IsIso ((condensedAmbientExchange (coefficient l c).X (square Y)).app M))
    (hp : IsIso (twistProjectionMap (coefficient l c).X (secondProjection Y)
      (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
      (secondLineComparison l c k p hpl Y)
      ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)))
    (h₁ : IsIso (projectionMap (coefficient l c).X (firstProjection Y) M
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
          (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧))) :
    (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
      (X := (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
              (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
      ((moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).map
        (X := ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M ⊗
          (((DerivedCategory.singleFunctor
            (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
              (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)))
          (tensorShiftIso (coefficient l c).X (diagonalSurface Y)
            (line l c (diagonalSurface Y))
            ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)).hom ≫
        @inv _ _ _ _ (twistProjectionMap (coefficient l c).X (secondProjection Y)
          (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
          (secondLineComparison l c k p hpl Y)
          ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M)) hp ≫
        (twist (coefficient l c).X (ProjectiveLine Y)
          (line l c (ProjectiveLine Y))).map
          (by
            unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
            exact @inv _ _ _ _
              ((condensedAmbientExchange (coefficient l c).X (square Y)).app M) hb)) ≫
      counitProjectionPart (coefficient l c).X Y (line l c (ProjectiveLine Y))
        ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M) hq ≫
      ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M ◁
        (trace (coefficient l c).X Y (line l c) (diagram l c Y family) ≫
          (singleUnitIso (coefficient l c).X Y).hom)) ≫
      (ρ_ ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)).hom =
    firstTerminalFunctional (coefficient l c).X Y (line l c) (diagram l c Y family) M
      (((DerivedCategory.singleFunctor
          (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
            (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
      (diagram l c Y family).trace₁ h₁ := by
  let _ := reference
  let _ := hM
  exact rationalP1_first_trace_transport_counit_expanded_for_diagram l c k p hpl Y
    (diagram l c Y family) M hq hb hp h₁
    (first_scalar_trace l c k p hpl Y δ family reference)

end AlgebraicGeometry.ProEtale.RationalP1
