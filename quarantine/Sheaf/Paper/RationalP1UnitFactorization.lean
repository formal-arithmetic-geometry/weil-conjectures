/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G9
-/
module

public import Sheaf.Paper.RationalP1AmbientComposites
public import Sheaf.Paper.RationalTatePullback

public import Sheaf.Paper.RationalP1SectionEvaluation

/-! # Factoring the normalized projective-line unit

Source: the literal ambient unit clause in the first rational projective-line triangle
calculation, before any trace functional is applied.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
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


set_option maxHeartbeats 800000 in
-- Fix the coefficient and all native endpoints before spelling out the unit paste.
/-- Factor the normalized unit into kernel insertion and the remaining inverse exchange paste.
No counit, trace functional, trace transport or integration equation occurs in this statement.

Source: current blueprint, sec-six-functors-basics/sk-prop-p1-adjunction-rational/
sk-prop-p1-adjunction-rational-triangle.proof.md, First identity, description of the unit;
unit clause 2 of the ambient formulas
(blueprint: lem-sfb-rational-p1-unit-factorization).

Proof: Open hη to obtain invertibility witnesses and its HEq with unitComponent.
Use those witnesses, through definitional equality of the fixed-arrow interfaces, as hb and hp.
Proof irrelevance identifies their uses. Replace η by the specified unit.
Expand unitComponent and diagonalClassMap.
Apply the second direct-image functor's map_comp to split the tensor-shift comparison from
the diagonal tensor comparison and the supported class. Associativity groups the section,
diagonal tensor map and class as firstKernelInsertion; the remaining three arrows are
exactly the displayed tail. This calculation holds for M = 0 and for a zero class, and
requires no assertion about the diagonal integral. -/
theorem rationalP1_unit_factorization
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (family : Family l Y)
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (η : M ⟶ (twist (coefficient l c).X (ProjectiveLine Y)
      (line l c (ProjectiveLine Y))).obj
        ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
          ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)))
    (hη : UnitComponentNormalized (coefficient l c).X Y (line l c) (diagram l c Y family)
      (secondLineComparison l c k p hpl Y) M η)
    :
    ∃ (hb : IsIso ((condensedAmbientExchange (coefficient l c).X (square Y)).app M))
    (hp : IsIso (twistProjectionMap (coefficient l c).X (secondProjection Y)
      (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
      (secondLineComparison l c k p hpl Y)
      ((moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y)).obj M))),
    η = firstKernelInsertion (coefficient l c).X Y M
      (((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X (diagonalSurface Y)) 0).obj
          (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
      (diagram l c Y family).delta ≫
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
              ((condensedAmbientExchange (coefficient l c).X (square Y)).app M) hb)) := by sorry

end AlgebraicGeometry.ProEtale.RationalP1
