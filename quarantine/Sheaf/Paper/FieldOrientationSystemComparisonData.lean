/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H6
-/
module

public import Sheaf.Paper.FieldOrientationSystemHeart

/-! Normalized scalar comparisons of tower orientations. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.FieldOrientationSystem
open FieldShriekSystem FieldExceptionalSystem

variable (P : PurityFiniteSetting.{u}) (D : Models P)

variable {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (p : Z ⟶ Y) [IsProper p]
  (b : FieldShriekSystem.Laws P D (SpTowerGamma.factorization j p))
  (a : Domains P D (SpTowerGamma.factorization j p))
  (A : Adjoints P D (SpTowerGamma.factorization j p) b a)

/-- Whole-system coefficient comparisons and their finite diagonal orientation squares.

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2), comparison
of rank-one tower orientations; parent node steps 1--4.
(blueprint: new-sp-field-orientation-comparison-data).

Proof:
The quotient inclusions define the coefficient-unit comparison by multiplication.
On the Tate line use extension of the scalar coefficient with the identity on roots;
tensor d copies in their prescribed order and commute with the even shift. Finite
free extension on whole strict systems is exact, so these maps and their inverses
assemble in the abelian category and induce the displayed derived isomorphisms.
The ordinary tensor formulas and the canonical evaluation comparisons prove
IsUnitComparison and IsLineComparison, including n=0 and ramified field extensions.
The coefficient unit is constructible and has Tor amplitude [0,0]. Apply finite
reduction-compatibilities clause (3) at this unit, using finite-orientation-reduction
to identify the general-ring purity arrow with the specified diagonal/DNC arrow.
The normalized whole-system exceptional comparison is the counit transpose; evaluate
its defining counit equation using b.scalarEvaluation and A.counit. Uniqueness of the
finite transpose identifies it with the finite exceptional coefficient comparison.
Consequently the two sides of the asserted square agree at every positive level.
This is the finite equation for the actual already constructed tower arrows;
the conversion to their equality in the tower derived category is deliberately
left to the parent theorem's shifted-heart detection argument.
-/
theorem field_orientation_comparison_data
    [IsNoetherian X]
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))] [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [(j ≫ p).IsOver (Spec (.of P.field.k))] [IsSeparated (j ≫ p)]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    {E F : Index P} (hEF : E ≤ F)
    (wE : Coordinates P D E X) (wF : Coordinates P D F X)
    (vE : Coordinates P D E Y) (vF : Coordinates P D F Y)
    (hE : normalized P D E Y (SpTowerGamma.unit P.coefficients.l E.val Y))
    (hF : normalized P D F Y (SpTowerGamma.unit P.coefficients.l F.val Y))
    (oE : line P D wE d ≅ omega P D j p b a A E hE)
    (oF : line P D wF d ≅ omega P D j p b a A F hF)
    (hoE : IsOrientation P D j p b a A E d wE vE hE oE.hom)
    (hoF : IsOrientation P D j p b a A F d wF vF hF oF.hom) :
    ∃ (q : (D.scalars E F hEF Y).T.obj
        (SpTowerGamma.unit P.coefficients.l E.val Y) ≅
          SpTowerGamma.unit P.coefficients.l F.val Y)
      (t : (D.scalars E F hEF X).T.obj (line P D wE d) ≅ line P D wF d),
      IsUnitComparison P D j p b hEF vE vF q.hom ∧
      IsLineComparison P D j p b hEF wE wF d t.hom ∧
      ∀ n : ℕ,
        (SpTowerShriek.Ev P.coefficients.l F.val X n).map
          ((D.scalars E F hEF X).T.map oE.hom ≫
            (component P D (SpTowerGamma.factorization j p) b a A hEF
              (coefficientUnit P D E Y hE)).hom ≫
            ((A.right F).map (ObjectProperty.homMk
              (Y := coefficientUnit P D F Y hF) q.hom)).hom) =
          (SpTowerShriek.Ev P.coefficients.l F.val X n).map (t.hom ≫ oF.hom) := by
  sorry

end AlgebraicGeometry.ProEtale.FieldOrientationSystem
