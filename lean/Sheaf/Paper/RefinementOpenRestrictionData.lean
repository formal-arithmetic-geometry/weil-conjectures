module

public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison

/-! A natural transformation with the specified refinement-restriction components. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurCompactSupport

variable (R : Coefficients.{u})
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
  (hi : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
    (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))

/--
Source: Stacks 0F7B and 0F7I, the restriction-to-open and proper-base-change
construction.  The componentwise proper restriction maps are natural in the
unbounded derived module category.  This is the component-construction part of
`lem-sf-refinement-open-restriction`; invertibility and shift compatibility are
recorded separately.
(blueprint: lem-sf-refinement-open-restriction-data).
-/
theorem refinementRestriction_data :
    ∃ θ : ((openExtension R c.i).mapDerivedCategory ⋙ push R r.hom) ⋙ pull R d.i ⟶
        (openExtension R c.i).mapDerivedCategory ⋙ pull R c.i,
      ∀ M, θ.app M = refinementRestriction R r hi M := by
  sorry

end WeilConjectures.PurCompactSupport
