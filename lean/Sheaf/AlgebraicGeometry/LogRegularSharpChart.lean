/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.FineLogStalkChartSpreading
import Sheaf.TraceFormula.FsFaceSharpening

/-!
# Sharp charts for log regular fs log schemes

Source: ILO, Exposé VI, 1.6 and 3.7(a), printed pp. 70 and 75
(blueprint: lem-trf-log-regular-sharp-chart).

The chart is modeled on the actual characteristic monoid, and its characteristic
map at the distinguished point is the identity under the canonical stalk identification.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A log regular fs log scheme has an affine pointed étale chart modeled on its
sharp characteristic monoid. Source: ILO VI 1.6 and 3.7(a), printed pp. 70 and 75
(blueprint: lem-trf-log-regular-sharp-chart).

Proof plan:
1. Choose an fs chart `Q` at the point and let `F` be the face mapping to local units.
The stalk pushout identifies the characteristic with `Q_F / Fᵍᵖ`.
2. Apply `lem-trf-fs-face-sharpening`: this quotient is fs sharp and its group completion
is free of finite rank, while the units of `Q_F` are precisely `Fᵍᵖ`.
3. Lift a finite basis of the characteristic group to `Qᵍᵖ`. The resulting group section
lands on the monoid in `Q_F`, since its difference from any representative is a unit.
This splits `Q_F` as the product of the characteristic monoid with `Fᵍᵖ`.
4. Push out this splitting along `Fᵍᵖ → Aˣ`. It gives a stalk chart from the characteristic
monoid whose induced map to the characteristic quotient is the identity.
5. Apply `lem-trf-fine-log-stalk-chart-spreading` to this specified germ to obtain an
affine pointed étale chart. Étale implies locally of finite presentation and hence locally
of finite type; `pqf-lem-locnoeth-lft` (Stacks Tag 01T6) gives local Noetherianity.
-/
theorem exists_sharp_chart_of_logRegular
    (X : FineSaturatedLogScheme.{u}) (_hX : X.IsLogRegular)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme) :
    IsFineSaturatedMonoid (X.logStructure.characteristic t) ∧
      (∀ p : X.logStructure.characteristic t, IsUnit p → p = 1) ∧
      ∃ (W : X.scheme.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
        (β : X.logStructure.characteristic t →*
          X.logStructure.monoidSheaf.obj.obj (op W)),
        IsAffine W.left ∧ IsLocallyNoetherian W.left ∧
          X.logStructure.IsChart W β ∧
          ∀ p : X.logStructure.characteristic t,
            Associates.mk (X.logStructure.toEtalePrelogStructure.germ t W w (β p)) = p := by
  sorry

end AlgebraicGeometry
