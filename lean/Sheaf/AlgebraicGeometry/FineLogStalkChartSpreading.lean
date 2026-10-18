/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.GroupTheory.Finiteness
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.TraceFormula.FgCommutativeMonoidFinitePresentation
import Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks

/-!
# Spreading a specified chart of a fine log stalk

Source: Illusie--Laszlo--Orgogozo, Exposé VI, 1.1 and 3.7(a), printed pp. 69 and 75
(blueprint: lem-trf-fine-log-stalk-chart-spreading).

Fineness is expanded as étale-local charts by finitely generated integral monoids.
The conclusion preserves the specified stalk homomorphism, not merely its image
in the characteristic monoid. Neither local charts nor the given monoid must be saturated.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A specified chart of the geometric stalk of a fine log structure spreads to an
affine pointed étale neighbourhood. Source: ILO VI 1.1 and the last sentence of
3.7(a), printed pp. 69 and 75 (blueprint: lem-trf-fine-log-stalk-chart-spreading).

Proof:
1. Use a small skeleton of affine pointed étale neighbourhoods. Affine neighbourhoods
are cofinal and pointed neighbourhoods are cofiltered. Filtered colimits commute with
finite products and equalizers, so finitely many germs and equations in finitely many
sheaves spread to one common refinement. Étale neighbourhoods remain locally Noetherian
by local finite presentation and the locally-Noetherian finite-type lemma. Refinements
through a fixed pointed neighbourhood compute the same stalk and preserve its germs.
2. Choose finite generators of `P` and their finitely many defining relations, using
`fg_commutative_monoid_finite_presentation`. Represent the prescribed images of the
generators and impose those relations on a common neighbourhood. This gives a monoid
homomorphism with germ exactly `h`. By fineness, refine to a neighbourhood with a chart
from a finitely generated integral monoid `Q`, lifting the geometric point through the
étale chart cover. No saturation or freeness is used.
3. Form the log structure `N` associated to the lifted map `P → O`. Its universal
property gives a map `f : N → M`; its stalk is the given isomorphism from the pushout
of `P` with the strict-local units. Its inverse on that stalk fixes units and respects
the structure maps to the strict local ring.
4. Lift under this inverse the finitely many `Q`-generators to sections of `N`.
Impose the finitely many relations, equality of their structure-map images, and the
equations that their `f`-images are the original chart sections. This gives `Q → N`
compatible with the structure maps and with `f`.
5. The associated-log universal property for the `Q`-chart extends that map to
`g : M → N`. Uniqueness gives `fg = id`, including on the entire unit sheaf; no
finite generation of the groups of units is required.
6. At the marked stalk, `g` is the inverse of `f`, so `gf` fixes the germs of the
finitely many `P`-generators. Refine so that it fixes these sections. Generation and
the associated-log universal property give `gf = id`. Hence the lifted map is a chart.
7. Take an affine pointed refinement. Compatibility of associated log structures
with restriction preserves the chart; the canonical stalk identifications preserve
all prescribed generator germs and therefore the entire homomorphism `h`.
-/
theorem EtaleLogStructure.exists_affine_chart_of_isStalkChart
    {X : Scheme.{u}} [IsLocallyNoetherian X] (M : EtaleLogStructure X)
    (hM : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t' : Spec (.of Ω') ⟶ X),
      ∃ (V : X.Etale) (_v : (Scheme.pointSmallEtale t').fiber.obj V)
        (Q : Type u) (_ : CommMonoid Q) (q : Q →* M.monoidSheaf.obj.obj (op V)),
        Monoid.FG Q ∧
          Function.Injective (Algebra.GrothendieckGroup.of (M := Q)) ∧ M.IsChart V q)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    {P : Type u} [CommMonoid P]
    (hPfg : Monoid.FG P)
    (hPint : Function.Injective (Algebra.GrothendieckGroup.of (M := P)))
    (h : P →* M.toEtalePrelogStructure.stalk t) (hh : M.IsStalkChart t h) :
    ∃ (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
      (hW : P →* M.monoidSheaf.obj.obj (op W)),
      IsAffine W.left ∧ M.IsChart W hW ∧
        (M.toEtalePrelogStructure.germ t W w).hom.comp hW = h := by
  sorry

end AlgebraicGeometry
