/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogIdealChartPresentation
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.IntegralChartLogificationThickening
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionsGeometricGermExt
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Integral saturated stalks and sections on arbitrary fs log schemes

Source: ILO VI 1.1, printed p.69, and VIII 3.3.3--3.3.6, printed pp.106--107;
the arbitrary-scheme stalk and section assertion is the DAG's agent refinement.
(blueprint: lem-per-associated-log-arbitrary-scheme).

The log structure, charts and fs predicate are the recorded definitions, which do not
require a locally Noetherian base. Chart isomorphisms can equivalently be tested on
geometric stalks, as in `EtaleLogStructure.IsChart`; the associated-log presentation
and universal property are provided by `integralChartLogificationThickening`.
Saturation is written multiplicatively as closure under positive roots in the
canonical Grothendieck group. Neither conclusion includes finite generation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Every geometric stalk and every étale section monoid of an fs log structure on an
arbitrary scheme embeds in its group completion and is closed under positive roots there.

Source: ILO VI 1.1, p.69, and VIII 3.3.3--3.3.6, pp.106--107, for the chart conventions;
the general assertion and proof are the DAG's agent refinement.

Proof:
1. Choose a pointed étale fs chart. The stalk formula of
   [lem-per-integral-chart-logification-thickening] identifies the stalk with
   C = P ⊕_E G, where G is the strict-local ring's unit group and E is the inverse
   image of those units in P. By [lem-per-integral-monoid-unit-pushout], C embeds in
   H = (P^gp × G)/{(e,-f^gp(e)) : e ∈ E^gp}, in additive notation. The universal
   property of the pushout and group completion identifies H with C^gp. Thus C is integral.
2. If h = [(z,g)] in H and n h = [(p,v)] in C with n > 0, the quotient relation gives
   n z - p = e₁ - e₂ with e₁,e₂ ∈ E. Therefore
   n(z + e₂) = p + e₁ + (n-1)e₂ belongs to P. Saturation of the fs chart P gives
   z + e₂ ∈ P, and h = [(z+e₂,g-f(e₂))] belongs to C. This proves stalk saturation
   without any divisibility or torsion-freeness assumption on G.
3. For B = M(U), equality a+c = b+c gives equality of a and b in all geometric
   stalks by their integrality. Apply [lem-weil-pbc-sets-sections-geometric-germ-ext]
   to the underlying set sheaf to conclude a=b. The difference presentation of the
   group completion then shows B → B^gp is injective. This applies also on overlaps.
4. For g=a-b ∈ B^gp with n g ∈ B, stalk saturation gives local germs d with d+b=a.
   Use [def-weil-pbc-geometric-stalks], the cofiltered neighbourhoods of
   [lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered], and the representative and
   eventual-equality clauses of [lem-weil-pbc-filtered-colimit-sets-elementwise] to
   represent d and d+b=a on pointed étale refinements. Choose these over geometric
   points above all points of U, yielding a jointly surjective étale cover. Work on
   small models in the enlarged universe of [def-weil-size-convention]. No finite
   subcover is required.
5. On an overlap the representatives satisfy d_V+b=a=d_W+b, so section cancellation
   gives d_V=d_W. The sheaf axiom [def-weil-pbc-etale-sheaf-of-sets] glues them to a
   global d with d+b=a, hence g=d ∈ B. For empty U the empty-cover axiom makes B the
   one-element monoid, which is integral and saturated. No Noetherian condition or
   finite generation of section monoids has been used.
(blueprint: lem-per-associated-log-arbitrary-scheme). -/
theorem EtaleLogStructure.integral_saturated_of_isFineSaturated
    {X : Scheme.{u}} (M : EtaleLogStructure X) (hM : M.IsFineSaturated) :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      Function.Injective
        (Algebra.GrothendieckGroup.of (M := M.toEtalePrelogStructure.stalk x)) ∧
      ∀ (g : Algebra.GrothendieckGroup (M.toEtalePrelogStructure.stalk x))
        (n : ℕ), 0 < n →
        (∃ m : M.toEtalePrelogStructure.stalk x,
          Algebra.GrothendieckGroup.of m = g ^ n) →
        ∃ m : M.toEtalePrelogStructure.stalk x, Algebra.GrothendieckGroup.of m = g) ∧
    ∀ U : X.Etale,
      Function.Injective
        (Algebra.GrothendieckGroup.of (M := M.monoidSheaf.obj.obj (op U))) ∧
      ∀ (g : Algebra.GrothendieckGroup (M.monoidSheaf.obj.obj (op U)))
        (n : ℕ), 0 < n →
        (∃ m : M.monoidSheaf.obj.obj (op U), Algebra.GrothendieckGroup.of m = g ^ n) →
        ∃ m : M.monoidSheaf.obj.obj (op U), Algebra.GrothendieckGroup.of m = g := by
  sorry

end AlgebraicGeometry
