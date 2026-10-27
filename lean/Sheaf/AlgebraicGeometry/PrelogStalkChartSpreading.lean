/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AssociatedLogArbitraryScheme
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import Sheaf.TraceFormula.FgCommutativeMonoidFinitePresentation
import Sheaf.AlgebraicGeometry.IntegralChartLogificationThickening

/-!+# Spreading prelog homomorphisms and prescribed stalk charts

Source: ILO VI 1.1, printed p.69; VI 3.7(a), printed p.75; VIII 3.3.4,
printed p.107; Kato (1988), section 2. The arbitrary-scheme generalization is
the DAG's finite-presentation argument, rather than a claim that ILO removes
its standing Noetherian convention.
(blueprint: lem-per-prelog-stalk-chart-spreading).

The finite simultaneous clause includes empty lists and homomorphisms on distinct
pointed neighbourhoods. Its restriction maps are the actual sheaf restriction maps.
`IsStalkChart` is the canonical pushout-isomorphism condition, and `IsChart` tests
this on every geometric stalk of the neighbourhood. A chart by the fixed monoid
`B`, when `B` is fine saturated, is precisely an fs chart; no different chart
monoid is substituted.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Homomorphisms from a finitely generated commutative monoid, their equalities,
and a prescribed integral stalk chart spread on an arbitrary scheme.

Source: ILO VI 1.1, p.69; VI 3.7(a), p.75; VIII 3.3.4, p.107;
Kato (1988), section 2. The non-Noetherian refinement follows the DAG argument.

Proof:
1. On the small pointed-neighbourhood category of `def-weil-size-convention`,
   `def-weil-pbc-geometric-stalks` is the colimit of sections. The category is
   cofiltered by `lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`.
   By `lem-weil-pbc-filtered-colimit-sets-elementwise`, every germ has a
   representative and equality of two germs holds on a refinement. For sections
   on the same object use its third clause, giving the same restriction arrow.
   Repeated refinements handle finite lists and preserve a specified initial
   neighbourhood. The restriction and germ identifications of
   `lem-weil-pbc-sets-etale-inverse-image-restriction` and
   `lem-weil-pbc-sets-etale-inverse-image-stalk-germ` respect monoid operations.
2. Choose finite generators of `B` and use
   `lem-trf-fg-commutative-monoid-finite-presentation` for finitely many relations.
   Represent the generator images on one neighbourhood, and impose these
   relations by Step 1. The presentation descends the generator assignment to a
   homomorphism with the specified germ. No integrality is needed here.
3. Equal germs of homomorphisms give equal germs on every generator. Impose
   those finitely many equalities on one refinement and use generation. Apply
   Steps 1--2 finitely often to obtain one common neighbourhood for all choices
   and equalities. Empty lists and the trivial monoid need no equations.
4. For an integral `B` and a stalk chart `c`, lift `c` by Step 2. By
   `lem-per-integral-chart-logification-thickening`, its associated log structure
   `N` is fine integral and has a canonical map `f : N → M` whose stalk is the
   stipulated pushout isomorphism. By `lem-per-associated-log-arbitrary-scheme`
   and `lem-weil-pbc-etale-cover-geometric-point-lift`, pass to a pointed member
   of an fs chart cover of `M`. The restriction clause for associated logs
   preserves `N`, its chart and every specified germ.
5. Write `q : Q → M` for this fine chart. Apply Step 2 to the sheaf `N` to
   lift `f_stalk⁻¹ q_stalk` to `k : Q → N`, and Step 3 to impose `f k = q`.
   Compatibility with structure maps and the associated-log universal property
   extend `k` to `g : M → N`. Uniqueness on the `Q`-chart gives `f g = id`.
   On the marked stalk, `g_stalk` is therefore the inverse of `f_stalk`.
6. Apply Step 3 to `g f` and the identity on the `B`-chart of `N`. After one
   refinement they agree on that chart. The same universal property gives
   `g f = id`, so `f` is an isomorphism and the specified lift is a chart.
   When `B` is fine saturated this very chart is an fs chart. Only finite
   presentations of `B` and `Q` were used, with no Noetherian hypothesis and
   no finite generation of section monoids or of unit groups.
(blueprint: lem-per-prelog-stalk-chart-spreading). -/
theorem EtaleLogStructure.prelog_stalk_chart_spreading
    {X : Scheme.{u}} (M : EtaleLogStructure X) (hM : M.IsFineSaturated)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (B : Type u) [CommMonoid B] (hB : Monoid.FG B) :
    (∀ c : B →* M.toEtalePrelogStructure.stalk t,
      ∃ (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
        (cW : B →* M.monoidSheaf.obj.obj (op W)),
        (M.toEtalePrelogStructure.germ t W w).hom.comp cW = c) ∧
    (∀ (U : X.Etale) (z : (Scheme.pointSmallEtale t).fiber.obj U)
      (a b : B →* M.monoidSheaf.obj.obj (op U)),
      (M.toEtalePrelogStructure.germ t U z).hom.comp a =
        (M.toEtalePrelogStructure.germ t U z).hom.comp b →
      ∃ (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W) (f : W ⟶ U),
        (Scheme.pointSmallEtale t).fiber.map f w = z ∧
        (M.monoidSheaf.obj.map f.op).hom.comp a =
          (M.monoidSheaf.obj.map f.op).hom.comp b) ∧
    (∀ (n m : ℕ) (c : Fin n → B →* M.toEtalePrelogStructure.stalk t)
      (U : Fin m → X.Etale) (z : ∀ j, (Scheme.pointSmallEtale t).fiber.obj (U j))
      (a b : ∀ j, B →* M.monoidSheaf.obj.obj (op (U j))),
      (∀ j, (M.toEtalePrelogStructure.germ t (U j) (z j)).hom.comp (a j) =
        (M.toEtalePrelogStructure.germ t (U j) (z j)).hom.comp (b j)) →
      ∃ (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
        (cW : Fin n → B →* M.monoidSheaf.obj.obj (op W)) (f : ∀ j, W ⟶ U j),
        (∀ i, (M.toEtalePrelogStructure.germ t W w).hom.comp (cW i) = c i) ∧
        ∀ j, (Scheme.pointSmallEtale t).fiber.map (f j) w = z j ∧
          (M.monoidSheaf.obj.map (f j).op).hom.comp (a j) =
            (M.monoidSheaf.obj.map (f j).op).hom.comp (b j)) ∧
    (Function.Injective (Algebra.GrothendieckGroup.of (M := B)) →
      ∀ c : B →* M.toEtalePrelogStructure.stalk t, M.IsStalkChart t c →
      ∃ (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
        (cW : B →* M.monoidSheaf.obj.obj (op W)),
        (M.toEtalePrelogStructure.germ t W w).hom.comp cW = c ∧ M.IsChart W cW) := by
  sorry

end AlgebraicGeometry
