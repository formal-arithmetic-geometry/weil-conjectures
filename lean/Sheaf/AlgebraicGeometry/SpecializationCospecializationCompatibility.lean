/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.SpecializationCospecializationArrows
public import Sheaf.AlgebraicGeometry.DerivedCategories
import Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso
import Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting
import Sheaf.AlgebraicGeometry.UnderivedGlobalGermExchange
import Sheaf.AlgebraicGeometry.DerivedExchangeTermwise
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Specialization and cospecialization commute with fibre maps

Source: Stacks Project, etale-cohomology.tex, Tag 0GJV,
`lemma-specialization-cospecialization`, specialized to `G[0]`
(blueprint: lem-weil-pbc-specialization-cospecialization-compatibility).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Specialization, the canonical fibre maps and cospecialization form a commutative
square in the bounded below derived category of abelian groups. The geometric point
`t` is arbitrary, including the distinguished closed-point lift. There is no properness
or torsion assumption and no invertibility assertion about the arrows in the square.
Source: Stacks Project, Tag 0GJV, `lemma-specialization-cospecialization`, `K = G[0]`
(blueprint: lem-weil-pbc-specialization-cospecialization-compatibility).

Proof:
1. Set `K = G[0]` and pull it back to the strict-local base. Construct the canonical
   comparison `a` from the derived stalk of `Rf_*K` at `s` to derived global sections
   on `X'`: strict-local germ restriction, derived exchange, and Leray. Exactness of
   strict-local sections, the germ-restriction isomorphism, and the strict-local
   global-homology comparison identify this with the strict-local comparison of the
   source (def-weil-pbc-strict-henselization-restriction,
   lem-weil-pbc-strict-local-germ-restriction-iso,
   lem-weil-pbc-strict-local-base-change-global-homology).
2. A germ represented on a pointed étale neighbourhood restricts along its strict-local
   limit leg. Restricting further to `t` is exactly specialization; restricting to the
   canonical closed point gives the original germ. This equality holds termwise on
   complexes (def-weil-pbc-geometric-stalks,
   lem-weil-pbc-strict-henselization-functoriality,
   lem-weil-pbc-geometric-point-pullback-stalk).
3. Horizontal coherence for derived exchange and naturality of restriction identify
   the closed fibre map with `i^* a`, and specialization followed by the other fibre
   map with `h^* a`. On K-injective representatives this follows from the underived
   global-germ/exchange identity and the derived-unit description of restriction.
   Uniqueness of comparison homotopy classes into K-injectives makes these equalities
   hold in the derived category itself (lemma-weil-pbc-derived-exchange-coherence,
   lem-weil-pbc-underived-global-germ-exchange,
   lem-weil-pbc-derived-exchange-termwise, lem-weil-pbc-kinjective-hom-derived,
   lem-weil-pbc-cohomology-pullback-derived-unit).
4. Write `β : K' ⟶ Rh_*h⁻¹K'`. The derived-unit formula gives
   `h^* = RΓ(β) ≫ Leray`. Local acyclicity makes `δ = i⁻¹β` invertible, without
   properness or torsion (lem-weil-pbc-local-acyclicity-closed-fibre-unit).
5. Naturality of the derived adjunction unit gives
   `RΓ(β) ≫ i_B^* = i_K'^* ≫ RΓ(δ)`, also for the derived object `B = Rh_*h⁻¹K'`
   (prop-weil-pbc-derived-inverse-image-adjunction,
   lem-weil-pbc-cohomology-pullback-derived-unit).
6. Expand cospecialization as inverse Leray, restriction, and `RΓ(δ⁻¹)`. Cancel
   Leray with inverse Leray, use step 5, and cancel `RΓ(δ)` with its inverse.
   The resulting composite is `i^* a`, the closed fibre map by step 3.
   No cancellation of specialization, `a`, or either fibre map is used. -/
theorem specialization_cospecialization_compatibility
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsLocallyAcyclicRelative f G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    (derivedEtaleStalkSpecialization s t).app
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≫
      strictBaseSheafFiberMap f G s t ≫ etaleCospecialization f G hG s t =
        closedStrictBaseSheafFiberMap f G s := by
  sorry

end AlgebraicGeometry.Etale
