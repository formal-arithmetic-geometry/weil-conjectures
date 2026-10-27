/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.RegularSchemeMorphism
public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import WeilConjectures.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Mathlib.RingTheory.Flat.Stability
import Sheaf.RingTheory.StrictHenselizationModuleFlatness
import WeilConjectures.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import WeilConjectures.RingTheory.StrictHenselizationSurjectiveQuotient
import WeilConjectures.RingTheory.StrictHenselizationRegular
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Submodule

/-! # Regular morphisms on geometric strict local rings

Source: Stacks Project, Tags 04HX, 06LJ, 05VL, 07QM, 05WS and 06LN
(blueprint: lem-per-regular-geometric-stalk-map).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a regular morphism of locally Noetherian schemes, the geometric strict local
rings are Noetherian local rings and their canonical map is flat with regular local
closed fibre. The ring map is obtained from `Scheme.strictHenselizationMap` by the
fully faithful spectrum functor; its pointed characterization fixes the residue
embeddings into the same geometric-point field. No excellence or finite type is assumed.

Source: Stacks Project, Tags 04HX, 06LJ, 05VL, 07QM, 05WS and 06LN
(blueprint: lem-per-regular-geometric-stalk-map).

Proof, following the five steps of the node:
1. Take Noetherian affine charts through the images of the geometric points.
   `lem-weil-pbc-affine-open-stalk-localization` identifies their localized rings
   with the ordinary stalks R and B; `lem-weil-pbc-localization-noetherian` makes
   these Noetherian. `lem-exc-affine-strict-local-ring-comparison` identifies the
   geometric strict local rings A and C with their algebraic strict henselizations,
   respecting the embeddings into the geometric-point field. They are local;
   `lem-sc-strict-henselization-noetherian` makes them Noetherian. The structural
   square of `lem-weil-pbc-strict-henselization-functoriality`, first on chart
   sections and then on fractions, identifies the composite R → A → C with R → B → C.
2. `def-per-regular-scheme-morphism` gives flatness, so `def-weil-flat-morphism`
   gives flatness of B over R. `lem-sc-strict-henselization-faithfully-flat` makes
   C flat over B. `lem-pc-module-flat-transitive` makes C flat over R. Apply
   `lem-sfb-strict-henselization-module-flatness` to C with its actual A-action
   to obtain flatness over A, which is `RingHom.Flat` for the canonical map.
3. `lem-weil-pbc-strict-henselization-chart-maximal-ideal` identifies the maximal
   ideal of A with the chart prime extended to A. Localizing the chart identifies
   this ideal with the maximal ideal of R extended to A. Extending to C through
   the square in step 1 gives m_A C = m_R C.
4. Put I = m_R B. The ordinary stalk map is local, so I lies in m_B. Testing
   regularity at the identity residue-field extension gives regularity of the
   ordinary fibre. `lem-sbc-scheme-fibre-stalk-quotient` identifies B/I with its
   local ring at the chosen point. `def-weil-regular-scheme` makes B/I regular local.
5. `lem-sbc-strict-henselization-surjective-quotient` makes the explicit quotient
   C/IC a strict henselization of B/I. `lem-sc-strict-henselization-regular`
   makes it regular local. Finally IC = m_R C = m_A C by step 3 and transitivity
   of ideal extension, giving exactly the displayed closed-fibre quotient.
-/
theorem regular_geometric_stalk_map
    {Y X : Scheme.{u}} (g : Y ⟶ X)
    [IsLocallyNoetherian Y] [IsLocallyNoetherian X]
    (hg : IsRegularSchemeMorphism g)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Y) :
    ∃ (_ : IsLocalRing (Scheme.strictHenselizationRing (barY ≫ g)))
      (_ : IsLocalRing (Scheme.strictHenselizationRing barY)),
      IsNoetherianRing (Scheme.strictHenselizationRing (barY ≫ g)) ∧
      IsNoetherianRing (Scheme.strictHenselizationRing barY) ∧
      RingHom.Flat (Spec.preimage (Scheme.strictHenselizationMap g barY)).hom ∧
      IsRegularLocalRing
        (Scheme.strictHenselizationRing barY ⧸
          (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing (barY ≫ g))).map
            (Spec.preimage (Scheme.strictHenselizationMap g barY)).hom) := by
  sorry

end AlgebraicGeometry
