/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.RingTheory.BirationalGenericLocalization

/-!
# Common dense opens of a locally finitely presented birational morphism

Source: Stacks Project, Morphisms, Tag 0BAC, lemma-birational-birational, case (2)
(blueprint: lem-per-birational-common-dense-opens).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A locally finitely presented morphism between schemes with finitely many irreducible
components identifies two dense opens if it bijects their generic points and induces
isomorphisms on the corresponding local rings.

Source: Stacks Project, Morphisms, Tag 0BAC, lemma-birational-birational, case (2)
(blueprint: lem-per-birational-common-dense-opens).

Proof:
1. Enumerate the finitely many components and their generic points, using scheme sobriety
   (`lem-sc-scheme-sober`). For each component remove all the other components; the resulting
   open subsets are pairwise disjoint and contain their respective generic points. Choose
   affine neighbourhoods Spec B and Spec A of the matched generic points inside these opens,
   with the source neighbourhood mapping into the target neighbourhood
   (`lem-weil-pbc-affine-opens-basis`). The restricted map is Spec of the induced ring map
   B → A (`lem-weil-pbc-affine-opens-induced-ring-map-spec-square`). These spectra are
   irreducible and have unique minimal primes q and p
   (`lem-weil-pbc-spec-irreducible-components-minimal-primes`).
2. The generic stalk hypothesis identifies B_q → A_p as an isomorphism
   (`lem-weil-pbc-spec-map-stalk-localization`). The generic-localization argument gives
   B_q ≅ A_q (`lem-per-birational-generic-localization`).
3. The affine ring map is finitely presented
   (`lem-weil-pbc-lfp-affine-opens-finite-presentation`). Choose finitely many algebra
   generators. Surjectivity after localization at q expresses each generator with a
   denominator outside q; finitely many further denominators kill the differences. Inverting
   their product g makes B_g → A_g surjective. Base change preserves finite presentation,
   so its kernel is finitely generated
   (`lem-weil-pbc-finite-presentation-surjection-kernel-fg`, with zero polynomial variables).
   Each kernel generator vanishes at q. Multiplying g by finitely many elements outside q
   kills them all, making B_g → A_g an isomorphism.
4. The corresponding principal opens in the affine neighbourhoods are isomorphic by f
   (`lem-weil-pbc-principal-localization-open-immersion`). They still contain the matched
   generic points because the chosen denominators lie outside q and p.
5. Take the unions of these source and target opens. They are disjoint unions because of
   the component complements chosen in step 1. The componentwise isomorphisms therefore
   glue to the restriction of f. Both unions contain every component's generic point, so
   their closures contain every irreducible component and hence the whole schemes
   (`def-weil-irreducible-components`). This argument also covers the empty schemes. -/
theorem exists_common_dense_opens_isIso_of_generic_stalks
    {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFinitePresentation f]
    (hX : (irreducibleComponents X).Finite) (hY : (irreducibleComponents Y).Finite)
    (hgeneric : Set.BijOn f (genericPoints Y) (genericPoints X))
    (hstalk : ∀ η ∈ genericPoints Y, IsIso (f.stalkMap η)) :
    ∃ (U : Y.Opens) (V : X.Opens), Dense (U : Set Y) ∧ Dense (V : Set X) ∧
      ∃ hUV : U ≤ f ⁻¹ᵁ V, IsIso (f.resLE V U hUV) := by
  sorry

end AlgebraicGeometry
