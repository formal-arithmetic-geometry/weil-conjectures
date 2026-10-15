/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.Compactification.CategoryBaseChange
public import Sheaf.AlgebraicGeometry.ProperOpenComparison
public import Sheaf.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.AlgebraicGeometry.ProperOpenComparisonIso
import Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-!
# Compact-support base change with finite coefficients and arbitrary refinements

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-cbc-finite-torsion;
Stacks Project, Tags 0DDE, 0F7I, 0F7J and 0F7F (blueprint: thm-cbc-finite-torsion).

The exchange map, its invertibility, identity and horizontal pasting, and its canonical
compactification-independent version and vertical pasting already exist upstream. The theorem
below also identifies the comparisons specified by the node with the canonical comparisons
for every proper refinement, including refinements whose square over the open is not Cartesian.
Together with the recorded upstream declarations, this states all clauses of the node.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The comparison `C_r = Rp₂*(α_r)`, followed by direct-image composition, for any
proper refinement fixing the open. The map `α_r` is exactly `properOpenComparison`, not an
exchange requiring a Cartesian refinement square.
Source: blueprint thm-cbc-finite-torsion, proof steps 4 and 5; Stacks Project, Tag 0F7I
(blueprint: thm-cbc-finite-torsion). -/
noncomputable def compactSupportProperOpenRefinementMap
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) d).obj K ⟶
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c).obj K :=
  (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) d.g).map
      (properOpenComparison Λ r.hom c.i d.i r.i_hom K) ≫
    ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).pfComp'
      r.hom d.g c.g r.hom_g).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategoryPlus.obj K)

/-- Compact-support exchange is invertible at every bounded-below complex, and the
specified proper/open refinement maps are the canonical comparison isomorphisms, for all
refinements without a Cartesian or density hypothesis.
Source: blueprint thm-cbc-finite-torsion; Stacks Project, Tags 0DDE and 0F7I
(blueprint: thm-cbc-finite-torsion).

Proof, following the node's seven steps:
1. For the supplied compactification, use its base change and its two Cartesian squares
from def-cbc-compact-support-square and lem-cbc-compactifiable-cofiltered. Exactness of
extension by zero (lem-weil-pbc-extension-by-zero-exact) keeps `j_! K` bounded below.
2. A finite ring has finite additive exponent, so all its modules are torsion. Apply
thm-weil-pbc-bounded-below to the proper factor. The exact comparison of
lem-weil-pbc-exchange-forget-coefficients identifies the module exchange and reflects
invertibility.
3. Compose with the extension-by-zero base-change isomorphism of
cor-cbc-derived-extension-zero-base-change. This is the specific exchange of
def-cbc-exchange-map, and it is natural as a composite of natural transformations.
4. Apply lem-cbc-proper-open-interchange-coherence to a proper refinement. Its specialization
is exactly the alpha of def-weil-pbc-proper-open-comparison. The base-change equation and
lem-weil-pbc-mate-pasting give the intertwining equation for `C_r`.
5. The identity and composition laws of lem-weil-pbc-proper-open-comparison-composition,
and invertibility from lem-weil-pbc-proper-open-comparison-iso, make these comparisons a
contravariant system. For a Cartesian refinement they agree with the formalism comparison:
restrict to the open, where both transposes are the identity on the distinguished clopen
component, and use the extension-by-zero adjunction. For an arbitrary refinement, pass to a
dense common refinement and use composition and cancellation. Hence `C_r` equals the hom of
`shriekIso d c`. The cofilteredness and equalizer clauses of
lem-cbc-compactifiable-cofiltered show that every common-refinement ratio is this same
canonical comparison. Direct-image compositors are normalized on bounded-below injectives
as in lem-weil-pbc-ringed-topoi-derived-pushforward-composition; successive direct images
remain injective by lem-weil-pbc-direct-image-preserves-injectives.
6. Identity and horizontal pasting follow from the corresponding equations for the proper
exchange and extension-by-zero base change. Naturality commutes the middle factors and
lem-weil-pbc-mate-pasting combines the proper factors. The upstream identity and horizontal
pasting statements are recorded with this theorem, not duplicated.
7. For vertical pasting use lem-cbc-compactifiable-compatible-tower. The proper/open
interchange base-change equation commutes the tower composition through pullback; proper
mate pasting and open base-change pasting give the composite exchange. A common refining
tower and step 5 remove all choices. Upstream `lowerShriekBaseChange_eq` and
`lowerShriekBaseChange_paste_vert` express these canonical equations. -/
theorem compactSupportFiniteTorsion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    (∀ K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso ((rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c).app K)) ∧
    (∀ (d : Compactification f) (r : c.Refinement d)
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      compactSupportProperOpenRefinementMap Λ r K =
        ((derivedPlusFormalism (ModuleCat.{u + 1} Λ)).shriekIso d c).hom.app K) := by
  sorry

end AlgebraicGeometry.Etale
