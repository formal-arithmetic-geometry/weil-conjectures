/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

import Sheaf.RingTheory.IntegralOverHenselianPair
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
open Scheme

/-- Restriction to the residue-field fibre of an integral scheme over a henselian
local ring is injective on module sections.
Source: Stacks Tags 09XK and 0A0C, the henselian comparison in Tag 0EYP.

Proof: Integrality makes Z affine. Write Z = Spec B by its canonical global-section
presentation. The ring map A → B is integral. Set J = m_A B. Tag 09XK makes (B,J)
a henselian pair. Apply isIso_globalSectionsUpperStarMap_of_henselianRing to the
proper identity morphism of Spec B and J. Its fibre is Spec(B/J). The tensor-quotient
isomorphism identifies this with the fibre over A/m_A. Transport the comparison
through the affine presentation and the given Cartesian square. These section
isomorphisms respect the inverse-image adjunction unit, so the displayed restriction
is an isomorphism, in particular injective. For B = 0 all the schemes in question
are empty and the section module is zero; the same argument applies.
(blueprint: new-integral-henselian-closed-fibre-sections) -/
theorem integralHenselianClosedFibreSections_injective
    (Λ : Type (u + 1)) [CommRing Λ]
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    {Z Z₀ : Scheme.{u}} (p : Z ⟶ Spec (.of A)) [IsIntegralHom p]
    (i₀ : Z₀ ⟶ Z) (p₀ : Z₀ ⟶ Spec (.of (IsLocalRing.ResidueField A)))
    (sq : IsPullback i₀ p₀ p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Injective (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i₀ F).hom := by
  sorry

end AlgebraicGeometry.Etale
