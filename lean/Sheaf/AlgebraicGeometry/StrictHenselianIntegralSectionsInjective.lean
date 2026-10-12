/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import WeilConjectures.SixFunctors.BaseChange.GlobalSections
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Sheaf.RingTheory.IntegralOverHenselianPair
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import Sheaf.AlgebraicGeometry.EtaleModuleSetPullbackComparison

/-! # Injectivity of integral sections over a strictly henselian base

Source: Stacks Project, Tags 09XK, 09ZH and 0A3I, as used in Tag 0EYP.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
open Scheme

/-- Restriction to any closed geometric fibre of an integral scheme over a strictly
henselian local ring is injective on sections.

Source: Stacks Project, Tags 09XK, 09ZH and 0A3I, proof of Tag 0EYP.
(blueprint: lem-sbc-strict-henselian-integral-sections-injective).

Proof: An integral scheme over Spec A is affine, say Spec B, with B integral over A.
Set J to the extension of the maximal ideal of A. Tag 09XK makes (B,J) henselian.
Apply henselian degree-zero comparison to the proper identity of Spec B to see
that restriction to Spec(B/J) is injective. The map t factors through the residue
field k of A, since its image is the closed point. The ring k is separably closed.
Tag 0A3I makes further restriction from the closed fibre to its extension along
k -> Omega bijective. Forgetting modules to sets commutes with inverse images
and the units; hence these are the same restriction maps for module coefficients.
The pullback property identifies their composite, up to the canonical composition
and terminal-section isomorphisms, with the displayed map. Injectivity follows.
The zero algebra B and the empty fibre cause no exception: their section module
is zero, and the henselian comparison also holds for the zero ring. -/
theorem strictHenselianIntegralSections_injective
    (Λ : Type (u + 1)) [CommRing Λ]
    (A : Type u) [CommRing A] [IsStrictlyHenselianLocalRing A]
    {Z Z' : Scheme.{u}} (p : Z ⟶ Spec (.of A)) [IsIntegralHom p]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of A))
    (ht : t (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint A)
    (i : Z' ⟶ Z) (p' : Z' ⟶ Spec (.of Ω)) (sq : IsPullback i p' p t)
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Injective (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i F).hom := by
  sorry

end AlgebraicGeometry.Etale
