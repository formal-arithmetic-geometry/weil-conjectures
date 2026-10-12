/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import Sheaf.RingTheory.IntegralOverHenselianPair
import Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import Sheaf.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero

/-! # Integral schemes over strictly henselian local rings

Source: Stacks Project, Tag 0EYP, via Tags 09XK, 09ZH and 0A3I.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
open Scheme

/-- Restriction to a closed geometric fibre of an integral scheme over a strictly
henselian local ring is an isomorphism on sections of every module sheaf.

Source: Stacks Project, Tag 0EYP, via Tags 09XK, 09ZH and 0A3I.
(blueprint: lem-sbc-integral-strict-henselian-geometric-fibre-sections).

Proof: Since p is integral and its base is affine, write Z = Spec B, with B integral
 over A. Let m be the maximal ideal of A. The pair (A,m) is henselian, so Tag 09XK
makes (B,mB) henselian. Apply the henselian degree-zero theorem to the proper
identity morphism of Spec B. It makes restriction to Spec(B/mB) invertible. The
closed-point hypothesis on t says that the corresponding map A to Omega has
kernel m. It factors uniquely through k = A/m, which is separably closed. The
Cartesian square identifies Z' with the base change of Spec(B/mB) from k to Omega.
Tag 0A3I makes its canonical restriction bijective for sheaves of sets. The
module/set inverse-image comparison and its adjunction-unit formula transport
that bijection to the module restriction. A module homomorphism with bijective
underlying function is an isomorphism. The composition identity for inverse-image
units and pullback pasting identify the composite of the two restriction maps
with globalSectionsUpperStarMap along i, up to isomorphisms. Hence that map is
invertible. If B is zero then both section modules are zero; the same argument
and identities apply. The coefficient ring may be zero. No algebraicity of Omega
 over k is used. -/
theorem isIso_integralStrictHenselianGeometricFibreRestriction
    (Λ : Type (u + 1)) [CommRing Λ]
    (A : Type u) [CommRing A] [IsStrictlyHenselianLocalRing A]
    {Z Z' : Scheme.{u}} (p : Z ⟶ Spec (.of A)) [IsIntegralHom p]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ Spec (.of A))
    (ht : t (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint A)
    {i : Z' ⟶ Z} {p' : Z' ⟶ Spec (.of Ω)} (sq : IsPullback i p' p t)
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i F) := by
  sorry

end AlgebraicGeometry.Etale
