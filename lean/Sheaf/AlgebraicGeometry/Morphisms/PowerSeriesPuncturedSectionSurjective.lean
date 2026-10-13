/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import Sheaf.RingTheory.Depth
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction
import Sheaf.RingTheory.FlatLocalDepthFormula

/-!
# Surjectivity of restriction on the punctured power-series section

Source: Stacks Project, Tags 0EY9, 0BK0, 0EKP and 0EL8.
(blueprint: lem-sbc-power-series-punctured-section-surjective)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Surjectivity of restriction on morphisms of finite étale covers in the
power-series punctured-section situation.  This is the lifting part of
Stacks Project, Tag 0EY9, using formal étaleness and the completion comparison.
The proof constructs compatible lifts on all infinitesimal thickenings, compares
finite locally free Hom modules, and descends the resulting algebra map by
relative Spec. (blueprint: lem-sbc-power-series-punctured-section-surjective)

Proof: Write B = A[[x_1,...,x_d]], I = (x_1,...,x_d), and U = Spec A minus its closed point.
The thickenings V_n of U in V have structure sheaves O_V/I^n. Depth at least two
and Hartogs (0BK0) give Gamma(U,O_U) = A. Each B/I^n is finite free over A, on
monomials of degree less than n. Thus lim Gamma(V_n,O_V_n) = B.
The map Gamma(V,O_V) to this limit is injective: Krull intersection shows that
a section with zero formal restriction has zero germ at every point of U.
The associated primes of B are pB, for associated primes p of A, by the flat
local depth formula. Such p differ from the maximal ideal because depth A is
positive; pB specializes to pB + I, a point of U. Hence the section vanishes
at every associated point of V, so it vanishes. The composition from B through
Gamma(V,O_V) to the limit is the canonical isomorphism; both maps are therefore
isomorphisms. For a finite locally free E on the Noetherian quasi-affine V,
global generation of E dual gives an embedding E into O^r with locally free
cokernel Q. Embed Q into O^s similarly. The sequence 0 -> E -> O^r -> O^s
remains exact on every V_n. Sections and inverse limits preserve its kernel,
so the comparison for O gives Gamma(V,E) = lim Gamma(V_n,E|V_n). Apply this
to internal Hom bundles to obtain bijectivity of completion on module maps.
Given a morphism of the restricted finite etale covers on U, formal etaleness
lifts it uniquely to every V_n, and uniqueness makes these lifts compatible.
They give a compatible system of maps on the finite locally free direct-image
algebras. Surjectivity of the internal Hom comparison lifts the underlying
module map to V. Injectivity of the comparison for the tensor square of the
source algebra and for the unit module verifies multiplication and the unit:
the two required equalities already hold on all V_n. The lifted map is thus
an algebra map. Relative Spec gives a cover morphism restricting to the given
one. This argument also includes empty covers and variable ranks. -/
theorem finiteEtale_powerSeries_punctured_section_restriction_surjective
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A) :
    let z := Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))
    ∀ P Q : V.toScheme.FiniteEtale,
      Function.Surjective ((FiniteEtale.pullback (z ∣_ V)).map (X := P) (Y := Q)) := by
  sorry

end AlgebraicGeometry.Scheme
