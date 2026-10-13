/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicUniqueLift
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.RingTheory.Depth
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction
import Sheaf.RingTheory.FlatLocalDepthFormula

/-!
# Algebraization of compatible formal morphisms on a punctured power-series open

Source: Stacks Project, Tags 0EY9, 0EKP and 0EL8.
(blueprint: lem-sbc-power-series-punctured-formal-hom-algebraization)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Compatible maps on all quotient-power thickenings of finite étale covers
algebraize on the power-series open.

Source: Stacks Project, Tag 0EY9, the comparison argument of Tag 0EKP and
algebra-map verification of Tag 0EL8.
(blueprint: lem-sbc-power-series-punctured-formal-hom-algebraization)

Proof: Write B = A[[x_1,...,x_d]] and I = ker(constantCoeff) = (x_1,...,x_d).
Put U = Spec(A) minus its closed point. Hartogs at depth two identifies
Gamma(U,O_U) with A. Since B/I^(n+1) is finite free over A on the monomials
of degree at most n, the limit of the sections on the infinitesimal
neighbourhoods of U in V is B. The comparison from Gamma(V,O_V) to this
limit is injective: Krull intersection detects zero germs along U, and
flat local depth shows that every associated prime of B is pB for an
associated prime p of A. Depth positive excludes the maximal ideal of A;
the prime pB specializes to pB+I, which belongs to U. Thus a section zero
formally is zero at every associated point of V, hence zero. The composite
B -> Gamma(V,O_V) -> B is the canonical isomorphism, so both maps are
isomorphisms. For any finite locally free E on the Noetherian quasi-affine
V, global generation of the dual gives a universally exact presentation
0 -> E -> O^r -> O^s: first embed E in O^r with locally free cokernel,
then embed that cokernel in O^s. Sections and inverse limits preserve the
kernel. The structure-sheaf comparison therefore gives the same comparison
for E and hence for internal Hom bundles, as in Tag 0EKP.
A compatible family g_n gives compatible maps between the finite locally
free direct-image algebras of Q and P. The Hom comparison lifts these to
a module map. Its multiplication and unit identities hold after completion;
faithfulness for the tensor square of the source algebra and for O_V gives
the identities before completion. Relative Spec turns the resulting algebra
map into g over V. Its pullback to every thickening is g_n by the construction.
No infinitesimal lifting or existence of a map on the reduced section is
used here: the entire compatible family is an input. Zero algebras, empty
covers, and variable ranks are included in the module comparison. -/
theorem finiteEtale_powerSeries_punctured_formal_hom_algebraization
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A)
    (P Q : V.toScheme.FiniteEtale)
    (g : ∀ n : ℕ, FiniteEtale.Adic.cover
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V P n ⟶ Q.obj.left)
    (hover : ∀ n, g n ≫ Q.obj.hom = FiniteEtale.Adic.coverMap
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V P n ≫ P.obj.hom)
    (hcompat : ∀ n, FiniteEtale.Adic.coverTransition
      (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V P n ≫ g (n + 1) = g n) :
    ∃ φ : P.obj.left ⟶ Q.obj.left, φ ≫ Q.obj.hom = P.obj.hom ∧
      ∀ n, FiniteEtale.Adic.coverMap
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) V P n ≫ φ = g n := by sorry

end AlgebraicGeometry.Scheme
