/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.RingTheory.Depth
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction
import Sheaf.RingTheory.MvPowerSeriesFlat
import Sheaf.RingTheory.AnnihilatorAssociatedPrimesFlatBaseChange
import Sheaf.RingTheory.DepthLeDimAssociatedPrime
import Sheaf.RingTheory.InjectivePiLocalizationAssociatedPrimes
import Mathlib.RingTheory.Filtration

/-!
# Global sections of a power-series open containing the punctured zero section

Source: Stacks Project, Tag 0EY9, first displayed comparison in the proof.
(blueprint: lem-sbc-power-series-punctured-global-sections)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The canonical restriction from the power-series ring to the global sections of
an open containing precisely the punctured zero section is bijective.

Source: Stacks Project, Tag 0EY9 (lemma-fully-faithful-power-series-over-depth2),
the comparison of global sections preceding the finite locally free argument;
Tags 0BK0, 0EKP and 0EL8 supply Hartogs and the uniqueness argument.
(blueprint: lem-sbc-power-series-punctured-global-sections)

Proof: Put B = A[[X_1,...,X_d]], I = (X_1,...,X_d), and let U be the punctured
spectrum of A. Its global sections are A by depth-two Hartogs. The quotients
B/I^n are finite free A-modules with basis the monomials of total degree less
than n. Therefore sections of the n-th zero-section thickening in V are B/I^n,
and their inverse limit is B. Completion gives a map Gamma(V,O) to this limit,
whose composite with the canonical map from B is the identity. This completion
map is injective: at each point of U its kernel has zero germ by Krull
intersection in the Noetherian local ring, since I lies in its maximal ideal.
By flat base change of associated primes, the associated primes of B are extensions
pB of associated primes p of A: B/pB is the power-series domain over A/p.
The depth bound by dim(A/p) excludes the maximal ideal of A from these primes.
The point pB specializes to pB+I, which lies in U and
therefore in V. Vanishing at the latter point forces vanishing at the former.
Thus a section in the kernel vanishes at every associated point of V and is
zero by the associated-point criterion. Since the composite B -> Gamma(V,O)
-> B is the identity and the second map is injective, the first map is also
surjective and injective. This is the canonical map in the conclusion, with
the standard identification Gamma(Spec B,O) = B. No reducedness or normality
is used; the associated-point argument also covers rings with nilpotents. -/
theorem bijective_powerSeries_punctured_globalSections
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A) :
    Function.Bijective
      ((ΓSpecIso (.of (MvPowerSeries (Fin d) A))).inv ≫ V.ι.appTop).hom := by sorry

end AlgebraicGeometry.Scheme
