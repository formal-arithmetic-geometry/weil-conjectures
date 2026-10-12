/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.EtaleMayerVietoris
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # GabberPrincipalVanishingIdeal

Source: Stacks Project, Tag 0GY0.
(blueprint: lem-weil-pbc-gabber-principal-vanishing-ideal) -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The principal restrictions killing a class form an ideal in the inductive step.

Source: Stacks Project, Etale Cohomology, Lemma 0GY0, label lemma-gabber-criterion,
proof's ideal and addition-closure paragraphs.
(blueprint: lem-weil-pbc-gabber-principal-vanishing-ideal)

Proof: let I consist of f such that the class restricts to zero on D(fh).
The empty open D(0) gives zero membership, and restriction functoriality gives
closure under multiplication by any r. For addition, restrict the class to
D(h(f+g)). If q = 1, apply hfg to hf and hg; its two target opens are
D(h^2 f(f+g)) and D(h^2 g(f+g)), equal to D(hf(f+g)) and D(hg(f+g)).
Functoriality and the inverse-image composition isomorphisms make both images
zero. If q > 1, these two opens cover D(h(f+g)), and their intersection is
D(hfg(f+g)). Its degree q-1 group is subsingleton by hprev. Exactness of
Mayer--Vietoris therefore makes the two restriction maps jointly injective.
The restricted class is zero, proving addition closure. Negatives follow from
multiplication by -1, so the set with these operations is an ideal. All
composition identifications are additive and preserve zero. The empty open,
f = 0, g = -f, and h = 0 require no exclusions. -/
theorem gabber_principal_vanishing_ideal
    (R : Type u) [CommRing R]
    (F : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hfg : ∀ (f g : R) (x : Sheaf.H
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1),
      (AlgebraicGeometry.Etale.cohomologyMap
            (Scheme.homOfLE (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen_mul_le_right f (f + g)))
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1 x) = 0 →
      (AlgebraicGeometry.Etale.cohomologyMap
            (Scheme.homOfLE (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen_mul_le_right g (f + g)))
            (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
              (PrimeSpectrum.basicOpen (f + g)))^*[AddCommGrpCat.{u + 1}]).obj F) 1 x) = 0 →
        x = 0)
    (q : ℕ) (hq : 0 < q)
    (hprev : ∀ (n : ℕ), 0 < n → n < q → ∀ (a : R),
      Subsingleton (Sheaf.H
        (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
          (PrimeSpectrum.basicOpen a))^*[AddCommGrpCat.{u + 1}]).obj F) n))
    (h : R) (ξ : Sheaf.H
      (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
      (PrimeSpectrum.basicOpen h))^*[AddCommGrpCat.{u + 1}]).obj F) q) :
    ∃ I : Ideal R, ∀ f : R, f ∈ I ↔ (cohomologyMap
      (Scheme.homOfLE (X := Spec (CommRingCat.of R))
        (PrimeSpectrum.basicOpen_mul_le_right f h))
      (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
      (PrimeSpectrum.basicOpen h))^*[AddCommGrpCat.{u + 1}]).obj F) q ξ) = 0 := by
  sorry

end AlgebraicGeometry.Etale
