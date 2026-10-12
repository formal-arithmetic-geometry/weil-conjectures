/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Henselian.PairHenselization
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Cohomology over the henselization of a pair

Let `B` be a ring, `J` an ideal and `Bʰ` the henselization of `(B, J)`
(`PairHenselization.henselization`). `Spec Bʰ` is the cofiltered limit of the spectra of the
étale neighbourhoods of `V(J)`, so by the continuity of étale cohomology a class of an étale
sheaf on `Spec B` restricted to `Spec Bʰ` comes from a class over one of these neighbourhoods.
In particular, if `G` has no cohomology in degree `q` over every étale `B`-algebra, neither does
its restriction to `Spec Bʰ`.

## Main statements

- `AlgebraicGeometry.Etale.subsingleton_H_upperStar_henselization`: the vanishing transfer.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- If an abelian étale sheaf `G` on `Spec B` has no cohomology in degree `q` after restriction
to every étale `B`-algebra, then it has no cohomology in degree `q` after restriction to the
henselization `Bʰ` of a pair `(B, J)`: `Spec Bʰ` is the cofiltered limit of the étale
neighbourhoods of `V(J)`, along which étale cohomology is continuous. -/
theorem subsingleton_H_upperStar_henselization {B : Type u} [CommRing B] (J : Ideal B)
    (G : Sheaf (Spec (.of B)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hG : ∀ (S : Type u) [CommRing S] [Algebra B S] [Algebra.Etale B S],
      Subsingleton (Sheaf.H
        ((Spec.map (CommRingCat.ofHom (algebraMap B S)))^*[AddCommGrpCat.{u + 1}].obj G) q)) :
    Subsingleton (Sheaf.H ((Spec.map (CommRingCat.ofHom
      (algebraMap B (PairHenselization.henselization B J))))^*[AddCommGrpCat.{u + 1}].obj G) q) :=
  sorry

end AlgebraicGeometry.Etale
