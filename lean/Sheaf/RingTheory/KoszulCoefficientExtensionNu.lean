/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.RingTheory.KoszulConormalComparison
public import Sheaf.RingTheory.KoszulRegularSequence
public import Mathlib.RingTheory.Localization.Defs

/-! # KoszulCoefficientExtensionNu

Source: Stacks Project, Tag 0BQZ, coefficient formulas in the finite free
Koszul calculation (blueprint: new-lem-sc-koszul-coefficient-extension-nu).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- The coefficient extension normal determinant map with its evaluation formula.
Source: Stacks Project, Tag 0BQZ, finite free Koszul computation.
(blueprint: new-lem-sc-koszul-coefficient-extension-nu)

Proof: Put B = A/I and C = S/IS. Localization is flat, so Tag 062H gives
Koszul regularity of the image sequence. The conormal-basis theorem (Tag 062I)
gives bases b_i of I/I^2 and c_i of IS/(IS)^2 consisting of the generator classes.
Let b_i^* and c_i^* be their coordinate functionals. Their increasing top wedges
are bases of the normal determinants. Define nu by sending a times the top
wedge of b_i^* to q(a) times the top wedge of c_i^*. This is additive and
A-linear: hq identifies the A-action through B with the A-action through C.
The coordinates of koszulConormalVector(v) in b are the residues of the
coordinates of v, by its linearCombination definition. The coordinates of its
image in c are their q-images by hq. Pairing the top dual wedge with these
vectors is their coordinate determinant (pairingDual_ιMulti_ιMulti). Ring maps
preserve determinants, so multiplication by q(a) gives exactly the displayed
formula for every w and v. For r = 0 use the empty wedge and determinant 1.
If B or C is the zero ring, the same basis-coordinate construction and formulas
still apply, without a nontriviality hypothesis. No data are chosen from a mere
existence statement: the described coordinate maps are explicit once the
conormal bases, fixed by their generator values, are given. -/
theorem exists_koszul_coefficient_extension_nu
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I)
    (T : Submonoid A) (S : Type u) [CommRing S] [Algebra A S]
    [IsLocalization T S]
    (hs : Ideal.span (Set.range (algebraMap A S ∘ f)) = I.map (algebraMap A S))
    (q : (A ⧸ I) →+* (S ⧸ I.map (algebraMap A S)))
    (hq : ∀ b : A, q (Ideal.Quotient.mk I b) =
      Ideal.Quotient.mk (I.map (algebraMap A S)) (algebraMap A S b)) :
  ∃ (ν : koszulNormalDeterminant A I r →ₗ[A]
    (ModuleCat.restrictScalars (algebraMap A S)).obj
      (koszulNormalDeterminant S (I.map (algebraMap A S)) r)),
  ∀ (w : koszulNormalDeterminant A I r) (v : Fin r → (Fin r →₀ A)),
    exteriorPower.pairingDual (S ⧸ I.map (algebraMap A S))
      (I.map (algebraMap A S)).Cotangent r (ν w)
      (exteriorPower.ιMulti (S ⧸ I.map (algebraMap A S)) r
        (fun i ↦ koszulConormalVector S (I.map (algebraMap A S)) r
          (algebraMap A S ∘ f) hs
          ((v i).mapRange (algebraMap A S) (map_zero _)))) =
    q (exteriorPower.pairingDual (A ⧸ I) I.Cotangent r w
      (exteriorPower.ιMulti (A ⧸ I) r
        (fun i ↦ koszulConormalVector A I r f hf (v i)))) := by sorry

end ExteriorAlgebra
