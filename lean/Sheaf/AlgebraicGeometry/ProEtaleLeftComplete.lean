/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProEtaleProductsDerived

/-!
# Postnikov convergence on the small pro-etale site

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
sk-prop-pe-left-complete/det-pe-left-complete-iso.md and its proof
(blueprint: det-pe-left-complete-iso).

We use the good truncations and quotient maps of Mathlib and the strict shifted-cone
construction used by `milnor_sequence`. The comparison has the quotient maps in its
first coordinate and zero in its second coordinate; no arbitrary cone lift is chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

section Construction

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The canonical quotient from the lower truncation at -(n+1) to that at -n.
Truncating the quotient map at the lower cutoff and identifying the already-supported
result with its source constructs the unique map compatible with the quotient from K.
Source: blueprint main-20261015, det-pe-left-complete-iso, first proof paragraph
(blueprint: det-pe-left-complete-iso). -/
def postnikovStep (K : CochainComplex A ℤ) (n : ℕ) :
    K.truncGE (-((n + 1 : ℕ) : ℤ)) ⟶ K.truncGE (-(n : ℤ)) :=
  letI := (K.truncGE (-(n : ℤ))).isStrictlyGE_of_ge
    (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
    (Int.neg_le_neg (Int.ofNat_le.mpr (Nat.le_succ n)))
  CochainComplex.truncGEMap (K.πTruncGE (-(n : ℤ))) (-((n + 1 : ℕ) : ℤ)) ≫
    inv ((K.truncGE (-(n : ℤ))).πTruncGE (-((n + 1 : ℕ) : ℤ)))

/-- The strict inverse sequence of good truncations, indexed by n >= 0.
Source: blueprint main-20261015, det-pe-left-complete-iso, displayed tower
(blueprint: det-pe-left-complete-iso). -/
def postnikovTower (K : CochainComplex A ℤ) : ℕᵒᵖ ⥤ CochainComplex A ℤ :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ K.truncGE (-(n : ℤ))) (postnikovStep K)

/-- The quotient family and zero second coordinate satisfy the shifted-cone chain-map
condition. This is the map-of-complexes assertion in the first paragraph of the source.
Source: blueprint main-20261015, det-pe-left-complete-iso.proof.md, first paragraph
(blueprint: det-pe-left-complete-iso).

Proof: Naturality of the good-truncation quotient, followed by cancellation of its
invertible further truncation, gives pi_(n+1) followed by postnikovStep n = pi_n.
The successor transition of Functor.ofOpSequence is postnikovStep n. Thus after every
product projection, the product quotient followed by 1-T is pi_n - pi_n = 0.
Product extensionality gives zero. The coboundary of the zero degree-minus-one cochain
is zero and Cochain.ofHom sends zero to zero, giving the displayed condition. -/
theorem postnikovComparison_condition (K : CochainComplex A ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain K
          (∏ᶜ (fun n : ℕ ↦ (postnikovTower K).obj (op n))) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (Pi.lift (fun n : ℕ ↦ K.πTruncGE (-(n : ℤ))) ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦ (postnikovTower K).obj (op n))
            (WeilConjectures.integralOperationsTowerStep (postnikovTower K))) = 0 := by
  sorry

/-- The canonical comparison with the sequential derived limit: its first coordinate
is the family K -> tau_(>=-n) K and its second coordinate is zero. Mathlib's
mappingCocone is Cone(1-T)[-1], with the same first projection as the source's (x,y)
coordinates; the zero second coordinate is unchanged by the cone sign convention.
Source: blueprint main-20261015, det-pe-left-complete-iso, displayed map
(blueprint: det-pe-left-complete-iso). -/
def postnikovComparison (K : CochainComplex A ℤ) :
    K ⟶ WeilConjectures.integralOperationsRoos (postnikovTower K) :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ (postnikovTower K).obj (op n))
      (WeilConjectures.integralOperationsTowerStep (postnikovTower K)))
    (Pi.lift (fun n : ℕ ↦ K.πTruncGE (-(n : ℤ)))) 0
    (postnikovComparison_condition K)

end Construction

/-- Every complex of modules over any ring sheaf on the small pro-etale site is
quasi-isomorphic to the strict sequential derived limit of its good lower truncations,
via the canonical quotient-family comparison.
Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-pe-left-complete/det-pe-left-complete-iso.md
(blueprint: det-pe-left-complete-iso).

Proof:
1. Put K_n = tau_(>=-n) K, P = product K_n, and F = Cone(1-T)[-1]. The quotient
maps commute with the canonical transitions, so (1-T) kills their product lift.
The comparison is the chain map (quotient family,0), with projection to P equal to
that family, as verified in postnikovComparison_condition.
2. Apply the cohomology long exact sequence to the rotated cone triangle
F -> P -> P -> F[1]. By det-pe-products-derived, H^r(P) identifies with the product
of H^r(K_n), through the actual projections. The induced endomorphism is 1-T.
Its kernel is the inverse limit of cohomology sheaves. Exactness gives the cokernel
in degree q-1, H^q(F), and that kernel in degree q as a short exact sequence. The
projection after H^q of the comparison has nth component H^q(K -> K_n).
3. Clause 2 of det-pe-milnor-sequence identifies the left endpoint with R^1 lim
H^(q-1)(K_n). By det-pe-left-complete-truncation-tower this is zero, and the
quotient-induced map H^q(K) -> lim H^q(K_n) is invertible. Hence the projection
H^q(F) -> lim H^q(K_n) is invertible and its composite with H^q of the comparison
is invertible. Therefore H^q of the comparison is invertible for every integer q,
which is precisely the quasi-isomorphism assertion. -/
theorem left_complete_quasiIso (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{max u (t + 1)})
    (K : CochainComplex (ringedSiteModules.{max u (t + 1)} R) ℤ) :
    QuasiIso (postnikovComparison K) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
