/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.LocalFrobeniusConjugacy

/-!
# Degree formula for the local Frobenius

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-tf-curve-local/sec-the-local-term-at-a-fixed-point/sk-p-frob/sk-c-proper-global/
lem-trf-frobenius-degree-formula.md and its proof, Steps 1--2
(blueprint: lem-trf-frobenius-degree-formula).

The operators are the recorded finite condensed-coefficient local Frobenii, evaluated
on their own point-fibre complexes. The scalar ring is the terminal evaluation of the
discrete condensed ring A, canonically A. Perfectness is concluded, not assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures.CondensedFrobeniusOperators

open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

/-- The trace at any F_(q^m)-point above x is the trace of the one-circuit local
Frobenius to the power m / deg(x), at the specified F_(q^deg(x))-point above x.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-tf-curve-local/sec-the-local-term-at-a-fixed-point/sk-p-frob/sk-c-proper-global/
lem-trf-frobenius-degree-formula.md and its proof, Steps 1--2
(blueprint: lem-trf-frobenius-degree-formula).

Proof, following the node's five steps:
1. Set d = [kappa(x):k0] and r = m/d. The specified degree-d point gives a lift z
   fixed by Phi^d, and by Phi^m since d divides m.
2. At z, fixed-point transport composition and pullback-stalk coherence, the naturality
   of kappa, and the iterated Weil cocycle give F_(z,(r+1)d) = F_(z,d) F_(z,rd).
3. Starting with r=1, induction gives F_(z,rd) = F_(z,d)^r.
4. Every degree-m point above x is a lift in the normalized orbit of z. Local Frobenius
   conjugacy transports F_(z,m) to its operator on that point's actual stalk complex.
5. These stalk complexes are perfect. Conjugacy invariance of their categorical traces
   gives the displayed equality, with r=m/d. This also proves independence of the
   chosen degree-d lift. The zero complex and d=1 require no separate assumptions.
-/
theorem frobenius_degree_formula
    (F : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of F.k₀)))
    [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ F.p)
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n) (K : FiniteStrictWeilComplex F Y₀ ell E n hn)
    (x : Y₀.left) (_hx : IsClosed ({x} : Set Y₀.left)) :
    letI : HasDerivedCategory.{u + 1}
        (ModuleCat.{u + 1} (condensedScalarRing (finiteCoefficient ell E n))) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    ∃ hd : 1 ≤ Y₀.hom.degreeOver x,
      ∀ (xₘ : F.extensionPoints Y₀ (Y₀.hom.degreeOver x) hd),
        IsLocalFrobeniusLift F Y₀ x
          (localExtensionPoint F Y₀ (Y₀.hom.degreeOver x) hd xₘ) →
      ∀ (m : ℕ) (hm : 1 ≤ m), Y₀.hom.degreeOver x ∣ m →
      ∀ (y : F.extensionPoints Y₀ m hm),
        IsLocalFrobeniusLift F Y₀ x (localExtensionPoint F Y₀ m hm y) →
      ∃ (hPy : DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
          ((localFrobeniusFibre F Y₀ ell E n (localExtensionPoint F Y₀ m hm y)).obj
            K.carrier.obj))
        (hPx : DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
          ((localFrobeniusFibre F Y₀ ell E n
            (localExtensionPoint F Y₀ (Y₀.hom.degreeOver x) hd xₘ)).obj K.carrier.obj)),
        DerivedCategory.perfectCategoricalTrace _ hPy
            (condensedLocalFrobenius F Y₀ ell hEll E n hn m hm ⟨y⟩ K) =
          DerivedCategory.perfectCategoricalTrace _ hPx
            ((condensedLocalFrobenius F Y₀ ell hEll E n hn
              (Y₀.hom.degreeOver x) hd ⟨xₘ⟩ K) ^ (m / Y₀.hom.degreeOver x)) := by
  sorry

end WeilConjectures.CondensedFrobeniusOperators
