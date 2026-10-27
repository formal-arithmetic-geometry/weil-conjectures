/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Canonical divisorial logarithms of a rank-one Kummer presentation

Source: ILO, Exposé VI 2.1--2.2, pp.71--72, and Exposé XVI 3.7, p.254.
(blueprint: lem-per-trait-kummer-divisorial-log-etale)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Polynomial

namespace AlgebraicGeometry

/-- A uniformizer Kummer presentation realizes the canonical divisorial structures
as fs log schemes, and the specified coefficient inclusion as a log-étale morphism.

Source: ILO VI 2.1--2.2, pp.71--72; XVI 3.7, p.254.
(blueprint: lem-per-trait-kummer-divisorial-log-etale).

Proof: Give Spec A and Spec B the divisorial log presheaves of their generic-point
inclusions. Étale descent for invertibility makes these monoid presheaves sheaves;
the inverse image of the units is exactly the structure sheaf of units. A
uniformizer gives the chart N -> M, 1 mapping to the uniformizer. At the closed
geometric point, strict henselian sections equal the stalk, and every nonzero
DVR element is uniquely a unit times a nonnegative uniformizer power. At the
generic point the uniformizer is a unit. Thus these are charts for the prescribed
log structures, and N is fine and saturated. Pullback of regular functions gives
the log map over Spec(algebraMap A B), since nonzero elements remain nonzero.
The equation tau^n = pi makes its chart homomorphism multiplication by n.
Its group completion is multiplication by n on Z; positivity makes the kernel
zero and the cokernel Z/nZ, of unit order on every source stalk. The comparison
has coordinate ring A tensor Z[x] over Z[z], where z maps to pi and x^n.
The maps sending x to its polynomial class and back identify this tensor ring
with A[X]/(X^n-C pi). The given evaluation equivalence therefore makes the
comparison an isomorphism, hence étale. This global chart covers the source and
proves log étaleness. The construction supplies the displayed isomorphisms of
monoid presheaves commuting with their actual structural inclusions. -/
theorem trait_kummer_divisorial_logEtale
    (A B : Type u) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsStrictlyHenselianLocalRing A] [IsStrictlyHenselianLocalRing B]
    [Algebra A B] (hinj : Function.Injective (algebraMap A B))
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : A))
    (pi : A) (hpi : Irreducible pi) (tau : B) (htau : Irreducible tau)
    (hpow : tau ^ n = algebraMap A B pi)
    (e : (A[X] ⧸ Ideal.span {X ^ n - C pi}) ≃ₐ[A] B)
    (he : ∀ Q : A[X], e (Ideal.Quotient.mk _ Q) = aeval tau Q) :
    ∃ (SB T : FineSaturatedLogScheme.{u})
      (eB : SB.scheme ≅ Spec (.of B))
      (eT : T.scheme ≅ Spec (.of A))
      (q : EtaleLogHom SB T),
      (∃ e : SB.logStructure.monoidSheaf.obj ≅ divisorialLogPresheaf
          (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) ≫ eB.inv),
        e.hom ≫ divisorialStructuralMap
          (Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) ≫ eB.inv) =
            SB.logStructure.alpha) ∧
      (∃ e : T.logStructure.monoidSheaf.obj ≅ divisorialLogPresheaf
          (Spec.map (CommRingCat.ofHom (algebraMap A
            (FractionRing A))) ≫ eT.inv),
        e.hom ≫ divisorialStructuralMap
          (Spec.map (CommRingCat.ofHom (algebraMap A
            (FractionRing A))) ≫ eT.inv) =
              T.logStructure.alpha) ∧
      q.base ≫ eT.hom = eB.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) ∧
      q.IsLogEtale := by sorry

end AlgebraicGeometry
