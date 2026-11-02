/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Torsion normal form on a perfect chart

On a chart where a complete integral complex is the completed realization of a perfect
complex over the valuation ring, its cohomology splits as a finite free sheaf and a
nilpotent-uniformizer torsion sheaf, and the cokernel of the uniformizer on the torsion
part is a quotient of the consecutive-quotient Tor sheaf.

Source: Bhatt--Scholze, Proposition 6.6.11; the elementary-divisor calculation in step 5
of `lem-weil-pbc-adic-tor-implies-flat-cohomology`
(blueprint: lem-weil-pbc-integral-cohomology-torsion-normal-form).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

/-- The torsion normal form on one perfect chart.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-cohomology-torsion-normal-form).
Proof: the perfect complex splits over the valuation ring as the sum of its shifted
cohomology modules; its degree-q cohomology is a finite free module plus a torsion module
killed by a power of the uniformizer. Inverse image and completed realization are exact,
so this gives the splitting of the cohomology sheaf; the uniformizer is nilpotent on the
torsion part. The consecutive-quotient Tor sheaf of the torsion summand is the realization
of its reduction modulo the uniformizer, which is the cokernel of the uniformizer. -/
theorem torsion_normal_form_chart (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {S : Scheme.{u}} (g : S ⟶ T)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))))
    (q : ℤ)
    (C : completedConstantDerived (ModuleCat.{u + 1} (PbcIntegralRing l E)))
    (hC : @DerivedCategory.IsPerfectRingComplex _ _ (HasDerivedCategory.standard _) C)
    (e : (adicTowerPullback g (pbcAdicCompletion T (pbcIntegralDatum l E))).obj K ≅
      (adicTowerPullback g (pbcAdicCompletion T (pbcIntegralDatum l E))).obj
        ((integralConstantDerived T (pbcIntegralDatum l E)).obj C)) :
    let d := pbcIntegralDatum l E
    let B := pbcAdicCompletion T d
    let tor (n : ℕ) := (DerivedCategory.homologyFunctor _ (-1)).obj
      ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((pbcCompletedReduction T d (n + 1)).obj K))))
    let B' := (adicTowerInverseImage g).obj B
    let P := proEtaleRingModulePullback g B B' (Iso.refl _)
    ∃ (r : ℕ) (F N : pbcModules S B'),
      (∀ U : S.ProEtᵒᵖ, Nonempty (Module.Basis (Fin r) (B'.obj.obj U) (F.val.obj U))) ∧
      Nonempty (P.obj ((DerivedCategory.homologyFunctor _ q).obj K) ≅ F ⊞ N) ∧
      ∃ f : End N, IsNilpotent f ∧ ∃ n : ℕ,
        ∃ t : (pbcRestrict ((adicTowerInverseImage g).map
            (pbcAdicProjection T d n))).obj
          ((proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
            ((adicTowerInverseImage g).obj ((pbcAdicRings T d).obj (op n)))
            (Iso.refl _)).obj (tor n)) ⟶ cokernel f,
          Epi t := by
  sorry

end AlgebraicGeometry.Scheme
