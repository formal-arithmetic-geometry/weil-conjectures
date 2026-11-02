/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.IdIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionShift

/-!
# The étale reading of the reduction `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` commutes with the shifts

The comparison `Ψ(ρ M) ⟶ ρ((𝒪_E ⧸ ℓⁿ) ⊗ᴸ M)` between the derived extension of scalars of the étale
reading `ρ` of a bounded constructible condensed `𝒪_E ⧸ ℓⁿ⁺¹`-complex `M` and the étale reading of
its condensed extension of scalars (`ProEtale.CondensedRing.finiteEtaleReadingExtendScalarsMap`)
commutes with the shifts.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

section Equivalence

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

/-- The inverse of the identification of the two derived models of finite coefficients commutes
with the shifts, for any finite discrete coefficient ring. -/
noncomputable instance commShift_finiteCoefficientDerivedEquivalence_inverse_of_commRing :
    (finiteCoefficientDerivedEquivalence X T).inverse.CommShift ℤ :=
  inferInstanceAs (D((finiteCoefficientModEquivalence X T).inverse).CommShift ℤ)

/-- The identification of the two derived models of finite coefficients commutes with the
shifts. -/
instance commShift_finiteCoefficientDerivedEquivalence :
    (finiteCoefficientDerivedEquivalence X T).CommShift ℤ :=
  Equivalence.CommShift.mk' _ ℤ (by
    have : NatTrans.CommShift (Equivalence.adjointifyη
        ((Functor.mapDerivedCategoryIdIso _).symm ≪≫
          Functor.mapDerivedCategoryNatIso (finiteCoefficientModEquivalence X T).unitIso ≪≫
          Functor.mapDerivedCategoryCompIso _ _)
        ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
          Functor.mapDerivedCategoryNatIso (finiteCoefficientModEquivalence X T).counitIso ≪≫
          Functor.mapDerivedCategoryIdIso _)).hom ℤ := by
      dsimp only [Equivalence.adjointifyη, Trans.trans]
      infer_instance
    exact this)

end Equivalence

section ExtendScalars

variable (X : Scheme.{u}) {T T' : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T']
  [DiscreteTopology T'] [Finite T'] {ρ : T →+* T'} (hρ : Function.Surjective ρ)
  {a : ULift.{u + 1} T} (ha : RingHom.ker ρ.ulift = Ideal.span {a})

/-- The compatibility of the derived extensions of scalars with the identification of the two
derived models of finite coefficients commutes with the shifts: it is a conjugate of an
isomorphism of exact functors. -/
instance commShift_finiteCoefficientDerivedEquivalenceExtendScalarsIso_hom :
    NatTrans.CommShift (finiteCoefficientDerivedEquivalenceExtendScalarsIso X hρ ha).hom ℤ := by
  dsimp only [finiteCoefficientDerivedEquivalenceExtendScalarsIso,
    finiteCoefficientDerivedEquivalenceComapIso, Iso.isoCompInverse]
  infer_instance

end ExtendScalars

end AlgebraicGeometry.ProEtale
