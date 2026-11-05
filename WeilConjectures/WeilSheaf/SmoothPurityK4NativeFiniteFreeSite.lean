/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteFreeSite
public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeFiniteFreePullback

/-! # Factoring the finite free-module comparison through the pro-étale site -/

set_option profiler true
set_option profiler.threshold 1

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj


namespace AlgebraicGeometry.ProEtale.K4Native

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (n : ℕ) (X : Scheme.{u})

noncomputable def comparisonUpperStarFreeIso :
    ν^*(X)[Ab.{u + 1}] ⋙ Mod.freeFunctor (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X) ⋙
        (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor ≅
      Etale.extendScalars (integersModPowCoeff.{u} ℓ E n) X ⋙
        ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)] :=
  (((comparisonAdjunction Ab.{u + 1} X).comp
    (Mod.freeForgetAdjunction (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X))).comp
      (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).toAdjunction).leftAdjointUniq
    (((Etale.extendScalarsAdjunction (integersModPowCoeff.{u} ℓ E n) X).comp
      (comparisonAdjunction _ X)).ofNatIsoRight
      ((NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)) ≪≫
        Functor.isoWhiskerRight (finiteCoefficientModEquivalenceInverseCompForgetIso (PadicAlgCl.integersModPow ℓ E n) X).symm
          ν_*(X)[Ab.{u + 1}]))


/-- Free sheaves commute with the comparison-site inverse image. -/
noncomputable def purityComparisonFreeSheafIso :
    ν^*(X)[Ab.{u + 1}] ⋙ purityFiniteFreeSheaf ℓ E n X ≅
      Etale.extendScalars (integersModPowCoeff.{u} ℓ E n) X ⋙
        ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)] :=
  (conjugateIsoEquiv
    ((Etale.extendScalarsAdjunction (integersModPowCoeff.{u} ℓ E n) X).comp (comparisonAdjunction _ X))
    ((comparisonAdjunction Ab.{u + 1} X).comp (purityFiniteFreeSheafAdjunction ℓ E n X))).symm
    (Iso.refl _)

/-- The existing finite-root free-module comparison factors through the ordinary
free sheaf and the comparison-site free-sheaf isomorphism. -/
lemma purity_comparisonUpperStarFreeIso_factor :
    comparisonUpperStarFreeIso ℓ E n X =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft ν^*(X)[Ab.{u + 1}] (purityFiniteCoefficientFreeIso ℓ E n X) ≪≫
        purityComparisonFreeSheafIso ℓ E n X := by
  unfold comparisonUpperStarFreeIso
  rw [CategoryTheory.purity_leftAdjointUniq_ofNatIsoRight]
  have h := purity_conjugate_comp_factor (comparisonAdjunction Ab.{u + 1} X)
    (Mod.freeForgetAdjunction (condensedRingObj (Profinite.integersModPowRingObj ℓ E n) X))
    (finiteCoefficientModEquivalence X (PadicAlgCl.integersModPow ℓ E n)).toAdjunction
    (purityFiniteFreeSheafAdjunction ℓ E n X)
    ((Etale.extendScalarsAdjunction (integersModPowCoeff.{u} ℓ E n) X).comp (comparisonAdjunction _ X))
    (finiteCoefficientModEquivalenceInverseCompForgetIso (PadicAlgCl.integersModPow ℓ E n) X).symm (Iso.refl _)
  refine Eq.trans ?_ h
  congr 1

/-- Component form of the factorization, without associator identities. -/
lemma purity_comparisonUpperStarFreeIso_hom_app
    (M : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    (comparisonUpperStarFreeIso ℓ E n X).hom.app M =
      (purityFiniteCoefficientFreeIso ℓ E n X).hom.app (ν^*(X)[Ab.{u + 1}].obj M) ≫
        (purityComparisonFreeSheafIso ℓ E n X).hom.app M := by
  rw [purity_comparisonUpperStarFreeIso_factor]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  erw [Category.id_comp]

end AlgebraicGeometry.ProEtale.K4Native
