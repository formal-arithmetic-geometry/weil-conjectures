/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityOpenFieldExchange
public import WeilConjectures.WeilSheaf.SmoothPurityOpenAmbientMate
public import WeilConjectures.WeilSheaf.SmoothPurityEtaleExchangeRestriction
public import WeilConjectures.WeilSheaf.SmoothPurityOpenAdjunctionTransport
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeEtale
public import WeilConjectures.CategoryTheory.ObjectProperty.FullSubcategoryEqToHom

/-! # The mate of the specified bounded open base-change isomorphism -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}

/-- The cross-field square comparison restricts the actual ambient pullback comparison. -/
lemma purity_upperStarOfMapSquareIso_hom_app_hom
    (sq : CommSq πX f'.left f.left πY)
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((upperStarOfMapSquareIso ℓ f f' sq.w).hom.app K).hom =
      (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq.flip).hom.app K.obj := by
  simp only [upperStarOfMapSquareIso, pullbackSquareComparison, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    eqToIso.hom, eqToHom_app, ObjectProperty.FullSubcategory.eqToHom_hom']
  rfl

variable [IsOpenImmersion f.left] [IsOpenImmersion f'.left]

/-- The chosen adjunction for an open immersion is the extension-by-zero adjunction
transported through the library's compactification independence isomorphism. -/
lemma purity_boundedOpenAdjunction_eq :
    boundedConstructibleOpenImmersionUpperStarAdjunction ℓ f =
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ f).ofNatIsoLeft
          (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f).symm := by
  exact Adjunction.purity_ofNatIsoRight_conjugate
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ f)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f)

variable [WeaklyEtale πY] (sq : IsPullback πX f'.left f.left πY)

/-- The inverse restricted extension-by-zero comparison is the restricted left exchange. -/
lemma purityOpenFieldExtensionExchange_inv :
    (purityOpenFieldExtensionExchange ℓ f f' sq).inv =
      Adjunction.exchangeLeft
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ f)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ f')
        (upperStarOfMapSquareIso ℓ f f' sq.w) := by
  have : WeaklyEtale πX := MorphismProperty.of_isPullback sq.flip ‹WeaklyEtale πY›
  ext K
  apply ObjectProperty.hom_ext
  have he := Adjunction.purity_exchangeLeft_restrictFullyFaithful_app_hom
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) f.left).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion
        (Profinite.padicAlgClRingObj ℓ) f.left).symm)
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (Profinite.padicAlgClRingObj ℓ) f'.left).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion
        (Profinite.padicAlgClRingObj ℓ) f'.left).symm)
    (pullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) sq.toCommSq.flip)
    (fun K ↦ boundedConstructible_openImmersionLowerShriek_obj _ ℓ f K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f K)
    (fun K ↦ boundedConstructible_openImmersionLowerShriek_obj _ ℓ f' K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj _ ℓ f' K)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πX K.obj K.property)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ πY K.obj K.property)
    (upperStarOfMapSquareIso ℓ f f' sq.w)
    (purity_upperStarOfMapSquareIso_hom_app_hom ℓ f f' sq.toCommSq) K
  rw [purityOpenAmbientExchange_eq _ sq] at he
  exact he.symm

/-- The inverse of the specified compact-support open exchange is the canonical inverse mate. -/
lemma purityOpenFieldLowerShriekExchange_inv :
    (purityOpenFieldLowerShriekExchange ℓ f f' sq).inv =
      Adjunction.exchangeLeft
        (boundedConstructibleOpenImmersionUpperStarAdjunction ℓ f)
        (boundedConstructibleOpenImmersionUpperStarAdjunction ℓ f')
        (upperStarOfMapSquareIso ℓ f f' sq.w) := by
  rw [purity_boundedOpenAdjunction_eq, purity_boundedOpenAdjunction_eq]
  apply (cancel_mono (Functor.whiskerRight
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f).hom
    (boundedConstructibleUpperStarOfMap ℓ πY))).mp
  rw [Adjunction.purity_exchangeLeft_ofNatIsoLeft]
  simp only [purityOpenFieldLowerShriekExchange, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Iso.symm_inv, Category.assoc,
    ← Functor.whiskerRight_comp, Iso.inv_hom_id, Functor.whiskerRight_id, Category.comp_id,
    purityOpenFieldExtensionExchange_inv]

/-- Step A: the mate of the specified bounded open exchange is exactly the pullback square. -/
theorem purityOpenFieldLowerShriekExchange_hEx :
    (mateEquiv (boundedConstructibleOpenImmersionUpperStarAdjunction ℓ f)
      (boundedConstructibleOpenImmersionUpperStarAdjunction ℓ f')
      (inv (purityOpenFieldLowerShriekExchange ℓ f f' sq).hom)).natTrans =
        (upperStarOfMapSquareIso ℓ f f' sq.w).hom := by
  rw [IsIso.Iso.inv_hom, purityOpenFieldLowerShriekExchange_inv,
    Adjunction.purity_exchangeLeft_eq_inverseMate]
  exact congrArg TwoSquare.natTrans ((mateEquiv
    (boundedConstructibleOpenImmersionUpperStarAdjunction ℓ f)
    (boundedConstructibleOpenImmersionUpperStarAdjunction ℓ f')).apply_symm_apply
      (TwoSquare.mk _ _ _ _ (upperStarOfMapSquareIso ℓ f f' sq.w).hom))

end AlgebraicGeometry.ProEtale.CondensedRing
