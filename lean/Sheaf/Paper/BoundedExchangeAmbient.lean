/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.OverSquare

public import Sheaf.Paper.IntegralResidueComparisons
public import Sheaf.CategoryTheory.Functor.TransportedCompositeIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

/-! # The specified bounded exchange viewed in the ambient category

Source: the defining unit-square-counit formula for boundedConstructibleBaseChange.
(blueprint: lem-weil-pbc-bounded-exchange-ambient)
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The ambient pullback square uses precisely the library's composition constraints.
Source: the composition constraints used in MorphismDefs.
(blueprint: def-weil-pbc-residue-exchange-ambient). -/
noncomputable def residueExchangeSquare (sq : CommSq g' f' f g) :
    residueExchangeUpperStar Λ g ⋙ residueExchangeUpperStar Λ f' ≅
      residueExchangeUpperStar Λ f ⋙ residueExchangeUpperStar Λ g' :=
  transportedCompositeIso (residueExchangeUpperStarComp Λ f' g).symm
    (residueExchangeUpperStarComp Λ g' f)
    (congrArg (fun h : X' ⟶ Y ↦ residueExchangeUpperStar Λ h) sq.w.symm)

/-- The ambient exchange is the adjunction mate of the pullback-square comparison.
Source: the unit-square-counit definition of exchange.
(blueprint: def-weil-pbc-residue-exchange-ambient). -/
noncomputable def residueExchangeBaseChange (sq : CommSq g' f' f g) :
    residueExchangeLowerStar Λ f ⋙ residueExchangeUpperStar Λ g ⟶
      residueExchangeUpperStar Λ g' ⋙ residueExchangeLowerStar Λ f' :=
  (mateEquiv (residueExchangeAdjunction Λ f)
    (residueExchangeAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (residueExchangeSquare Λ sq).hom)).natTrans

/-- The counit equation characterizing the ambient exchange mate.
Source: Mathlib, mateEquiv_counit.
(blueprint: lem-weil-pbc-residue-exchange-counit)
Proof. Apply the mates equivalence's counit identity to the pullback-square comparison.
-/
theorem residueExchangeBaseChange_counit (sq : CommSq g' f' f g)
    (K : residueExchangeDerived Λ X) :
    (residueExchangeUpperStar Λ f').map ((residueExchangeBaseChange Λ sq).app K) ≫
      (residueExchangeAdjunction Λ f').counit.app
        ((residueExchangeUpperStar Λ g').obj K) =
    (residueExchangeSquare Λ sq).hom.app ((residueExchangeLowerStar Λ f).obj K) ≫
      (residueExchangeUpperStar Λ g').map ((residueExchangeAdjunction Λ f).counit.app K) := by
  exact mateEquiv_counit (residueExchangeAdjunction Λ f)
    (residueExchangeAdjunction Λ f')
    (TwoSquare.mk _ _ _ _ (residueExchangeSquare Λ sq).hom) K

variable (ℓ : ℕ) [Fact ℓ.Prime] [IsFinitenessCoefficient ℓ Λ] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar
  residueExchangeAdjunction residueExchangeUpperStarComp

private theorem bounded_counit_hom (K : ProEtale.BoundedConstructible
    (condensedRingObj Λ X)) :
    ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ
      (f.asOver (Spec (.of k)))).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ f).counit.app K.obj := by
  have h := Adjunction.map_restrictFullyFaithful_counit_app
    (derivedUpperStarLowerStarAdjunction Λ f)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility Λ ℓ (f.asOver (Spec (.of k)))).symm
    (boundedConstructibleLowerStarCompatibility Λ ℓ (f.asOver (Spec (.of k)))).symm K
  change ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ
      (f.asOver (Spec (.of k)))).counit.app K).hom =
    𝟙 _ ≫ (L((f)^*⟦Λ⟧)).map (𝟙 _) ≫
      (derivedUpperStarLowerStarAdjunction Λ f).counit.app K.obj at h
  rw [(L((f)^*⟦Λ⟧)).map_id] at h
  simpa only [Category.id_comp] using h


omit [IsFinitenessCoefficient ℓ Λ] in
private theorem bounded_comp_hom {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] (h : Y ⟶ Z) [h.IsOver (Spec (.of k))]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ Z)) :
    ((boundedConstructibleUpperStarComp Λ ℓ (f.asOver (Spec (.of k)))
      (h.asOver (Spec (.of k)))).hom.app K).hom =
      (residueExchangeUpperStarComp Λ f h).hom.app K.obj := by
  simp only [Functor.comp_obj, boundedConstructibleUpperStarComp,
    CategoryTheory.Functor.FullyFaithful.preimageIso,
    CategoryTheory.Functor.FullyFaithful.whiskeringRight, Functor.whiskeringRight_obj_obj,
    boundedConstructibleUpperStarCompatibility, ObjectProperty.liftCompιIso, Iso.trans_hom,
    Iso.refl_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Iso.refl_inv, CategoryTheory.Functor.FullyFaithful.preimage_comp, NatTrans.id_app,
    ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    CategoryTheory.Functor.map_id, Functor.associator_hom_app, Category.comp_id,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv, Category.assoc,
    Functor.isoWhiskerRight_inv, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.homMk_hom, residueExchangeUpperStarComp, id_eq]
  exact Category.id_comp _

private theorem subcat_iso_inv {C : Type*} [Category C] {P : ObjectProperty C}
    {A B : P.FullSubcategory} (e : A ≅ B) (d : A.obj ≅ B.obj)
    (h : e.hom.hom = d.hom) : e.inv.hom = d.inv := by
  apply Iso.inv_ext'
  rw [← h]
  exact ObjectProperty.isoHom_inv_id_hom e

omit [IsFinitenessCoefficient ℓ Λ] in
private theorem bounded_comp_inv_hom {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] (h : Y ⟶ Z) [h.IsOver (Spec (.of k))]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ Z)) :
    ((boundedConstructibleUpperStarComp Λ ℓ (f.asOver (Spec (.of k)))
      (h.asOver (Spec (.of k)))).inv.app K).hom =
      (residueExchangeUpperStarComp Λ f h).inv.app K.obj := by
  exact subcat_iso_inv ((boundedConstructibleUpperStarComp Λ ℓ
    (f.asOver (Spec (.of k))) (h.asOver (Spec (.of k)))).app K)
    ((residueExchangeUpperStarComp Λ f h).app K.obj) (bounded_comp_hom Λ ℓ k h K)

omit [IsFinitenessCoefficient ℓ Λ] in
private theorem bounded_transport_obj_hom
    (h i : X' ⟶ Y) [h.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
    (w : h = i)
    (hf : boundedConstructibleUpperStar Λ ℓ (h.asOver (Spec (.of k))) =
      boundedConstructibleUpperStar Λ ℓ (i.asOver (Spec (.of k))))
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ Y)) :
    (eqToHom (congrArg (fun F : ProEtale.BoundedConstructible (condensedRingObj Λ Y) ⥤
        ProEtale.BoundedConstructible (condensedRingObj Λ X') ↦ F.obj K) hf)).hom =
      eqToHom (congrArg
        (fun t : X' ⟶ Y ↦ (residueExchangeUpperStar Λ t).obj K.obj) w) := by
  cases w
  rfl

omit [IsFinitenessCoefficient ℓ Λ] in
private theorem bounded_square_hom (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ Y)) :
    ((boundedConstructiblePullbackSquareComparison Λ ℓ (sq.asOver (Spec (.of k)))).hom.app K).hom =
      (residueExchangeSquare Λ sq).hom.app K.obj := by
  let hB : boundedConstructibleUpperStar Λ ℓ ((f' ≫ g).asOver (Spec (.of k))) =
      boundedConstructibleUpperStar Λ ℓ ((g' ≫ f).asOver (Spec (.of k))) := by simp only [sq.w]
  have hs : boundedConstructiblePullbackSquareComparison Λ ℓ (sq.asOver (Spec (.of k))) =
      transportedCompositeIso (boundedConstructibleUpperStarComp Λ ℓ
        (f'.asOver (Spec (.of k))) (g.asOver (Spec (.of k)))).symm
        (boundedConstructibleUpperStarComp Λ ℓ (g'.asOver (Spec (.of k)))
          (f.asOver (Spec (.of k)))) hB :=
    (transportedCompositeIso_eq (boundedConstructibleUpperStarComp Λ ℓ
      (f'.asOver (Spec (.of k))) (g.asOver (Spec (.of k)))).symm
      (boundedConstructibleUpperStarComp Λ ℓ (g'.asOver (Spec (.of k)))
        (f.asOver (Spec (.of k)))) hB).symm
  rw [hs]
  dsimp only [transportedCompositeIso, residueExchangeSquare,
    NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    ObjectProperty.FullSubcategory.comp_hom, eqToIso.hom]
  rw [bounded_comp_inv_hom Λ ℓ k (f := f') g K,
    bounded_comp_hom Λ ℓ k (f := g') f K,
    bounded_transport_obj_hom Λ ℓ k _ _ sq.w.symm hB K]

set_option maxHeartbeats 400000 in
-- Elaborate the bundled square while retaining the original exchange equality.
/-- Inclusion identifies the specified bounded exchange with the ambient adjunction mate.

Source: the defining three-step formula in MorphismDefs and Mathlib adjunction restriction.
(blueprint: lem-weil-pbc-bounded-exchange-ambient)

Proof. Apply injectivity of the ambient f-prime inverse hom equivalence. The existing
bounded exchange adjunct equation gives the restricted square followed by the pulled
counit. Fully faithful restriction has the same underlying counit because its
compatibility isomorphisms are identities. The restricted pull-composition constraints
likewise have the original underlying components. Equality transport commutes with
inclusion, so the square comparison has the ambient component. Substituting these
component identities gives the ambient mate counit equation, hence the desired equality.
This identification requires no properness and does not assert invertibility. -/
theorem boundedConstructibleBaseChange_hom_eq_ambient (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((boundedConstructibleBaseChange Λ ℓ (sq.asOver (Spec (.of k)))).app K).hom =
      (residueExchangeBaseChange Λ sq).app K.obj := by
  apply ((residueExchangeAdjunction Λ f').homEquiv _ _).symm.injective
  change (residueExchangeUpperStar Λ f').map
      (((boundedConstructibleBaseChange Λ ℓ (sq.asOver (Spec (.of k)))).app K).hom) ≫
      (residueExchangeAdjunction Λ f').counit.app
        ((residueExchangeUpperStar Λ g').obj K.obj) =
    (residueExchangeUpperStar Λ f').map ((residueExchangeBaseChange Λ sq).app K.obj) ≫
      (residueExchangeAdjunction Λ f').counit.app
        ((residueExchangeUpperStar Λ g').obj K.obj)
  have h := congrArg (fun z ↦ z.hom)
    (boundedConstructibleBaseChange_adjunct Λ ℓ (sq.asOver (Spec (.of k))) K)
  change (residueExchangeUpperStar Λ f').map
      (((boundedConstructibleBaseChange Λ ℓ (sq.asOver (Spec (.of k)))).app K).hom) ≫
      ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (f'.asOver (Spec (.of k)))).counit.app
        ((boundedConstructibleUpperStar Λ ℓ (g'.asOver (Spec (.of k)))).obj K)).hom =
    ((boundedConstructiblePullbackSquareComparison Λ ℓ (sq.asOver (Spec (.of k)))).hom.app
      ((boundedConstructibleLowerStar Λ ℓ (f.asOver (Spec (.of k)))).obj K)).hom ≫
      (residueExchangeUpperStar Λ g').map
        (((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ
          (f.asOver (Spec (.of k)))).counit.app K).hom) at h
  rw [bounded_counit_hom Λ ℓ k, bounded_square_hom Λ ℓ k sq,
    bounded_counit_hom Λ ℓ k] at h
  exact h.trans (residueExchangeBaseChange_counit Λ sq K.obj).symm

end AlgebraicGeometry.ProEtale.CondensedRing
