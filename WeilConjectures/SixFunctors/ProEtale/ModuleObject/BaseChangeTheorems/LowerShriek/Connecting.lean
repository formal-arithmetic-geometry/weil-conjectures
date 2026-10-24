/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Shift.ConnectingLift
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

/-!
# The compact-support base change commutes with the connecting morphisms

The six functors on the bounded constructible derived categories `Dᵇc(X)⟦Λ⟧` are restrictions
of functors on the ambient derived categories `D(Mod_{Λ_X})` which commute with the shifts
(`CategoryTheory.Functor.ShiftLift`). A morphism `δ : K ⟶ M[1]` of the ambient derived category
between bounded constructible complexes is therefore sent by each of them to a morphism of the
same form (`CategoryTheory.Functor.ShiftLift.connecting`), for instance the connecting morphism
of a distinguished triangle.

This file shows that the natural transformations of the six-functor formalism on `Dᵇc(-)⟦Λ⟧`
built from units and counits of the restricted adjunctions and from composition isomorphisms
commute with these connecting morphisms (`CategoryTheory.NatTrans.CommConnecting`). In
particular so does the compact-support base change morphism
(`ProEtale.CondensedRing.commConnecting_boundedConstructibleLowerShriekBaseChange_padicAlgCl`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-! ### The lifts of the six functors -/

section Lifts

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The derived pullback on `Dᵇc` lifts the derived pullback `L((f)^*⟦Λ⟧)`. -/
noncomputable instance shiftLift_boundedConstructibleUpperStar (f : X ⟶ Y) :
    Functor.ShiftLift (boundedConstructible (condensedRingObj Λ Y.left)).ι
      (boundedConstructibleUpperStar Λ ℓ f) (boundedConstructible (condensedRingObj Λ X.left)).ι
    where
  lift := L((f.left)^*⟦Λ⟧)
  iso := boundedConstructibleUpperStarCompatibility Λ ℓ f

/-- The derived pushforward on `Dᵇc` lifts the derived pushforward `R((f)_*⟦Λ⟧)`. -/
noncomputable instance shiftLift_boundedConstructibleLowerStar [IsFinitenessCoefficient ℓ Λ]
    (f : X ⟶ Y) :
    Functor.ShiftLift (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleLowerStar Λ ℓ f) (boundedConstructible (condensedRingObj Λ Y.left)).ι
    where
  lift := R((f.left)_*⟦Λ⟧)
  iso := boundedConstructibleLowerStarCompatibility Λ ℓ f

/-- The extension by zero on `Dᵇc` lifts the levelwise extension by zero `D((j)_!open⟦Λ⟧)`. -/
noncomputable instance shiftLift_boundedConstructibleOpenImmersionLowerShriek (j : X ⟶ Y)
    [IsOpenImmersion j.left] :
    Functor.ShiftLift (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j)
      (boundedConstructible (condensedRingObj Λ Y.left)).ι where
  lift := D((j.left)_!open⟦Λ⟧)
  iso := boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j

/-- The lower shriek `Rf_!^c = i_! ⋙ Rp_*` on `Dᵇc` lifts `Rf_!(c)⟦Λ⟧`. -/
noncomputable instance shiftLift_boundedConstructibleLowerShriekOfCompactification
    [IsFinitenessCoefficient ℓ Λ] {f : X ⟶ Y} (c : Compactification f.left) :
    Functor.ShiftLift (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleLowerShriekOfCompactification Λ ℓ c)
      (boundedConstructible (condensedRingObj Λ Y.left)).ι :=
  inferInstanceAs (Functor.ShiftLift _ (boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.overI ⋙
    boundedConstructibleLowerStar Λ ℓ c.overG) _)

/-- The lower shriek `Rf_!` on `Dᵇc` lifts `R(f)_!⟦Λ⟧`. -/
noncomputable instance shiftLift_boundedConstructibleLowerShriek [IsFinitenessCoefficient ℓ Λ]
    (f : X ⟶ Y) :
    Functor.ShiftLift (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleLowerShriek Λ ℓ f)
      (boundedConstructible (condensedRingObj Λ Y.left)).ι :=
  inferInstanceAs (Functor.ShiftLift _
    (boundedConstructibleLowerShriekOfCompactification Λ ℓ (compactificationOverField f)) _)

end Lifts

/-! ### The units, counits and composition isomorphisms -/

section Leaves

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The unit of `Lf^* ⊣ Rf_*` on `Dᵇc` commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleUpperStarLowerStarAdjunction_unit
    [IsFinitenessCoefficient ℓ Λ] (f : X ⟶ Y) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ Y.left)).ι
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).unit := by
  let adj : Functor.ShiftLift.lift (boundedConstructible (condensedRingObj Λ Y.left)).ι
      (boundedConstructibleUpperStar Λ ℓ f) ⊣ Functor.ShiftLift.lift
        (boundedConstructible (condensedRingObj Λ X.left)).ι
          (boundedConstructibleLowerStar Λ ℓ f) :=
    derivedUpperStarLowerStarAdjunction Λ f.left
  have : adj.CommShift ℤ :=
    commShift_derivedUpperStarLowerStarAdjunction Λ f.left
  exact NatTrans.CommConnecting.restrictFullyFaithful_unit adj (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.fullyFaithfulι _)

/-- The counit of `Lf^* ⊣ Rf_*` on `Dᵇc` commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleUpperStarLowerStarAdjunction_counit
    [IsFinitenessCoefficient ℓ Λ] (f : X ⟶ Y) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).counit := by
  let adj : Functor.ShiftLift.lift (boundedConstructible (condensedRingObj Λ Y.left)).ι
      (boundedConstructibleUpperStar Λ ℓ f) ⊣ Functor.ShiftLift.lift
        (boundedConstructible (condensedRingObj Λ X.left)).ι
          (boundedConstructibleLowerStar Λ ℓ f) :=
    derivedUpperStarLowerStarAdjunction Λ f.left
  have : adj.CommShift ℤ :=
    commShift_derivedUpperStarLowerStarAdjunction Λ f.left
  exact NatTrans.CommConnecting.restrictFullyFaithful_counit adj (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.fullyFaithfulι _)

/-- The unit of `j_! ⊣ Lj^*` on `Dᵇc` commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit := by
  let adj : Functor.ShiftLift.lift (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j) ⊣ Functor.ShiftLift.lift
        (boundedConstructible (condensedRingObj Λ Y.left)).ι
          (boundedConstructibleUpperStar Λ ℓ j) :=
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j.left).symm
  have : adj.CommShift ℤ :=
    commShift_derivedOpenImmersionLowerShriekUpperStarAdjunction_ofNatIsoRight Λ j.left
  exact NatTrans.CommConnecting.restrictFullyFaithful_unit adj (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.fullyFaithfulι _)

/-- The counit of `j_! ⊣ Lj^*` on `Dᵇc` commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_counit
    (j : X ⟶ Y) [IsOpenImmersion j.left] :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ Y.left)).ι
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).counit := by
  let adj : Functor.ShiftLift.lift (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j) ⊣ Functor.ShiftLift.lift
        (boundedConstructible (condensedRingObj Λ Y.left)).ι
          (boundedConstructibleUpperStar Λ ℓ j) :=
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j.left).symm
  have : adj.CommShift ℤ :=
    commShift_derivedOpenImmersionLowerShriekUpperStarAdjunction_ofNatIsoRight Λ j.left
  exact NatTrans.CommConnecting.restrictFullyFaithful_counit adj (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.fullyFaithfulι _)

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`
commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleUpperStarComp_hom {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ Z.left)).ι
      (boundedConstructibleUpperStarComp Λ ℓ f g).hom :=
  NatTrans.CommConnecting.of_ambient _ (leftDerivedUpperStarComp Λ f.left g.left).hom fun c ↦ by
    simp only [ObjectProperty.ι_obj, Functor.comp_obj, boundedConstructibleUpperStarComp,
      Functor.whiskeringRight_obj_obj, Over.comp_left, boundedConstructibleUpperStarCompatibility,
      Functor.FullyFaithful.preimageIso_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.FullyFaithful.whiskeringRight_preimage_app,
      NatTrans.comp_app, ObjectProperty.liftCompιIso_hom_app, ObjectProperty.lift_obj_obj,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      ObjectProperty.liftCompιIso_inv_app, CategoryTheory.Functor.map_id,
      Functor.associator_hom_app, Category.comp_id, ObjectProperty.ι_map, ObjectProperty.homMk_hom,
      Functor.ShiftLift.e, Functor.ShiftLift.iso, Category.id_comp, Category.assoc]
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`
commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleLowerStarComp_hom [IsFinitenessCoefficient ℓ Λ]
    {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleLowerStarComp Λ ℓ f g).hom := by
  have e : (boundedConstructibleLowerStarComp Λ ℓ f g).hom = conjugateEquiv
      ((boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ g).comp
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f))
      (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ (f ≫ g))
      (boundedConstructibleUpperStarComp Λ ℓ f g).hom := rfl
  rw [e]
  exact NatTrans.CommConnecting.conjugateEquiv _ _ _

end Leaves

/-! ### The base change morphisms -/

section BaseChange

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback comparison of a commutative square commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructiblePullbackSquareComparison_hom
    (sq : CommSq g' f' f g) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ Y.left)).ι
      (boundedConstructiblePullbackSquareComparison Λ ℓ sq).hom := by
  have := NatTrans.CommConnecting.eqToHom_congrArg
    (ι := (boundedConstructible (condensedRingObj Λ Y.left)).ι)
    (fun h : X' ⟶ Y ↦ boundedConstructibleUpperStar Λ ℓ h) sq.w.symm
  have := NatTrans.CommConnecting.of_iso_inv
    (ι := (boundedConstructible (condensedRingObj Λ Y.left)).ι)
    (boundedConstructibleUpperStarComp Λ ℓ f' g)
  dsimp only [boundedConstructiblePullbackSquareComparison, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom]
  infer_instance

/-- The base change morphism `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*`
commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleBaseChange [IsFinitenessCoefficient ℓ Λ]
    (sq : CommSq g' f' f g) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleBaseChange Λ ℓ sq) := by
  rw [boundedConstructibleBaseChange_eq_exchangeRight]
  dsimp only [Adjunction.exchangeRight]
  infer_instance

/-- The extension-by-zero exchange morphism commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleOpenImmersionLowerShriekBaseChange
    [IsOpenImmersion f.left] [IsOpenImmersion f'.left] (sq : CommSq g' f' f g) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq) := by
  have := commConnecting_boundedConstructiblePullbackSquareComparison_hom Λ ℓ sq.flip
  dsimp only [boundedConstructibleOpenImmersionLowerShriekBaseChange,
    boundedConstructibleOpenImmersionLowerShriekBaseChangeUnitStep,
    boundedConstructibleOpenImmersionLowerShriekBaseChangeSquareStep,
    boundedConstructibleOpenImmersionLowerShriekBaseChangeCounitStep]
  infer_instance

/-- The extension-by-zero exchange isomorphism commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleOpenImmersionLowerShriekBaseChangeIso_hom
    [IsOpenImmersion f.left] [IsOpenImmersion f'.left] (sq : IsPullback g' f' f g) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq).hom := by
  have := isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq
  have : NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ X.left)).ι
      (asIso (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq)).hom :=
    commConnecting_boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq
  exact NatTrans.CommConnecting.of_iso_inv
    (asIso (boundedConstructibleOpenImmersionLowerShriekBaseChange Λ ℓ sq.toCommSq))

end BaseChange

/-! ### Independence of the compactification -/

section Refinement

variable {X Z Z₁ : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom]
  [IsSeparated Z₁.hom]
  {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁} [IsOpenImmersion i.left] [IsOpenImmersion i₁.left]

/-- The triangle comparison `Li₁^* ≅ Lh^* ⋙ Li^*` commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleUpperStarTriangleComparison_hom
    (w : i ≫ h = i₁) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ Z₁.left)).ι
      (boundedConstructibleUpperStarTriangleComparison Λ ℓ w).hom := by
  have := NatTrans.CommConnecting.eqToHom_congrArg
    (ι := (boundedConstructible (condensedRingObj Λ Z₁.left)).ι)
    (fun e : X ⟶ Z₁ ↦ boundedConstructibleUpperStar Λ ℓ e) w.symm
  dsimp only [boundedConstructibleUpperStarTriangleComparison, Iso.trans_hom, eqToIso.hom]
  infer_instance

/-- The triangle transport step of the restriction comparison
commutes with the connecting morphisms. -/
noncomputable instance
    commConnecting_boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep_hom
    (w : i ≫ h = i₁) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep Λ ℓ w).hom := by
  dsimp only [boundedConstructibleOpenImmersionLowerShriekRefinementTriangleStep]
  refine NatTrans.CommConnecting.of_connecting_eq
    (inferInstanceAs (Functor.ShiftLift _ ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i₁ ⋙
      boundedConstructibleUpperStar Λ ℓ i₁) ⋙
        (𝟭 _ ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ i)) _)) _ _ _ _
    (NatTrans.CommConnecting.squareTransport_hom _ _ _) (fun δ ↦ ?_) (fun δ ↦ rfl)
  simp only [Functor.ShiftLift.connecting_comp]
  exact Functor.ShiftLift.connecting_id_comp
    (ι := (boundedConstructible (condensedRingObj Λ X.left)).ι)
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ i) _

/-- The restriction comparison `i_! ⟶ i₁_! ⋙ Lh^*` commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleOpenImmersionLowerShriekRefinement
    (w : i ≫ h = i₁) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ w) := by
  dsimp only [boundedConstructibleOpenImmersionLowerShriekRefinement,
    boundedConstructibleOpenImmersionLowerShriekRefinementUnitStep,
    boundedConstructibleOpenImmersionLowerShriekRefinementCounitStep]
  infer_instance

/-- The pushforward comparison `i₁_! ⟶ i_! ⋙ Rh_*` commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward
    [IsFinitenessCoefficient ℓ Λ] (sq : IsPullback (𝟙 X) i i₁ h) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ sq) := by
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinement Λ ℓ sq
  dsimp only [boundedConstructibleOpenImmersionLowerShriekRefinementPushforward]
  infer_instance

/-- The isomorphism `Rf_!^{c₁} ≅ Rf_!^c` along a refinement
commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleLowerShriekRefinementIso_hom
    [IsFinitenessCoefficient ℓ Λ] (sq : IsPullback (𝟙 X) i i₁ h) {Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {p₁ : Z₁ ⟶ Y} {p : Z ⟶ Y} (wp : h ≫ p₁ = p)
    [IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ sq)] :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleLowerShriekRefinementIso Λ ℓ sq wp).hom := by
  have := NatTrans.CommConnecting.eqToHom_congrArg
    (ι := (boundedConstructible (condensedRingObj Λ Z.left)).ι)
    (fun e : Z ⟶ Y ↦ boundedConstructibleLowerStar Λ ℓ e) wp
  dsimp only [boundedConstructibleLowerShriekRefinementIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, asIso_hom, eqToIso.hom]
  infer_instance

end Refinement

section Independence

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- The isomorphism `Rf_!^{c₁} ≅ Rf_!^c` along a refinement of compactifications commutes with
the connecting morphisms. -/
lemma commConnecting_boundedConstructibleLowerShriekRefinementIso_padicAlgCl_hom
    {c c₁ : Compactification f.left} (r : c.OverRefinement c₁) :
    haveI := r.isProper
    haveI := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
      r.isPullback
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj
        (Profinite.padicAlgClRingObj ℓ) X.left)).ι
      (boundedConstructibleLowerShriekRefinementIso _ ℓ r.isPullback r.hom_overG).hom := by
  have := r.isProper
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
    r.isPullback
  infer_instance

/-- The independence isomorphism `Rf_!^{c₁} ≅ Rf_!^{c₂}` commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_hom
    (c₁ c₂ : Compactification f.left) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj
        (Profinite.padicAlgClRingObj ℓ) X.left)).ι
      (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ c₁ c₂).hom := by
  have h₁ := commConnecting_boundedConstructibleLowerShriekRefinementIso_padicAlgCl_hom ℓ
    (Compactification.exists_overRefinement c₁ c₂).choose_spec.1.some
  have h₂ := commConnecting_boundedConstructibleLowerShriekRefinementIso_padicAlgCl_hom ℓ
    (Compactification.exists_overRefinement c₁ c₂).choose_spec.2.some
  have h₃ := NatTrans.CommConnecting.of_iso_inv (he := h₂)
  dsimp only [boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl]
  exact NatTrans.CommConnecting.of_comp h₁ h₃

end Independence

/-! ### The compact-support base change -/

section CompactSupport

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The compact-support base change for a compactification
commutes with the connecting morphisms. -/
instance commConnecting_boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
    [IsFinitenessCoefficient ℓ Λ] (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj Λ X.left)).ι
      (boundedConstructibleLowerShriekOfCompactificationBaseChangePasting Λ ℓ c sq) := by
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq]
  infer_instance

/-- **The compact-support base change commutes with the connecting morphisms**: for a cartesian
square `sq`, the base change morphism `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded
constructible `ℚ̄_ℓ`-sheaves commutes with the connecting morphisms transported through the
ambient derived functors, which commute with the shifts. -/
instance commConnecting_boundedConstructibleLowerShriekBaseChange_padicAlgCl
    (sq : IsPullback g' f' f g) :
    NatTrans.CommConnecting (boundedConstructible (condensedRingObj
        (Profinite.padicAlgClRingObj ℓ) X.left)).ι
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq) := by
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq]
  infer_instance

end CompactSupport

end AlgebraicGeometry.ProEtale.CondensedRing
