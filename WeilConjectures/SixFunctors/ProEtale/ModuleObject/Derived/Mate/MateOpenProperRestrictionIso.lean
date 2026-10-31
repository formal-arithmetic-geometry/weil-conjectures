/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenSquareRestriction
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The specified open restriction mate is invertible
Source: blueprint det-sf-comp-composition-interchange, proof (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem mate_component
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {H : A ⥤ C} {H' : B ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (θ : TwoSquare H L L' H') (M : B) :
    (mateEquiv a b θ).natTrans.app M =
      b.homEquiv _ _ (θ.natTrans.app (R.obj M) ≫ H'.map (a.counit.app M)) := by
  simp [mateEquiv, Adjunction.homEquiv_unit]

private theorem inverse_mate_eq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {H : A ⥤ C} {H' : B ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (θ : R ⋙ H ≅ H' ⋙ R') (e : H ⋙ L' ≅ L ⋙ H')
    (he : ∀ M, b.unit.app (H.obj M) ≫ R'.map (e.hom.app M) =
      H.map (a.unit.app M) ≫ θ.hom.app (L.obj M)) :
    ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ θ.hom)).natTrans = e.hom := by
  apply NatTrans.ext
  funext M
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ θ.hom) M).symm.trans (he M).symm

set_option maxHeartbeats 800000 in
-- Concrete derived mate comparisons require extra elaboration heartbeats.
/-- Open restriction of derived direct image is the canonical pullback-counit mate.
Source: blueprint det-sf-comp-composition-interchange, proof (2)
(blueprint: lem-sfb-mate-open-proper-restriction-iso).

Proof: Exact open extension commutes with arbitrary inverse image, with its inverse
normalized by the pullback compositor and the open units. Descend this mate equation
termwise to derived categories. Conjugate that invertible left-adjoint square under
the two composite adjunctions. The iterated-mates identity identifies the result with
the pullback-counit mate defining mateOpenProperRestriction. This argument uses no
properness, boundedness, constructibility or completeness assumption. -/
theorem mateOpenProperRestriction_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {W V Y : Over (Spec (.of k))}
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (r : W ⟶ Y) (i : V ⟶ Y) [IsOpenImmersion i.left] [QuasiCompact i.left]
    (B : DerivedCategory
      (Mod (Sheaf (ProEt.topology W.left) Ab.{u + 1}) (condensedRingObj Λ W.left))) :
    IsIso (mateOpenProperRestriction Λ
      (IsPullback.of_hasPullback r.left i.left).toCommSq B) := by
  obtain ⟨e, he, _⟩ :=
    (condensed_open_square_scalar_comparison ℓ Λ hΛ r i).2.2.2.2.2.2.2.2.2
  let θ := moduleOpenSquarePullbackComparison Λ r.left i.left
  have he' (M) :
      (openImmersionLowerShriekUpperStarAdjunction Λ
        (pullback.fst r.left i.left)).unit.app
          ((upperStar Λ (pullback.snd r.left i.left)).obj M) ≫
        (upperStar Λ (pullback.fst r.left i.left)).map (e.inv.app M) =
      (upperStar Λ (pullback.snd r.left i.left)).map
        ((openImmersionLowerShriekUpperStarAdjunction Λ i.left).unit.app M) ≫
        θ.hom.app ((openImmersionLowerShriek Λ i.left).obj M) := by
    simpa only [Adjunction.homEquiv_unit, ← square_comparison_eq] using he M
  let θD := Functor.mapDerivedCategorySquareIso θ
  let eD := Functor.mapDerivedCategorySquareIso e.symm
  let av := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i.left
  let ab := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (pullback.fst r.left i.left)
  let ap := (upperStarLowerStarAdjunction Λ r.left).mapDerivedCategoryRightDerivedAdjunction
  let aq := (upperStarLowerStarAdjunction Λ
    (pullback.snd r.left i.left)).mapDerivedCategoryRightDerivedAdjunction
  have hD := Adjunction.mapDerivedCategoryAdjunction_mate
    (openImmersionLowerShriekUpperStarAdjunction Λ i.left)
    (openImmersionLowerShriekUpperStarAdjunction Λ (pullback.fst r.left i.left))
    θ e.symm he'
  have hleft := inverse_mate_eq av ab θD eD hD
  let α : TwoSquare (upperStar Λ (pullback.snd r.left i.left)).mapDerivedCategory
      (openImmersionLowerShriek Λ i.left).mapDerivedCategory
      (openImmersionLowerShriek Λ (pullback.fst r.left i.left)).mapDerivedCategory
      (upperStar Λ r.left).mapDerivedCategory :=
    (mateEquiv av ab).symm (TwoSquare.mk _ _ _ _ θD.hom)
  have hα : IsIso α.natTrans := by
    change IsIso (((mateEquiv av ab).symm (TwoSquare.mk _ _ _ _ θD.hom)).natTrans)
    rw [hleft]
    infer_instance
  have hρ : IsIso ((mateEquiv ap aq (TwoSquare.mk _ _ _ _ θD.hom)).natTrans) := by
    have h := iterated_mateEquiv_conjugateEquiv av ab aq ap α
    have : IsIso (conjugateEquiv (av.comp ap) (aq.comp ab) α.natTrans) :=
      inferInstance
    rw [← h] at this
    simpa only [α, Equiv.apply_symm_apply] using this
  have hn := refinementAdjunction_eq Λ r.left
  have hq := refinementAdjunction_eq Λ (pullback.snd r.left i.left)
  change IsIso (((derivedUpperStarLowerStarAdjunction Λ
    (pullback.snd r.left i.left)).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (pullback.snd r.left i.left))).homEquiv _ _ _)
  rw [hq, hn]
  have hcomp := mate_component ap aq (TwoSquare.mk _ _ _ _ θD.hom) B
  change IsIso (aq.homEquiv _ _
    (θD.hom.app ((lowerStar Λ r.left).rightDerivedFunctor.obj B) ≫
      (upperStar Λ (pullback.fst r.left i.left)).mapDerivedCategory.map
        (ap.counit.app B)))
  rw [← hcomp]
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
