/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement

/-! Mate transport for the finite restriction square.
(blueprint: new-lem-sf-finite-base-change-restriction-mate-transport)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

private theorem mate_eq_of_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') {E : C ⥤ C'} {F : D ⥤ D'}
    (s : E ⋙ L' ⟶ L ⋙ F) (r : R ⋙ E ⟶ F ⋙ R')
    (h : ∀ K, E.map (a.unit.app K) ≫ r.app (L.obj K) =
      b.unit.app (E.obj K) ≫ R'.map (s.app K)) :
    (mateEquiv a b s).natTrans = r := by
  have hs : s = ((mateEquiv a b).symm r).natTrans := by
    ext K
    apply (b.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit]
    exact (h K).symm.trans (unit_mateEquiv_symm a b r K)
  rw [hs]
  exact congrArg TwoSquare.natTrans ((mateEquiv a b).apply_symm_apply r)

private theorem inverse_mate_eq_of_homEquiv
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') {E : C ⥤ C'} {F : D ⥤ D'}
    (s : E ⋙ L' ⟶ L ⋙ F) (r : R ⋙ E ⟶ F ⋙ R')
    (h : ∀ K, b.homEquiv _ _ (s.app K) =
      E.map (a.unit.app K) ≫ r.app (L.obj K)) :
    ((mateEquiv a b).symm r).natTrans = s := by
  ext K
  apply (b.homEquiv _ _).injective
  rw [h, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm a b r K).symm

private theorem transport_from_unit
    {A Ab B Bb C Cb D Db : Type*}
    [Category A] [Category Ab] [Category B] [Category Bb]
    [Category C] [Category Cb] [Category D] [Category Db]
    (EA : A ≌ Ab) (EB : B ≌ Bb) (EC : C ≌ Cb) (ED : D ≌ Db)
    {J : A ⥤ B} {U : B ⥤ A} {J' : C ⥤ D} {U' : D ⥤ C}
    {Jb : Ab ⥤ Bb} {Ub : Bb ⥤ Ab} {Jb' : Cb ⥤ Db} {Ub' : Db ⥤ Cb}
    (adj : J ⊣ U) (adj' : J' ⊣ U') (adjb : Jb ⊣ Ub) (adjb' : Jb' ⊣ Ub')
    (r : U ⋙ EA.functor ≅ EB.functor ⋙ Ub)
    (r' : U' ⋙ EC.functor ≅ ED.functor ⋙ Ub')
    (j : J ⋙ EB.functor ≅ EA.functor ⋙ Jb)
    (j' : J' ⋙ ED.functor ≅ EC.functor ⋙ Jb')
    (hj : ∀ X, EA.functor.map (adj.unit.app X) ≫ r.hom.app (J.obj X) =
      adjb.unit.app (EA.functor.obj X) ≫ Ub.map (j.inv.app X))
    (hj' : ∀ X, EC.functor.map (adj'.unit.app X) ≫ r'.hom.app (J'.obj X) =
      adjb'.unit.app (EC.functor.obj X) ≫ Ub'.map (j'.inv.app X))
    (P : A ⥤ C) (Q : B ⥤ D) (Pb : Ab ⥤ Cb) (Qb : Bb ⥤ Db)
    (p : P ⋙ EC.functor ≅ EA.functor ⋙ Pb)
    (q : Q ⋙ ED.functor ≅ EB.functor ⋙ Qb)
    (β : P ⋙ J' ⟶ J ⋙ Q) (γ : Pb ⋙ Jb' ⟶ Jb ⋙ Qb)
    (bb : Ub ⋙ Pb ⟶ Qb ⋙ Ub')
    (hγ : ∀ X, adjb'.homEquiv _ _ (γ.app X) =
      Pb.map (adjb.unit.app X) ≫ bb.app (Jb.obj X))
    (hb : ∀ Y,
      p.hom.app (U.obj Y) ≫ Pb.map (r.hom.app Y) ≫ bb.app (EB.functor.obj Y) =
        EC.functor.map ((mateEquiv adj adj' β).natTrans.app Y) ≫
          r'.hom.app (Q.obj Y) ≫ Ub'.map (q.hom.app Y)) (X : A) :
    j'.hom.app (P.obj X) ≫ Jb'.map (p.hom.app X) ≫ γ.app (EA.functor.obj X) =
      ED.functor.map (β.app X) ≫ q.hom.app (J.obj X) ≫ Qb.map (j.hom.app X) := by
  have h := (equivalenceAdjunctionComparison_inverseMate EA EB EC ED
    adj adj' adjb adjb' r r' j j'
    (mate_eq_of_unit adj adjb j.inv r.hom hj)
    (mate_eq_of_unit adj' adjb' j'.inv r'.hom hj') P Q Pb Qb p q
    (mateEquiv adj adj' β).natTrans bb hb).1 X
  have hβ : ((mateEquiv adj adj').symm
      (mateEquiv adj adj' β)).natTrans = β :=
    congrArg TwoSquare.natTrans ((mateEquiv adj adj').symm_apply_apply β)
  have hγ' := inverse_mate_eq_of_homEquiv adjb adjb' γ bb hγ
  change ED.functor.map (((mateEquiv adj adj').symm
      (mateEquiv adj adj' β)).natTrans.app X) ≫ _ =
    _ ≫ _ ≫ (((mateEquiv adjb adjb').symm bb).natTrans.app _) at h
  rw [hβ, hγ'] at h
  exact h.symm

set_option maxHeartbeats 4000000 in
-- The concrete finite specialization elaborates through four equivalence records.
/-- Transport the right-adjoint square through the four finite comparison pins.
Source: third step of `lem-sf-finite-base-change-restriction-ordinary-pin-mate`.
Proof: apply the four finite pull-pin mate equations and
`equivalenceAdjunctionComparison_inverseMate` to transport the supplied
right-square identity. Rewrite the inverse mates as `upperStarCompIso.hom` and
`ordinaryTheta.inv`, then cancel the comparison isomorphisms. This is strictly
smaller than the parent because its right-square identity is supplied as a
hypothesis. The categorical normalization and cancellation are an independent
obstacle estimated at more than four hours from the currently published
interfaces.
(blueprint: new-lem-sf-finite-base-change-restriction-mate-transport)
-/
theorem finite_base_change_restriction_mate_transport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o) (N : FiniteModules A X)
    (h : ∀ M : FiniteModules A X',
      e.open_pin.star.hom.app ((ProEtale.lowerStar (ModuleCat.{u + 1} A) g).obj M) ≫
        (restrict .ordinary j (finiteInput A gU j' j g sq).R).map
          (e.pull_pin.right.hom.app M) ≫
        o.rightSquare.hom.app (e.realizeX'.equivalence.functor.obj M) =
      e.realizeU.equivalence.functor.map
          ((mateEquiv
            (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
            (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) gU)
            (ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w).hom).natTrans.app M) ≫
        e.pullU_pin.right.hom.app
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) j').obj M) ≫
        (direct .ordinary gU _ _ (cornerCoefficient t)).map
          (e.open'_pin.star.hom.app M)) :
    e.pullU_pin.ordinary.hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N) ≫
      o.gUPull.ordinary.map (e.open_pin.star.hom.app N) ≫
      o.ordinaryTheta.inv.app (e.realizeX.equivalence.functor.obj N) =
    e.realizeU'.equivalence.functor.map
        ((ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w).hom.app N) ≫
      e.open'_pin.star.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj N) ≫
      (restrict .ordinary j' (finiteInput A gU j' j g sq).S).map
        (e.pull_pin.ordinary.hom.app N) := by
  exact transport_from_unit
    (A := FiniteModules A X) (B := FiniteModules A X')
    (C := FiniteModules A U) (D := FiniteModules A U')
    (Ab := Mod ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of A)))
    (Bb := Mod ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj
      (CommRingCat.of A)))
    (Cb := Mod (restrictRing .ordinary j
      ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A))))
    (Db := Mod (restrictRing .ordinary j'
      ((constantSheaf (ProEt.topology X') CommRingCat.{u + 1}).obj (CommRingCat.of A))))
    (EA := e.realizeX.equivalence)
    (EB := e.realizeX'.equivalence)
    (EC := e.realizeU.equivalence)
    (ED := e.realizeU'.equivalence)
    (adj := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
    (adj' := ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) gU)
    (adjb := o.gPull.adjunction)
    (adjb' := o.gUPull.adjunction)
    (r := e.pull_pin.right)
    (r' := e.pullU_pin.right)
    (j := e.pull_pin.ordinary)
    (j' := e.pullU_pin.ordinary)
    (hj := e.pull_pin.mate)
    (hj' := e.pullU_pin.mate)
    (P := ProEtale.upperStar (ModuleCat.{u + 1} A) j)
    (Q := ProEtale.upperStar (ModuleCat.{u + 1} A) j')
    (Pb := restrict .ordinary j (finiteInput A gU j' j g sq).R)
    (Qb := restrict .ordinary j' (finiteInput A gU j' j g sq).S)
    (p := e.open_pin.star)
    (q := e.open'_pin.star)
    (β := (ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w).hom)
    (γ := o.ordinaryTheta.inv)
    (bb := o.rightSquare.hom)
    (hγ := o.ordinaryTheta_mate)
    (hb := h)
    N

end SheafOfModules.OpenTensorNormalization
