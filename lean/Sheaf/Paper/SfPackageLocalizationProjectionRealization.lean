/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Sheaf.Paper.SfPackageLocalizationBoundaryData
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.CompactSupportProjectionFormula
import Sheaf.Paper.SfPackageLocalizationRationalTransport
import Sheaf.Paper.SfPackageLocalizationBoundaryDescent
import Sheaf.Paper.FiniteTorStability
import Sheaf.Paper.SfOpenClosedTriangleAllStages
import Sheaf.Paper.SfPackageIntegralRecollementSource
import Sheaf.Paper.SfPackageIntegralSupportTowerNormalization

/-! # Localization and projection for the actual compact-support values

Source: current Weil blueprint, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, clauses (3) and (5)
(blueprint: lem-sf-package-localization-projection-realization).

The first two arrows below are composites of the recorded counit/unit and the
specified open, proper and composition comparisons. A boundary is a natural
transformation, so functoriality includes its third square.

## Main statements

* `sfPackageLocalizationProjectionRealization`: localization and canonical projection.
* `sfPackageLocalizationIntegralTower`: coherent tower and connecting-map realization.
* `sfPackageLocalizationCommonStages`: coefficient transport of the three maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.longLine false
set_option linter.tacticAnalysis false
set_option linter.style.multiGoal false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w a b v' w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] sfRationalTriangulationDatum sfIntegralConstructible
  ScalarLocalization.composition



section AdjunctionTransport
variable {C D C' D' : Type v} [Category.{w} C] [Category.{w} D]
  [Category.{w} C'] [Category.{w} D']

private def sfPackageCompositeIso {R : C ⥤ D} {L : D ⥤ C}
    {R' : C' ⥤ D'} {L' : D' ⥤ C'} {c : C ⥤ C'} {d : D ⥤ D'}
    (r : R ⋙ d ≅ c ⋙ R') (l : L ⋙ c ≅ d ⋙ L') :
    (R ⋙ L) ⋙ c ≅ c ⋙ (R' ⋙ L') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ l ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight r _ ≪≫
      Functor.associator _ _ _


private theorem sfPackageAdjunctionCounit
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {adj : L ⊣ R} {adj' : L' ⊣ R'} {c : C ⥤ C'} {d : D ⥤ D'}
    (a : SuppliedExchangeProjection.ExchangeProjectionAdjunctionComparison adj adj' c d)
    (K : D) :
    d.map (adj.counit.app K) =
      (sfPackageCompositeIso a.right a.left).hom.app K ≫ adj'.counit.app (d.obj K) := by
  dsimp only [sfPackageCompositeIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Functor.comp_obj, Category.id_comp, Category.comp_id, Category.assoc]
  rw [a.counit, Iso.hom_inv_id_app_assoc]

private theorem sfPackageAdjunctionUnit
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {adj : L ⊣ R} {adj' : L' ⊣ R'} {c : C ⥤ C'} {d : D ⥤ D'}
    (a : SuppliedExchangeProjection.ExchangeProjectionAdjunctionComparison adj adj' c d)
    (K : C) :
    c.map (adj.unit.app K) ≫ (sfPackageCompositeIso a.left a.right).hom.app K =
      adj'.unit.app (c.obj K) := by
  dsimp only [sfPackageCompositeIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Functor.comp_obj, Category.id_comp, Category.comp_id]
  exact a.unit K

end AdjunctionTransport



section BoundaryTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type v} [Category.{w} C] {M : Type a} [Category.{b} M]
  [HasShift M ℤ] [Preadditive M] [HasZeroObject M]
  [∀ r : ℤ, (shiftFunctor M r).Additive] [Pretriangulated M]

private theorem sfPackageBoundaryTransport (P : SfRecollementPresentation C)
    (R : SfRecollementPresentation M) (I : C ⥤ M)
    (eo : P.openTerm ⋙ I ≅ I ⋙ R.openTerm)
    (ec : P.closedTerm ⋙ I ≅ I ⋙ R.closedTerm)
    (ho : ∀ K, I.map (P.counit.app K) = eo.hom.app K ≫ R.counit.app (I.obj K))
    (hc : ∀ K, I.map (P.unit.app K) ≫ ec.hom.app K = R.unit.app (I.obj K))
    (htri : ∀ K, ∃! d, Triangle.mk (R.counit.app (I.obj K))
      (R.unit.app (I.obj K)) d ∈ distTriang M)
    (hnat : ∀ K L (v : K ⟶ L) d d',
      Triangle.mk (R.counit.app (I.obj K)) (R.unit.app (I.obj K)) d ∈ distTriang M →
      Triangle.mk (R.counit.app (I.obj L)) (R.unit.app (I.obj L)) d' ∈ distTriang M →
      R.closedTerm.map (I.map v) ≫ d' =
        d ≫ (shiftFunctor M (1 : ℤ)).map (R.openTerm.map (I.map v))) :
    ∃ d : P.closedTerm ⋙ I ⟶ (P.openTerm ⋙ I) ⋙ shiftFunctor M (1 : ℤ),
      ∀ K, (Triangle.mk (I.map (P.counit.app K)) (I.map (P.unit.app K))
        (d.app K) ∈ distTriang M) ∧
      ∀ d', Triangle.mk (I.map (P.counit.app K)) (I.map (P.unit.app K))
        d' ∈ distTriang M → d' = d.app K := by
  classical
  let d₀ : I ⋙ R.closedTerm ⟶ (I ⋙ R.openTerm) ⋙ shiftFunctor M (1 : ℤ) :=
    { app := fun K ↦ (htri K).choose
      naturality := fun {K L} v ↦ hnat K L v _ _
        (htri K).choose_spec.1 (htri L).choose_spec.1 }
  let d := ec.hom ≫ d₀ ≫ Functor.whiskerRight eo.inv (shiftFunctor M (1 : ℤ))
  have hd (K : C) : Triangle.mk (I.map (P.counit.app K)) (I.map (P.unit.app K))
      (d.app K) ∈ distTriang M := by
    refine isomorphic_distinguished _ (htri K).choose_spec.1 _
      (Triangle.isoMk _ _ (eo.app K) (Iso.refl _) (ec.app K) ?_ ?_ ?_)
    · simpa using ho K
    · simpa using hc K
    · change (ec.hom.app K ≫ d₀.app K ≫ (shiftFunctor M (1 : ℤ)).map (eo.inv.app K)) ≫
        (shiftFunctor M (1 : ℤ)).map (eo.hom.app K) = ec.hom.app K ≫ d₀.app K
      rw [Category.assoc, Category.assoc, ← Functor.map_comp,
        Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
      simp only [Functor.comp_obj, Category.comp_id]
  refine ⟨d, fun K ↦ ⟨hd K, fun δ hδ ↦ ?_⟩⟩
  let δ' := ec.inv.app K ≫ δ ≫ (shiftFunctor M (1 : ℤ)).map (eo.hom.app K)
  have hδ' : Triangle.mk (R.counit.app (I.obj K)) (R.unit.app (I.obj K))
      δ' ∈ distTriang M := by
    refine isomorphic_distinguished _ hδ _
      (Triangle.isoMk _ _ ((eo.app K).symm) (Iso.refl _) ((ec.app K).symm) ?_ ?_ ?_)
    · change R.counit.app (I.obj K) ≫ 𝟙 _ = eo.inv.app K ≫ I.map (P.counit.app K)
      rw [Category.comp_id, ho, Iso.inv_hom_id_app_assoc]
    · change R.unit.app (I.obj K) ≫ ec.inv.app K = 𝟙 _ ≫ I.map (P.unit.app K)
      rw [← hc, Category.assoc, Iso.hom_inv_id_app]
      simp only [Functor.comp_obj, Category.comp_id, Category.id_comp]
    · change δ' ≫ (shiftFunctor M (1 : ℤ)).map (eo.inv.app K) = ec.inv.app K ≫ δ
      dsimp only [δ']
      rw [Category.assoc, Category.assoc, ← Functor.map_comp,
        Iso.hom_inv_id_app]
      simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id]
  have heq := (htri K).choose_spec.2 δ' hδ'
  calc
    δ = ec.hom.app K ≫ δ' ≫ (shiftFunctor M (1 : ℤ)).map (eo.inv.app K) := by
      dsimp only [δ']
      rw [Category.assoc, Iso.hom_inv_id_app_assoc, Category.assoc, ← Functor.map_comp,
        Iso.hom_inv_id_app]
      simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id]
    _ = d.app K := by rw [heq]; rfl

end BoundaryTransport

section ImageProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
  [∀ X, Category.{w} (B X)] (P : SixFunctorPushStage D B)
  {Z U X Y : SixFunctorSpace D} (i : Z ⟶ X) (j : U ⟶ X) (f : X ⟶ Y)
  [IsProper i.hom.left] (hj : IsOpenImmersion j.hom.left)
  (c : Compactification f.hom.left)
  (cj : Compactification (j ≫ f).hom.left) (ci : Compactification (i ≫ f).hom.left)
  {M : Type a} [Category.{b} M] [HasShift M ℤ]
  [Preadditive M] [HasZeroObject M] [∀ m : ℤ, (shiftFunctor M m).Additive]
  [Pretriangulated M]
  {A : Type a} [Category.{b} A] [HasShift A ℤ]
  [Preadditive A] [HasZeroObject A] [∀ m : ℤ, (shiftFunctor A m).Additive]
  [Pretriangulated A]
  (I : B X ⥤ M) (V : B Y ⥤ A) (F : M ⥤ A) [F.CommShift ℤ] [F.IsTriangulated]

private theorem sfPackageLocalizationImage
    (e : P.support f c ⋙ V ≅ I ⋙ F)
    (d : (P.pull i ⋙ P.direct i) ⋙ I ⟶
      ((P.pull j ⋙ P.openExtension j hj) ⋙ I) ⋙ shiftFunctor M (1 : ℤ))
    (hd : ∀ K, Triangle.mk (I.map ((P.openAdjunction j hj).counit.app K))
      (I.map ((P.pullDirectAdjunction i).unit.app K)) (d.app K) ∈ distTriang M)
    (hu : ∀ K d', Triangle.mk (I.map ((P.openAdjunction j hj).counit.app K))
      (I.map ((P.pullDirectAdjunction i).unit.app K)) d' ∈ distTriang M → d' = d.app K)
    (Q : ObjectProperty (B X)) :
    ∃ δ : SfPackageLocalizationBoundary P i j f cj ci V,
      SfPackageLocalizationRealizes P i j f hj c cj ci V I F inferInstance e δ Q ∧
      ∀ K, Q K → sfPackageLocalizationTriangle P i j f hj c cj ci V δ K ∈ distTriang A := by
  let O := P.pull j ⋙ P.openExtension j hj
  let C := P.pull i ⋙ P.direct i
  let a : (P.pull j ⋙ P.support (j ≫ f) cj) ⋙ V ≅ (O ⋙ I) ⋙ F :=
    Functor.isoWhiskerRight (sfPackageLocalizationOpenComparison P j f hj c cj) V ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft O e ≪≫
        (Functor.associator _ _ _).symm
  let b : (P.pull i ⋙ P.support (i ≫ f) ci) ⋙ V ≅ (C ⋙ I) ⋙ F :=
    Functor.isoWhiskerRight (sfPackageLocalizationClosedComparison P i f c ci) V ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft C e ≪≫
        (Functor.associator _ _ _).symm
  let δ : SfPackageLocalizationBoundary P i j f cj ci V :=
    b.hom ≫ Functor.whiskerRight d F ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (O ⋙ I) (F.commShiftIso (1 : ℤ)).hom ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight a.inv (shiftFunctor A (1 : ℤ))
  refine ⟨δ, ?_, ?_⟩
  · intro K _
    refine ⟨⟨d.app K, hd K⟩, fun d' hd' ↦ ?_⟩
    rw [hu K d' hd']
    dsimp only [δ, a, b, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.comp_id, Category.id_comp, Functor.map_comp, Category.assoc]
    rfl
  · intro K _
    let T := Triangle.mk (I.map ((P.openAdjunction j hj).counit.app K))
      (I.map ((P.pullDirectAdjunction i).unit.app K)) (d.app K)
    refine isomorphic_distinguished _ (F.map_distinguished T (hd K)) _
      (Triangle.isoMk _ _ (a.app K) (e.app K) (b.app K) ?_ ?_ ?_)
    · change V.map ((sfPackageLocalizationFirst P j f hj c cj).app K) ≫
        e.hom.app K = a.hom.app K ≫ F.map (I.map ((P.openAdjunction j hj).counit.app K))
      dsimp only [sfPackageLocalizationFirst, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.leftUnitor_hom_app]
      simp only [Functor.map_comp, Category.assoc]
      dsimp only [a, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app]
      simp only [Functor.comp_obj, O, Category.comp_id, Category.id_comp, Category.assoc]
      erw [V.map_id, Category.id_comp]
      exact congrArg (fun z ↦ V.map
        ((sfPackageLocalizationOpenComparison P j f hj c cj).hom.app K) ≫ z)
          (e.hom.naturality ((P.openAdjunction j hj).counit.app K))
    · change V.map ((sfPackageLocalizationSecond P i f c ci).app K) ≫ b.hom.app K =
        e.hom.app K ≫ F.map (I.map ((P.pullDirectAdjunction i).unit.app K))
      dsimp only [sfPackageLocalizationSecond, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.leftUnitor_inv_app]
      dsimp only [b, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app]
      simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
      have hcancel := (V.mapIso
        ((sfPackageLocalizationClosedComparison P i f c ci).app K)).inv_hom_id
      simp only [Functor.mapIso_inv, Functor.mapIso_hom] at hcancel
      rw [← Category.assoc (V.map ((sfPackageLocalizationClosedComparison
        P i f c ci).inv.app K))]
      erw [hcancel, Category.id_comp]
      simp only [Functor.comp_obj, C]
      exact e.hom.naturality _
    · change δ.app K ≫ (shiftFunctor A (1 : ℤ)).map (a.hom.app K) =
        b.hom.app K ≫ (F.map (d.app K) ≫ (F.commShiftIso (1 : ℤ)).hom.app _)
      dsimp only [δ, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
      simp only [Category.id_comp, Category.assoc]
      rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
      simp only [Functor.comp_obj, O, Category.comp_id]

end ImageProof

private theorem sfPackageLocalization_primeUnit (D : FiniteFieldDatum.{u})
    (C : D.CoefficientDatum) : IsUnit (C.l : D.k) := by
  classical
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let _ : Fact D.p.Prime := ⟨D.prime⟩
  let _ : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  have hunit : IsUnit (C.l : D.k₀) :=
    (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : C.l.Prime) C.different.symm).isUnit
  simpa only [map_natCast] using hunit.map (algebraMap D.k₀ D.k)



section Statements
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
  {n : ℕ} {hn : 1 ≤ n} (S : SixFunctorOperationDatum D C E n hn)
  {Z U X Y : SixFunctorSpace D}
  [sepZ : IsSeparated Z.obj.hom] [sepU : IsSeparated U.obj.hom]
  [sepX : IsSeparated X.obj.hom] [sepY : IsSeparated Y.obj.hom]
  (i : Z ⟶ X) (j : U ⟶ X) (f : X ⟶ Y)
  [closedI : IsClosedImmersion i.hom.left] (hj : IsOpenImmersion j.hom.left)
  [sepF : IsSeparated f.hom.left] [ftF : LocallyOfFiniteType f.hom.left]
  [qcF : QuasiCompact f.hom.left]
  (c : Compactification f.hom.left)
  (cj : Compactification (j ≫ f).hom.left) (ci : Compactification (i ≫ f).hom.left)

include sepZ sepU sepX sepY closedI sepF ftF qcF

omit sepZ sepU sepY sepF ftF qcF in
set_option backward.isDefEq.respectTransparency false in
private theorem sfPackageFiniteSource
    (hij : Set.range j.hom.left.base = (Set.range i.hom.left.base)ᶜ) :
    ∃ d : (S.finite.pull i ⋙ S.finite.direct i) ⋙
        (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ⟶
      ((S.finite.pull j ⋙ S.finite.openExtension j hj) ⋙
        (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι) ⋙
          shiftFunctor _ (1 : ℤ),
      ∀ K : sixFunctorFiniteCategory D C E n hn X,
        (Triangle.mk
          ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.map
            ((S.finite.openAdjunction j hj).counit.app K))
          ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.map
            ((S.finite.pullDirectAdjunction i).unit.app K)) (d.app K) ∈ distTriang _) ∧
        ∀ δ, Triangle.mk
          ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.map
            ((S.finite.openAdjunction j hj).counit.app K))
          ((intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι.map
            ((S.finite.pullDirectAdjunction i).unit.app K)) δ ∈ distTriang _ → δ = d.app K := by
  classical
  let _ : IsOpenImmersion j.hom.left := hj
  let _ : IsSeparated (X.obj.left ↘ Spec (.of D.k)) := sepX
  let A := Padic.coefficientExtensionRing C.l E n
  have : Finite A := Padic.finite_coefficientExtensionRing C.l E n hn
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
  let P := sfFiniteRecollementAt C.l E i.hom.left j.hom.left n hn
  obtain ⟨htri, hnat⟩ := sfOpenClosedTriangle_finite C.l E D.k
    (sfPackageLocalization_primeUnit D C) i.hom.left j.hom.left hij n hn
  obtain ⟨ao, _hao, _hbo⟩ := S.finiteOpenAdjunctionNormalization j hj
  obtain ⟨ac, _hac, _hbc⟩ := S.finiteDirectAdjunctionNormalization i
  let eo : (S.finite.pull j ⋙ S.finite.openExtension j hj) ⋙ I ≅ I ⋙ P.openTerm :=
    sfPackageCompositeIso ao.right ao.left
  let ec : (S.finite.pull i ⋙ S.finite.direct i) ⋙ I ≅ I ⋙ P.closedTerm :=
    sfPackageCompositeIso ac.left ac.right
  have ho (K : sixFunctorFiniteCategory D C E n hn X) :
      I.map ((S.finite.openAdjunction j hj).counit.app K) =
        eo.hom.app K ≫ P.counit.app K.obj :=
    sfPackageAdjunctionCounit ao K
  have hc (K : sixFunctorFiniteCategory D C E n hn X) :
      I.map ((S.finite.pullDirectAdjunction i).unit.app K) ≫ ec.hom.app K =
        P.unit.app K.obj :=
    sfPackageAdjunctionUnit ac K
  let Q : SfRecollementPresentation (sixFunctorFiniteCategory D C E n hn X) :=
    ⟨S.finite.pull j ⋙ S.finite.openExtension j hj, S.finite.pull i ⋙ S.finite.direct i,
      (S.finite.openAdjunction j hj).counit, (S.finite.pullDirectAdjunction i).unit⟩
  exact sfPackageBoundaryTransport Q P I eo ec ho hc
    (fun K ↦ (htri K.obj K.property).2.2.1)
    (fun K L v ↦ hnat K.obj L.obj K.property L.property v.hom)

omit sepZ sepU sepX sepY closedI sepF ftF qcF in
private theorem sfPackageFiniteTorIso (W : SixFunctorSpace D)
    {K L : proEtaleDerivedCategory W.obj.left (Padic.coefficientExtensionRing C.l E n)}
    (e : K ≅ L) (hL : finiteTorConstructible C.l E n hn W.obj.left L) :
    finiteTorConstructible C.l E n hn W.obj.left K := by
  refine ⟨(finiteTorsionConstructible D C.l C.different E n hn W.obj.left).prop_of_iso
    e.symm hL.1, ?_⟩
  obtain ⟨a, b, hab, h⟩ := hL.2
  refine ⟨a, b, hab, ?_⟩
  intro M P hM q hq hP N r hr
  exact h M P (hM.map (fun α ↦ α ≪≫ e)) q hq hP N r hr

omit sepZ sepU sepX sepY closedI sepF ftF qcF in
private theorem sfPackageFinitePullTor {W V : SixFunctorSpace D}
    [IsSeparated W.obj.hom] [IsSeparated V.obj.hom] (g : W ⟶ V)
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (K : sixFunctorFiniteCategory D C E n hn V) (hK : S.finiteTorDomain V K) :
    S.finiteTorDomain W ((S.finite.pull g).obj K) := by
  have : LocallyOfFiniteType W.obj.hom := W.property.1
  have : QuasiCompact W.obj.hom := W.property.2
  have : LocallyOfFiniteType V.obj.hom := V.property.1
  have : QuasiCompact V.obj.hom := V.property.2
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply sfPackageFiniteTorIso W ((S.finitePullback g).app K)
  exact (finiteTor_stability D C.l C.different E m W.obj V.obj g.hom).1 K.obj hK

omit sepZ sepU sepX sepY closedI sepF ftF qcF in
private theorem sfPackageFiniteSupportTor {W V : SixFunctorSpace D}
    [IsSeparated W.obj.hom] [IsSeparated V.obj.hom] (g : W ⟶ V)
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cg : Compactification g.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn W) (hK : S.finiteTorDomain W K) :
    S.finiteTorDomain V ((S.finite.support g cg).obj K) := by
  have : LocallyOfFiniteType W.obj.hom := W.property.1
  have : QuasiCompact W.obj.hom := W.property.2
  have : LocallyOfFiniteType V.obj.hom := V.property.1
  have : QuasiCompact V.obj.hom := V.property.2
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply sfPackageFiniteTorIso V ((S.finiteSupport g cg).app K)
  exact (finiteTor_stability D C.l C.different E m W.obj V.obj g.hom).2.2.2.2 cg K.obj hK

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- At finite coefficients the boundary is exactly the image of the recollement
boundary under the actual compact-support functor, with its canonical shift.
The three actual values retain finite Tor amplitude.
Source: current blueprint prop-functor-package.proof.md, clause (3)
(blueprint: lem-sf-package-localization-projection-realization).
Proof: transport the finite recollement presentation through the two normalized
adjunction comparisons. Uniqueness of its connecting map gives a natural source
boundary. Apply the triangulated intrinsic compact-support composite and conjugate
by the specified outer comparisons. Its realization comparison is S.finiteSupport.
The last arrow is exactly the displayed realization formula for every distinguished
source boundary, by uniqueness. Finite-Tor stability for pullback and compact support,
transported through S.finitePullback and S.finiteSupport, gives all three output
conditions. No nonemptiness condition on either stratum is used. -/
theorem sfPackageLocalizationFiniteImage
    (_hij : Set.range j.hom.left.base = (Set.range i.hom.left.base)ᶜ) :
    ∃ (s : (sixFunctorFiniteSupport D C E n hn f c).CommShift ℤ)
      (δ : SfPackageLocalizationBoundary S.finite i j f cj ci
        (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι),
      SfPackageLocalizationRealizes S.finite i j f hj c cj ci
        (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
        (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
        (sixFunctorFiniteSupport D C E n hn f c) s (S.finiteSupport f c) δ
        (S.finiteTorDomain X) ∧
      ∀ K : sixFunctorFiniteCategory D C E n hn X, S.finiteTorDomain X K →
        sfPackageLocalizationTriangle S.finite i j f hj c cj ci
          (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι δ K ∈ distTriang _ ∧
        S.finiteTorDomain Y ((S.finite.support (j ≫ f) cj).obj ((S.finite.pull j).obj K)) ∧
        S.finiteTorDomain Y ((S.finite.support f c).obj K) ∧
        S.finiteTorDomain Y ((S.finite.support (i ≫ f) ci).obj ((S.finite.pull i).obj K)) := by
  classical
  let _ : IsOpenImmersion j.hom.left := hj
  let _ : IsSeparated (X.obj.left ↘ Spec (.of D.k)) := sepX
  let _ : Finite (Padic.coefficientExtensionRing C.l E n) :=
    Padic.finite_coefficientExtensionRing C.l E n hn
  have hjsep : IsSeparated j.hom.left := inferInstance
  have : QuasiCompact j.hom.left := by
    have : IsNoetherian X.obj.left := sfRecollementNoetherian D.k X.obj.left
    infer_instance
  have : IsSeparated (j ≫ f).hom.left :=
    IsSeparated.stableUnderComposition.comp_mem j.hom.left f.hom.left hjsep sepF
  have : LocallyOfFiniteType (j ≫ f).hom.left := by
    rw [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left]
    infer_instance
  have : QuasiCompact (j ≫ f).hom.left := by
    rw [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left]
    infer_instance
  have : IsSeparated (i ≫ f).hom.left := by
    rw [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left]
    exact IsSeparated.stableUnderComposition.comp_mem i.hom.left f.hom.left
      inferInstance sepF
  have : LocallyOfFiniteType (i ≫ f).hom.left := by
    rw [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left]
    infer_instance
  have : QuasiCompact (i ≫ f).hom.left := by
    rw [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left]
    infer_instance
  let F := sixFunctorFiniteSupport D C E n hn f c
  let _ : F.CommShift ℤ := by
    dsimp [F, sixFunctorFiniteSupport, sfIntrinsicCompactSupport]
    infer_instance
  have : F.IsTriangulated := by
    dsimp [F, sixFunctorFiniteSupport, sfIntrinsicCompactSupport]
    infer_instance
  obtain ⟨d, hd⟩ := sfPackageFiniteSource (S := S) (i := i) (j := j) (hj := hj) _hij
  obtain ⟨δ, hreal, hdist⟩ := sfPackageLocalizationImage S.finite i j f hj c cj ci
    (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι F
    (S.finiteSupport f c) d (fun K ↦ (hd K).1) (fun K ↦ (hd K).2) (S.finiteTorDomain X)
  refine ⟨inferInstance, δ, hreal, fun K hK ↦ ⟨hdist K hK, ?_, ?_, ?_⟩⟩
  · exact sfPackageFiniteSupportTor S (j ≫ f) cj _ (sfPackageFinitePullTor S j K hK)
  · exact sfPackageFiniteSupportTor S f c K hK
  · exact sfPackageFiniteSupportTor S (i ≫ f) ci _ (sfPackageFinitePullTor S i K hK)

set_option linter.unusedSectionVars false in
/-- A single strict tower realizes the entire integral localization triangle. Its
transition maps are fixed by CompactSupportReductionTowerConstruction, including
every quotient m to n. The comparison is one natural isomorphism of functors;
its map equation and the boundary formula rule out independent choices of cones.
Source: current blueprint prop-functor-package.proof.md, clause (3)
(blueprint: lem-sf-package-localization-projection-realization).
Proof: steps 1--4 of sfPackageLocalizationProjectionRealization. Apply the strict
reduction-tower functor to the whole recollement triangle, use its triangulated
structure and total right-derived inverse limit, and transport by the normalized
comparison with actual integral support. The reduction-boundary theorem identifies
all three finite maps. The tower datum retains all quotient transitions. Naturality
of the comparison gives the map equation, and the composite shift gives the
connecting-arrow equation. The inclusion is full and exact, so the resulting
triangle has the asserted bounded constructible vertices. -/
theorem sfPackageLocalizationIntegralTower
    (_hij : Set.range j.hom.left.base = (Set.range i.hom.left.base)ᶜ)
    (hl : IsUnit (C.l : D.k)) :
    ∃ δI : SfPackageLocalizationBoundary S.higher.integral i j f cj ci
        (𝟭 (sfIntegralConstructibleCategory C.l E Y.obj.left)),
      SfPackageLocalizationTowerBoundary i j f hj c cj ci S.higher hl δI := by
  classical
  let := integralOperationsDerivedCountableProducts C.l E Y.obj.left
  obtain ⟨T, hT, sT, sL, hexT, hexL, e, hp⟩ :=
    sfPackageIntegralSupportTowerNormalization S f hl c
  let : T.tower.CommShift ℤ := sT
  let : T.limit.CommShift ℤ := sL
  have : T.tower.IsTriangulated := hexT
  have : T.limit.IsTriangulated := hexL
  let sF : (T.tower ⋙ T.limit).CommShift ℤ := inferInstance
  let I := (sfIntegralConstructible C.l E X.obj.left).ι
  let V := (sfIntegralConstructible C.l E Y.obj.left).ι
  obtain ⟨d, hd⟩ := sfPackageIntegralRecollementSource S i j hj _hij
  obtain ⟨δ, hreal, hdist⟩ := sfPackageLocalizationImage S.higher.integral i j f hj c cj ci
    I V (T.tower ⋙ T.limit) e d (fun K ↦ (hd K).1) (fun K ↦ (hd K).2)
      (fun _ ↦ True)
  let O := S.higher.integral.pull j ⋙ S.higher.integral.support (j ≫ f) cj
  let B := S.higher.integral.pull i ⋙ S.higher.integral.support (i ≫ f) ci
  let δ' : B ⋙ V ⟶ (O ⋙ shiftFunctor _ (1 : ℤ)) ⋙ V :=
    δ ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft O (V.commShiftIso (1 : ℤ)).inv ≫
      (Functor.associator _ _ _).inv
  let δI : SfPackageLocalizationBoundary S.higher.integral i j f cj ci (𝟭 _) :=
    ((Functor.whiskeringRight _ _ _).obj V).preimage δ'
  have hδ (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
      δ.app K = V.map (δI.app K) ≫ (V.commShiftIso (1 : ℤ)).hom.app (O.obj K) := by
    have h := congrArg (fun t ↦ t.app K)
      (((Functor.whiskeringRight _ _ _).obj V).map_preimage δ')
    change V.map (δI.app K) = δ'.app K at h
    dsimp only [δ', NatTrans.comp_app, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app] at h
    simp only [Category.id_comp, Category.comp_id] at h
    rw [h, Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id (δ.app K)).symm
  refine ⟨δI, T, hT, sT, sL, hexT, hexL, sF, e, δ, hp, hδ, hreal,
    (fun K ↦ hdist K trivial), ?_, ?_⟩
  · intro K L v
    exact e.hom.naturality v
  · intro K
    exact Functor.commShiftIso_comp_hom_app T.tower T.limit (1 : ℤ) K

section CommonStagesProof

attribute [local irreducible] SfPackageLocalizationBoundary
  SfPackageLocalizationCoefficientBoundary SfPackageLocalizationTowerBoundary
  SfPackageLocalizationRationalBoundary SfPackageLocalizationFieldSystem

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Exact common-stage embeddings carry all three arrows, including the boundary,
with precisely their supplied coefficient comparisons. Every finite field stage
is allowed; no fixed representative for all objects or maps is assumed.
Source: current blueprint prop-functor-package.proof.md, clause (3)
(blueprint: lem-sf-package-localization-projection-realization).
Proof: step 5 of the main theorem. Apply rationalization at each finite field,
then exact scalar extension, with the operation reduction equations. Descend the
natural arrows and their equations by prop-weil-pbc-descent-functors. Every finite
diagram has a common finite field stage, where the distinguished triangle and its
boundary square hold; exact inclusion gives them in the common-stage category.
The comparison cocycle makes the result independent of field enlargement. One δE
family is used simultaneously for common-stage inclusions and scalar transitions. -/
theorem sfPackageLocalizationCommonStages
    (_hij : Set.range j.hom.left.base = (Set.range i.hom.left.base)ᶜ)
    (hl : IsUnit (C.l : D.k)) :
    ∃ (δR : SfPackageLocalizationBoundary S.higher.rational i j f cj ci
        (𝟭 (sfRationalConstructibleCategory C.l E Y.obj.left)))
      (δE : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
        SfPackageLocalizationBoundary
          (sixFunctorCoefficientRational D C S.closure.coefficientStages E₀) i j f cj ci
          (𝟭 (GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Y.obj.left E₀)))
      (δbar : SfPackageLocalizationBoundary S.closure.commonStage i j f cj ci
        (𝟭 (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left))),
      SfPackageLocalizationFieldSystem i j f hj c cj ci S hl δR δE δbar := by
  classical
  obtain ⟨δI, hI⟩ := sfPackageLocalizationIntegralTower (D := D) (C := C) (E := E)
      S i j f hj c cj ci _hij hl
  obtain ⟨δR, hIR, hR⟩ :=
    sfPackageLocalizationRationalTransport (D := D) (C := C) (E := E)
      i j f hj c cj ci S.higher hl δI hI
  have hbase : SfPackageLocalizationRationalBoundary i j f hj c cj ci S.higher hl δR := by
    unfold SfPackageLocalizationRationalBoundary
    exact ⟨δI, hI, hIR, hR⟩
  have hfinite (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar) :
      ∃ δ : SfPackageLocalizationBoundary
          (sixFunctorCoefficientRational D C S.closure.coefficientStages E₀) i j f cj ci
          (𝟭 (GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Y.obj.left E₀)),
        SfPackageLocalizationRationalBoundary i j f hj c cj ci
          (S.closure.coefficientStages E₀) hl δ := by
    let N := S.coefficientIntegralNormalization E₀
    let S₀ : SixFunctorOperationDatum D C
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) 1 (by decide) :=
      { toSixFunctorFiniteOperations := N.finiteLevels 0
        higher := S.closure.coefficientStages E₀
        integralNormalization := N
        closure := S.closure
        coefficientIntegralNormalization := S.coefficientIntegralNormalization
        commonStageCoherence := S.commonStageCoherence }
    have hIntegral :
        ∃ δI₀ : SfPackageLocalizationBoundary (S.closure.coefficientStages E₀).integral
            i j f cj ci (𝟭 (sfIntegralConstructibleCategory C.l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) Y.obj.left)),
          SfPackageLocalizationTowerBoundary i j f hj c cj ci
            (S.closure.coefficientStages E₀) hl δI₀ :=
      sfPackageLocalizationIntegralTower (D := D) (C := C)
        (E := AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀)
        S₀ i j f hj c cj ci _hij hl
    obtain ⟨δI₀, hI₀⟩ := hIntegral
    obtain ⟨δ, hcoeff, hdist⟩ := sfPackageLocalizationRationalTransport (D := D) (C := C)
      (E := AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀)
      i j f hj c cj ci (S.closure.coefficientStages E₀) hl δI₀ hI₀
    refine ⟨δ, ?_⟩
    unfold SfPackageLocalizationRationalBoundary
    exact ⟨δI₀, hI₀, hcoeff, hdist⟩
  choose δE hE using hfinite
  obtain ⟨δbar, hbar, hincl, htrans⟩ :=
    sfPackageLocalizationBoundaryDescent (D := D) (C := C) (E := E)
      i j f hj c cj ci S _hij hl δE hE
  refine ⟨δR, δE, δbar, ?_⟩
  unfold SfPackageLocalizationFieldSystem
  exact ⟨hbase, hE, hbar, hincl, htrans⟩

end CommonStagesProof

/-- Localization on the actual compact-support values at all four coefficient stages,
and the canonical projection formula with its naturality, compactification, composition
and proper-coincidence equations. The refinements below pin every coefficient boundary
to one coherent tower system. Finite coefficients use the finite-Tor input domain;
integral and field coefficients use the recorded bounded constructible categories.
Source: current blueprint prop-functor-package.proof.md, clauses (3) and (5)
(blueprint: lem-sf-package-localization-projection-realization).

Proof:
1. Use prop-sf-open-closed-triangle-all-stages for the specified counit/unit triangle.
2. Apply lem-compact-support-direct-image-triangulated at each finite level;
   thm-sf-ctf-stability retains the finite-Tor domain and its three vertices.
3. Integrally, lem-sf-recollement-reduction-boundary includes the connecting map.
   Apply lem-weil-compact-support-reduction-tower-functor to the entire triangle.
   lem-sf-compact-support-total-limit-realization gives its maps and shift comparison;
   lem-sf-integral-compact-support-constructible and
   lem-weil-integral-constructible-triangulated retain the integral domain.
4. lem-sf-package-compactified-tower-comparisons identifies the outer vertices by
   composition, open identification and proper coincidence. Conjugate the whole
   image triangle by these specified comparisons, giving precisely First and Second.
5. prop-weil-pbc-rational-transport and lem-weil-scalar-extension-exact-triangulated
   carry all three arrows to fields; lem-fix-operation-reduction identifies the maps.
   def-weil-algebraically-closed-coefficients and prop-weil-pbc-descent-functors
   descend them over arbitrary common finite stages.
6. None of these steps requires a nonempty stratum. For descended inputs,
   lem-fix-weil-operations and the Weil recollement theorem retain all three squares.
7. fix-prop-projection-formula gives the specified canonical projection and all its
   compatibilities. def-weil-derived-pullback-tensor-hom fixes completed operations.
-/
theorem sfPackageLocalizationProjectionRealization
    (_hij : Set.range j.hom.left.base = (Set.range i.hom.left.base)ᶜ) :
    SfPackageLocalizationConclusion S.finite i j f hj c cj ci
      (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
      (S.finiteTorDomain X) ∧
    SfPackageLocalizationConclusion S.higher.integral i j f hj c cj ci
      (sfIntegralConstructible C.l E Y.obj.left).ι (fun _ ↦ True) ∧
    SfPackageLocalizationConclusion S.higher.rational i j f hj c cj ci
      (𝟭 (sfRationalConstructibleCategory C.l E Y.obj.left)) (fun _ ↦ True) ∧
    SfPackageLocalizationConclusion S.closure.commonStage i j f hj c cj ci
      (𝟭 (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left))
      (fun _ ↦ True) ∧
    CompactSupportFiniteProjection.Laws S.toSixFunctorFiniteOperations ∧
    CompactSupportProjectionLaws S.higher.integral S.higher.integralTensor
      S.higher.integralExchange S.integralFiniteTorDomain ∧
    CompactSupportProjectionLaws S.higher.rational S.higher.rationalTensor
      S.higher.rationalExchange (fun _ _ ↦ True) ∧
    CompactSupportProjectionLaws S.closure.commonStage S.closure.commonStageTensor
      S.closure.commonStageExchange (fun _ _ ↦ True) := by
  obtain ⟨s, δF, hrealF, hF⟩ :=
    sfPackageLocalizationFiniteImage S i j f hj c cj ci _hij
  have hl : IsUnit (C.l : D.k) := sfPackageLocalization_primeUnit D C
  obtain ⟨δI, hI⟩ := sfPackageLocalizationIntegralTower S i j f hj c cj ci _hij hl
  obtain ⟨δR, δE, δbar, hR, hE, hbar, hincl, htrans⟩ :=
    sfPackageLocalizationCommonStages S i j f hj c cj ci _hij hl
  obtain ⟨T, hT, sT, sL, hexT, hexL, sF, e, δ, hp, hδ, hreal, hdist, hmap, hs⟩ := hI
  obtain ⟨δI', hI', hcoeff, hdistR⟩ := hR
  obtain ⟨hpf, hpi, hpr, hpb, hlevels, hstages⟩ := compactSupportProjectionFormula S
  exact ⟨⟨δF, fun K hK ↦ (hF K hK).1⟩,
    ⟨δ, fun K _ ↦ hdist K⟩,
    ⟨δR, fun K _ ↦ hdistR K⟩,
    ⟨δbar, fun K _ ↦ hbar K⟩, hpf, hpi, hpr, hpb⟩



end Statements

end WeilConjectures
