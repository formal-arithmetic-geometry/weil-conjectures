/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QbarCurveOrdinaryImage
public import WeilConjectures.AlgebraicGeometry.CommonStageFourierTransform
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.AlgebraicGeometry.IsomorphismFieldTransport
import WeilConjectures.AlgebraicGeometry.FourierTrivialCharacterUnit
import WeilConjectures.AlgebraicGeometry.CommonStageShiftedUnitTensor
import WeilConjectures.AlgebraicGeometry.FieldWeilShriekShiftData

/-! # Ordinary middle extension of common-stage Weil sheaves

Source: main-20261015, def-wf-middle-extension, ordinary direct-image and shift paragraphs
(blueprint: def-wf-middle-extension).

The Weil direct image is determined by the ordinary sheaf adjunction. The shift is
implemented by tensoring with the explicit arithmetic constant coefficient line [1].
That line is the trivial-character Artin--Schreier projector, not a chosen Weil map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (c : Scheme.MiddleExtensionCurve D)

private theorem curveHeartFrobenius_equiv (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (zlHeartFrobenius D l hl Ω X₀).IsEquivalence := by
  let : (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber X₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let g := (D.geometricFrobenius X₀).hom
  let I := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := I
  obtain ⟨iX, iY, hc⟩ := isomorphismFieldTransport D l hl Ω g
  have hiX : iX = I := Subsingleton.elim _ _
  have hiY : iY = I := Subsingleton.elim _ _
  subst iX
  subst iY
  obtain ⟨hX, hY, _, _, S, R, _, ⟨c⟩, ⟨d⟩⟩ := hc
  let F := sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω
  let : F.IsEquivalence := c.equivalence
  have hcH := (constructible_pullback_t_exact D l hl Ω (Classical.arbitrary _)
    (W := (D.geometricFiber X₀).left) (X := (D.geometricFiber X₀).left) (inv g)).2
  dsimp only [ConstructibleCommonStagePullbackComparison] at hcH
  have hI : constructiblePullbackResidueUnits D l hl (D.geometricFiber X₀).left = I :=
    Subsingleton.elim _ _
  rw [hI] at hcH
  obtain ⟨H⟩ := hcH
  let P := sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
  let e : commonStageDerivedPullback l Ω (inv g) ⋙ F ≅ 𝟭 _ := by
    have de := d.epsilon
    change commonStageDerivedPullback l Ω (inv g) ⋙
      commonStageDerivedPullback l Ω (inv (inv g)) ≅ 𝟭 _ at de
    rw [CategoryTheory.IsIso.inv_inv] at de
    exact de
  let : (zlHeartFrobenius D l hl Ω X₀).Full := by
    change (P.lift (P.ι ⋙ F) _).Full
    infer_instance
  let : (zlHeartFrobenius D l hl Ω X₀).Faithful := by
    change (P.lift (P.ι ⋙ F) _).Faithful
    infer_instance
  let : (zlHeartFrobenius D l hl Ω X₀).EssSurj := ⟨fun K ↦ by
    refine ⟨H.heart.obj K, ⟨P.isoMk ?_⟩⟩
    exact F.mapIso ((eqToIso H.heart_fac).app K) ≪≫ e.app K.obj⟩
  exact {}


private def heartPairs {C : Type*} [Category C] (F : C ⥤ C) (P : ObjectProperty C)
    (h : ∀ K : P.FullSubcategory, P (F.obj K.obj)) :
    (P.inverseImage (IsoAlgebra.forget F)).FullSubcategory ⥤ IsoAlgebra (P.lift (P.ι ⋙ F) h) where
  obj K := IsoAlgebra.mk ⟨K.obj.carrier, K.property⟩
    { hom := ObjectProperty.homMk K.obj.str.hom
      inv := ObjectProperty.homMk K.obj.str.inv
      hom_inv_id := ObjectProperty.hom_ext _ K.obj.str.hom_inv_id
      inv_hom_id := ObjectProperty.hom_ext _ K.obj.str.inv_hom_id }
  map a := ObjectProperty.homMk
    { f := ObjectProperty.homMk a.hom.hom.f
      h := ObjectProperty.hom_ext _ a.hom.hom.h }
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply Algebra.Hom.ext
    apply ObjectProperty.hom_ext
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply Algebra.Hom.ext
    apply ObjectProperty.hom_ext
    rfl

private def heartPairsFullyFaithful {C : Type*} [Category C] (F : C ⥤ C)
    (P : ObjectProperty C) (h : ∀ K : P.FullSubcategory, P (F.obj K.obj)) :
    (heartPairs F P h).FullyFaithful where
  preimage g := ObjectProperty.homMk (ObjectProperty.homMk
    { f := g.hom.f.hom
      h := congrArg (fun f ↦ f.hom) g.hom.h })
  map_preimage _ := by
    apply ObjectProperty.hom_ext
    apply Algebra.Hom.ext
    apply ObjectProperty.hom_ext
    rfl
  preimage_map _ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Algebra.Hom.ext
    rfl

private def heartPairsInverse {C : Type*} [Category C] (F : C ⥤ C)
    (P : ObjectProperty C) (h : ∀ K : P.FullSubcategory, P (F.obj K.obj)) :
    IsoAlgebra (P.lift (P.ι ⋙ F) h) ⥤ (P.inverseImage (IsoAlgebra.forget F)).FullSubcategory where
  obj K := ⟨IsoAlgebra.mk K.carrier.obj
    { hom := K.str.hom.hom
      inv := K.str.inv.hom
      hom_inv_id := congrArg (fun f ↦ f.hom) K.str.hom_inv_id
      inv_hom_id := congrArg (fun f ↦ f.hom) K.str.inv_hom_id }, K.carrier.property⟩
  map a := ObjectProperty.homMk (ObjectProperty.homMk
    { f := a.hom.f.hom
      h := congrArg (fun f ↦ f.hom) a.hom.h })
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Algebra.Hom.ext
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Algebra.Hom.ext
    rfl

private def heartSquare {C E : Type*} [Category C] [Category E]
    (F : C ⥤ C) (G : E ⥤ E) (L : C ⥤ E)
    (P : ObjectProperty C) (Q : ObjectProperty E)
    (hF : ∀ K : P.FullSubcategory, P (F.obj K.obj))
    (hG : ∀ K : Q.FullSubcategory, Q (G.obj K.obj))
    (hL : ∀ K : P.FullSubcategory, Q (L.obj K.obj)) (e : L ⋙ G ≅ F ⋙ L) :
    Q.lift (P.ι ⋙ L) hL ⋙ Q.lift (Q.ι ⋙ G) hG ≅
      P.lift (P.ι ⋙ F) hF ⋙ Q.lift (P.ι ⋙ L) hL :=
  NatIso.ofComponents (fun K ↦ Q.isoMk (e.app K.obj))
    (fun f ↦ ObjectProperty.hom_ext _ (e.hom.naturality f.hom))

private def heartPairsPullComparison {C E : Type*} [Category C] [Category E]
    (F : C ⥤ C) (G : E ⥤ E) (L : C ⥤ E)
    (P : ObjectProperty C) (Q : ObjectProperty E)
    (hF : ∀ K : P.FullSubcategory, P (F.obj K.obj))
    (hG : ∀ K : Q.FullSubcategory, Q (G.obj K.obj))
    (hL : ∀ K : P.FullSubcategory, Q (L.obj K.obj)) (e : L ⋙ G ≅ F ⋙ L) :
    heartPairs F P hF ⋙ IsoAlgebra.mapOfNatIso (heartSquare F G L P Q hF hG hL e) ≅
      (Q.inverseImage (IsoAlgebra.forget G)).lift
        ((P.inverseImage (IsoAlgebra.forget F)).ι ⋙ IsoAlgebra.mapOfNatIso e)
        (fun K ↦ hL ⟨K.obj.carrier, K.property⟩) ⋙ heartPairs G Q hG :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    (Algebra.isoMk (Iso.refl _) (by
      apply ObjectProperty.hom_ext
      change G.map (𝟙 _) ≫ (e.hom.app K.obj.carrier ≫ L.map K.obj.str.hom) =
        (e.hom.app K.obj.carrier ≫ L.map K.obj.str.hom) ≫ 𝟙 _
      rw [G.map_id, Category.id_comp, Category.comp_id])))
    (fun f ↦ by
      apply ObjectProperty.hom_ext
      apply Algebra.Hom.ext
      apply ObjectProperty.hom_ext
      change L.map f.hom.hom.f ≫ 𝟙 _ = 𝟙 _ ≫ L.map f.hom.hom.f
      simp only [Category.id_comp, Category.comp_id])

private def heartPairsInverseComparison {C : Type*} [Category C] (F : C ⥤ C)
    (P : ObjectProperty C) (h : ∀ K : P.FullSubcategory, P (F.obj K.obj)) :
    heartPairsInverse F P h ⋙ heartPairs F P h ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    (Algebra.isoMk (P.isoMk (Iso.refl _)) (by
      apply ObjectProperty.hom_ext
      change F.map (𝟙 _) ≫ K.str.hom.hom = K.str.hom.hom ≫ 𝟙 _
      rw [F.map_id, Category.id_comp, Category.comp_id])))
    (fun f ↦ by
      apply ObjectProperty.hom_ext
      apply Algebra.Hom.ext
      apply ObjectProperty.hom_ext
      change f.hom.f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.f.hom
      simp only [Category.id_comp, Category.comp_id])

private def pairHeartForget {C : Type*} [Category C] (F : C ⥤ C)
    (P : ObjectProperty C) :
    (P.inverseImage (IsoAlgebra.forget F)).FullSubcategory ⥤ P.FullSubcategory where
  obj K := ⟨K.obj.carrier, K.property⟩
  map f := ObjectProperty.homMk f.hom.hom.f

private def pairHeartRight {C E : Type*} [Category C] [Category E]
    (F : C ⥤ C) (G : E ⥤ E) (L : C ⥤ E)
    (P : ObjectProperty C) (Q : ObjectProperty E)
    (hF : ∀ K : P.FullSubcategory, P (F.obj K.obj))
    (hG : ∀ K : Q.FullSubcategory, Q (G.obj K.obj))
    (hL : ∀ K : P.FullSubcategory, Q (L.obj K.obj)) (e : L ⋙ G ≅ F ⋙ L)
    (R : Q.FullSubcategory ⥤ P.FullSubcategory) (a : Q.lift (P.ι ⋙ L) hL ⊣ R)
    [(P.lift (P.ι ⋙ F) hF).IsEquivalence]
    [(Q.lift (Q.ι ⋙ G) hG).IsEquivalence] :=
  heartPairs G Q hG ⋙
    IsoAlgebra.mapOfNatIso (IsoAlgebra.mateIso a (heartSquare F G L P Q hF hG hL e)) ⋙
    heartPairsInverse F P hF

private def pairHeartAdjunction {C E : Type*} [Category C] [Category E]
    (F : C ⥤ C) (G : E ⥤ E) (L : C ⥤ E)
    (P : ObjectProperty C) (Q : ObjectProperty E)
    (hF : ∀ K : P.FullSubcategory, P (F.obj K.obj))
    (hG : ∀ K : Q.FullSubcategory, Q (G.obj K.obj))
    (hL : ∀ K : P.FullSubcategory, Q (L.obj K.obj)) (e : L ⋙ G ≅ F ⋙ L)
    (R : Q.FullSubcategory ⥤ P.FullSubcategory) (a : Q.lift (P.ι ⋙ L) hL ⊣ R)
    [(P.lift (P.ι ⋙ F) hF).IsEquivalence]
    [(Q.lift (Q.ι ⋙ G) hG).IsEquivalence] :
    (Q.inverseImage (IsoAlgebra.forget G)).lift
        ((P.inverseImage (IsoAlgebra.forget F)).ι ⋙ IsoAlgebra.mapOfNatIso e)
        (fun K ↦ hL ⟨K.obj.carrier, K.property⟩) ⊣
      pairHeartRight F G L P Q hF hG hL e R a := by
  let eH := heartSquare F G L P Q hF hG hL e
  let m := IsoAlgebra.mateIso a eH
  let J := IsoAlgebra.mapOfNatIso m
  let b := IsoAlgebra.mapOfNatIsoAdjunction a eH m rfl
  refine b.restrictFullyFaithful (heartPairsFullyFaithful F P hF)
    (heartPairsFullyFaithful G Q hG) (heartPairsPullComparison F G L P Q hF hG hL e) ?_
  exact Functor.isoWhiskerLeft (heartPairs G Q hG ⋙ J)
      (heartPairsInverseComparison F P hF).symm ≪≫
    (Functor.associator _ _ _).symm

private def pairHeartRightForget {C E : Type*} [Category C] [Category E]
    (F : C ⥤ C) (G : E ⥤ E) (L : C ⥤ E)
    (P : ObjectProperty C) (Q : ObjectProperty E)
    (hF : ∀ K : P.FullSubcategory, P (F.obj K.obj))
    (hG : ∀ K : Q.FullSubcategory, Q (G.obj K.obj))
    (hL : ∀ K : P.FullSubcategory, Q (L.obj K.obj)) (e : L ⋙ G ≅ F ⋙ L)
    (R : Q.FullSubcategory ⥤ P.FullSubcategory) (a : Q.lift (P.ι ⋙ L) hL ⊣ R)
    [(P.lift (P.ι ⋙ F) hF).IsEquivalence]
    [(Q.lift (Q.ι ⋙ G) hG).IsEquivalence] :
    pairHeartRight F G L P Q hF hG hL e R a ⋙ pairHeartForget F P ≅
      pairHeartForget G Q ⋙ R :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

private def curveWeilRight :
    sfCommonStageWeilSheaf D l hl c.U Ω ⥤ sfCommonStageWeilSheaf D l hl c.C Ω := by
  letI : ((sfCommonStageHeartProperty l (D.geometricFiber c.C).left Ω).lift
      ((sfCommonStageHeartProperty l (D.geometricFiber c.C).left Ω).ι ⋙
        sfCommonStageWeilFrobeniusPullback D l hl c.C Ω)
      (zlHeartFrobenius_mem D l hl Ω c.C)).IsEquivalence :=
    curveHeartFrobenius_equiv D l hl Ω c.C
  letI : ((sfCommonStageHeartProperty l (D.geometricFiber c.U).left Ω).lift
      ((sfCommonStageHeartProperty l (D.geometricFiber c.U).left Ω).ι ⋙
        sfCommonStageWeilFrobeniusPullback D l hl c.U Ω)
      (zlHeartFrobenius_mem D l hl Ω c.U)).IsEquivalence :=
    curveHeartFrobenius_equiv D l hl Ω c.U
  exact pairHeartRight _ _ _ _ _ (zlHeartFrobenius_mem D l hl Ω c.C)
    (zlHeartFrobenius_mem D l hl Ω c.U) (qbarCurveRestriction_mem D l hl Ω c)
    (zlFrobeniusSquare D l hl Ω c.j) _ (qbarCurveOrdinaryAdjunction D l hl Ω c)

private def curveWeilAdjunction :
    zlWeilPull D l hl Ω c.j ⊣ curveWeilRight D l hl Ω c := by
  letI : ((sfCommonStageHeartProperty l (D.geometricFiber c.C).left Ω).lift
      ((sfCommonStageHeartProperty l (D.geometricFiber c.C).left Ω).ι ⋙
        sfCommonStageWeilFrobeniusPullback D l hl c.C Ω)
      (zlHeartFrobenius_mem D l hl Ω c.C)).IsEquivalence :=
    curveHeartFrobenius_equiv D l hl Ω c.C
  letI : ((sfCommonStageHeartProperty l (D.geometricFiber c.U).left Ω).lift
      ((sfCommonStageHeartProperty l (D.geometricFiber c.U).left Ω).ι ⋙
        sfCommonStageWeilFrobeniusPullback D l hl c.U Ω)
      (zlHeartFrobenius_mem D l hl Ω c.U)).IsEquivalence :=
    curveHeartFrobenius_equiv D l hl Ω c.U
  exact pairHeartAdjunction _ _ _ _ _ (zlHeartFrobenius_mem D l hl Ω c.C)
    (zlHeartFrobenius_mem D l hl Ω c.U) (qbarCurveRestriction_mem D l hl Ω c)
    (zlFrobeniusSquare D l hl Ω c.j) _ (qbarCurveOrdinaryAdjunction D l hl Ω c)

/-- Ordinary inverse image of Weil sheaves has ordinary direct image as right adjoint.
Source: Weil II (1.1.1), blueprint def-wf-middle-extension
(blueprint: def-wf-middle-extension).
Proof: ordinary j_* is sectionwise evaluation at V times_C U. Its Frobenius
comparison is the counit mate of zlFrobeniusSquare. The inverse Frobenius square
makes that mate invertible. The sheaf adjunction therefore restricts to equivariant
maps. On the finite boundary, stalks are inertia invariants, finite dimensional;
thus j_* preserves constructibility. Pass through rationalization and common stages.
No Frobenius-stable integral lattice is needed. -/
theorem qbarCurveWeilPull_isLeftAdjoint :
    (zlWeilPull D l hl Ω c.j).IsLeftAdjoint := by
  exact (curveWeilAdjunction D l hl Ω c).isLeftAdjoint

/-- Ordinary direct image on the recorded common-stage Weil heart, determined by
its adjunction to the actual inverse image, including its unit and counit.
Source: blueprint ordinary j_* convention (blueprint: def-wf-middle-extension). -/
def qbarCurveWeilOrdinaryPushforward :
    sfCommonStageWeilSheaf D l hl c.U Ω ⥤ sfCommonStageWeilSheaf D l hl c.C Ω :=
  @Functor.rightAdjoint _ _ _ _ (zlWeilPull D l hl Ω c.j)
    (qbarCurveWeilPull_isLeftAdjoint D l hl Ω c)

/-- Forget the Weil structure while retaining the actual geometric heart object.
Source: blueprint sheaf-theoretic convention (blueprint: def-wf-middle-extension). -/
def qbarCurveWeilHeartForget (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageHeart l (D.geometricFiber X₀).left Ω where
  obj M := ⟨M.obj.carrier, M.property⟩
  map f := ObjectProperty.homMk f.hom.hom.f

/-- The ordinary Weil direct image forgets to the recorded ordinary geometric j_*.
Source: blueprint sections formula (blueprint: def-wf-middle-extension).
Proof: the two functors are right adjoints to the same inverse-image operation
after forgetting Frobenius. The adjunction bijections identify the comparison,
whose section maps are identity maps on G(V times_C U). Frobenius is the mate of
the normalized pullback square, so this comparison respects the induced Weil map. -/
theorem qbarCurveWeilOrdinaryPushforward_forget :
    Nonempty (qbarCurveWeilOrdinaryPushforward D l hl Ω c ⋙
        qbarCurveWeilHeartForget D l hl Ω c.C ≅
      qbarCurveWeilHeartForget D l hl Ω c.U ⋙
        qbarCurveOrdinaryPushforward D l hl Ω c) := by
  let a := @Adjunction.ofIsLeftAdjoint _ _ _ _ (zlWeilPull D l hl Ω c.j)
    (qbarCurveWeilPull_isLeftAdjoint D l hl Ω c)
  let b := curveWeilAdjunction D l hl Ω c
  refine ⟨Functor.isoWhiskerRight (a.rightAdjointUniq b)
    (qbarCurveWeilHeartForget D l hl Ω c.C) ≪≫ ?_⟩
  letI : ((sfCommonStageHeartProperty l (D.geometricFiber c.C).left Ω).lift
      ((sfCommonStageHeartProperty l (D.geometricFiber c.C).left Ω).ι ⋙
        sfCommonStageWeilFrobeniusPullback D l hl c.C Ω)
      (zlHeartFrobenius_mem D l hl Ω c.C)).IsEquivalence :=
    curveHeartFrobenius_equiv D l hl Ω c.C
  letI : ((sfCommonStageHeartProperty l (D.geometricFiber c.U).left Ω).lift
      ((sfCommonStageHeartProperty l (D.geometricFiber c.U).left Ω).ι ⋙
        sfCommonStageWeilFrobeniusPullback D l hl c.U Ω)
      (zlHeartFrobenius_mem D l hl Ω c.U)).IsEquivalence :=
    curveHeartFrobenius_equiv D l hl Ω c.U
  exact pairHeartRightForget _ _ _ _ _ (zlHeartFrobenius_mem D l hl Ω c.C)
    (zlHeartFrobenius_mem D l hl Ω c.U) (qbarCurveRestriction_mem D l hl Ω c)
    (zlFrobeniusSquare D l hl Ω c.j) _ (qbarCurveOrdinaryAdjunction D l hl Ω c)

variable (F : FourierSetting.{u})

/-- Arithmetic affine-line geometry, with its actual characteristic.
Source: blueprint affine-line application (blueprint: def-wf-middle-extension).
Proof: the line is Spec k0[x], a Noetherian integral scheme. Its global sections
are the polynomial k0-algebra and have characteristic p, as k0 has p^a elements. -/
theorem qbarAffineArithmeticGeometry :
    IsNoetherian (fourierAffineModel F PUnit.{u + 1}).left ∧
      CharP Γ((fourierAffineModel F PUnit.{u + 1}).left, ⊤) F.field.p := by
  constructor
  · let : IsLocallyNoetherian (fourierAffineModel F PUnit.{u + 1}).left :=
      LocallyOfFiniteType.isLocallyNoetherian (fourierAffineModel F PUnit.{u + 1}).hom
    let : CompactSpace (fourierAffineModel F PUnit.{u + 1}).left :=
      QuasiCompact.compactSpace_of_compactSpace (fourierAffineModel F PUnit.{u + 1}).hom
    exact ⟨⟩
  · let := fourierBaseCharacteristic F
    let z := AffineSpace.zeroSection PUnit.{u + 1} (Spec (.of F.field.k₀))
    let : Nontrivial Γ((fourierAffineModel F PUnit.{u + 1}).left, ⊤) :=
      z.appTop.hom.domain_nontrivial
    exact CharP.of_ringHom_of_ne_zero
      ((Scheme.ΓSpecIso (CommRingCat.of F.field.k₀)).inv ≫
        (fourierAffineModel F PUnit.{u + 1}).hom.appTop).hom
      F.field.p F.field.prime.ne_zero

/-- The explicit arithmetic constant line [1]. The trivial-character projector on
the Artin--Schreier cover of the zero function has invariant sections exactly the
constant coefficient sheaf. Complete, rationalize and then shift by one.
Source: blueprint ordinary-image shift convention (blueprint: def-wf-middle-extension). -/
def qbarAffineArithmeticShiftLine :
    generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar
      (fourierAffineModel F PUnit.{u + 1}).left :=
  letI := (qbarAffineArithmeticGeometry F).1
  letI := (qbarAffineArithmeticGeometry F).2
  (shiftFunctor _ (1 : ℤ)).obj
    ⟨fourierCoefficientStage F,
      (sfRationalConstructibleLocalization F.coefficients.l (fourierCoefficient F)
        (fourierAffineModel F PUnit.{u + 1}).left).obj
        ⟨fourierAdicArtinSchreier F (fourierAffineModel F PUnit.{u + 1}).left 1 0,
          fourierAdicArtinSchreier_mem F (fourierAffineModel F PUnit.{u + 1}).left 1 0⟩⟩

/-- Canonical shift [1] of fixed Frobenius pairs on the affine line. The shift line
is defined over k0, hence has the normalized arithmetic-descent Weil map. Tensor
uses the recorded monoidal Frobenius comparison; no independent map is supplied.
Source: blueprint final paragraph (blueprint: def-wf-middle-extension). -/
def qbarAffineWeilShift :
    sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
        (fourierAffineModel F PUnit.{u + 1}) F.coefficients.Qbar ⥤
      sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
        (fourierAffineModel F PUnit.{u + 1}) F.coefficients.Qbar :=
  fourierWeilTensorFunctor F (fourierAffineModel F PUnit.{u + 1})
    (fourierModelWeil F (fourierAffineModel F PUnit.{u + 1})
      (qbarAffineArithmeticShiftLine F))

/-- The explicit shift-line tensor is naturally the actual cohomological shift.
Source: blueprint final paragraph (blueprint: def-wf-middle-extension).
Proof: the trivial-character projector averages over the finite torsor. Its invariant
sections descend uniquely to the base, identifying its completed image with the
constant coefficient module, with section 1 as unit. The map m tensor 1 to m
is its unit comparison. Apply the signed tensor/shift comparison and descend
through rationalization and common stages. Arithmetic descent gives the constant
line its usual Frobenius, and monoidal pullback preserves this unit comparison.
Thus the construction shifts the given Weil structure, without changing it. -/
theorem qbarAffineWeilShift_forget :
    Nonempty (qbarAffineWeilShift F ⋙
        sfCommonStageWeilForget F.field F.coefficients.l F.coefficients.different
          (fourierAffineModel F PUnit.{u + 1}) F.coefficients.Qbar ≅
      sfCommonStageWeilForget F.field F.coefficients.l F.coefficients.different
          (fourierAffineModel F PUnit.{u + 1}) F.coefficients.Qbar ⋙
        shiftFunctor _ (1 : ℤ)) := by
  let X₀ := fourierAffineModel F PUnit.{u + 1}
  let X := (F.field.geometricFiber X₀).left
  let := (qbarAffineArithmeticGeometry F).1
  let := (qbarAffineArithmeticGeometry F).2
  let := fourierModelPrimeInvertible F X₀
  let := sfWeilPrimeInvertible F.field F.coefficients.l F.coefficients.different X₀
  let P := commonStageDerivedPullback F.coefficients.l F.coefficients.Qbar
    (fourierModelProjection F X₀)
  let A : generalAlgebraicallyClosedConstructibleCategory F.coefficients.l
      F.coefficients.Qbar X₀.left :=
    ⟨fourierCoefficientStage F,
      (sfRationalConstructibleLocalization F.coefficients.l (fourierCoefficient F) X₀.left).obj
        ⟨fourierAdicArtinSchreier F X₀.left 1 0,
          fourierAdicArtinSchreier_mem F X₀.left 1 0⟩⟩
  obtain ⟨a⟩ := fourierTrivialCharacter_unit F X₀.left
  have h := derivedPullbackTensorIso F.coefficients.l (fourierCoefficient F)
    (fourierModelProjection F X₀) 0 F.coefficients.Qbar
  have hu : canonicalCommonStagePullbackTensor_unit F.coefficients.l
      F.coefficients.Qbar (fourierModelProjection F X₀) :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨ε, _, _⟩ := hu
  let e : P.obj (A⟦(1 : ℤ)⟧) ≅
      (pullbackTensorCommonUnit F.coefficients.l F.coefficients.Qbar X)⟦(1 : ℤ)⟧ :=
    (P.commShiftIso (1 : ℤ)).app A ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso (P.mapIso a ≪≫ ε)
  let T := commonStageDerivedTensor F.coefficients.l F.coefficients.Qbar X
  let N := fourierModelWeil F X₀ (qbarAffineArithmeticShiftLine F)
  let eT : fourierTensorUnderlying F X₀ N ≅
      Functor.prod' (𝟭 _) ((Functor.const _).obj
        ((pullbackTensorCommonUnit F.coefficients.l F.coefficients.Qbar X)⟦(1 : ℤ)⟧)) ⋙ T :=
    NatIso.ofComponents (fun K ↦ T.mapIso (Iso.prod (Iso.refl K) e)) (fun f ↦ by
      change T.map (Prod.mkHom f (𝟙 _)) ≫ T.map (Prod.mkHom (𝟙 _) e.hom) =
        T.map (Prod.mkHom (𝟙 _) e.hom) ≫ T.map (Prod.mkHom f (𝟙 _))
      rw [← T.map_comp, ← T.map_comp]
      congr 1
      ext <;> simp)
  obtain ⟨s⟩ := commonStageShiftedUnit_tensor F.coefficients.l F.coefficients.Qbar X (1 : ℤ)
  exact ⟨Functor.isoWhiskerLeft
    (sfCommonStageWeilForget F.field F.coefficients.l F.coefficients.different
      X₀ F.coefficients.Qbar) (eT ≪≫ s)⟩

end WeilConjectures
