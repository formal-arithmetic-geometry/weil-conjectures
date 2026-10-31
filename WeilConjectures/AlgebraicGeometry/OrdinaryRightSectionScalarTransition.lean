/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSystemImageData
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-!
# Operations and transitions of the normalized ordinary right image

Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10, printed pp. 21--23;
Stacks Project, Tags 00YV and 03D3
(blueprint: lem-pur-ordinary-right-section-laws).

The comparison below is the prescribed composite, natural in the strict system.
Scalar restriction is represented by `coefficientRestrictionUnderlying`, whose section
functions are identities. No transition of the system is required to be invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
namespace SheafOfModules

/-- The specified underlying comparison, as a natural isomorphism in the strict system.
Its component is exactly the composite of `rightEvaluation` and `rightUnderlying`.
Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10, printed pp. 21--23
(blueprint: lem-pur-ordinary-right-section-laws). -/
def ordinaryRightSectionScalarTransitionComparison
    {T U : Scheme.{u}} (g : T ⟶ U) (O : Type (u + 1)) [CommRing O] (t : O)
    (B : CoefficientSystemOrdinaryImage.{u + 1, u, u + 1, u, u + 1}
      (J := Scheme.ProEt.topology U) (K := Scheme.ProEt.topology T) O t
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
      (Scheme.proEtaleSheafDirectImage g (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction g (Type (u + 1)))) (n : ℕ) :
    B.rightSystem ⋙ coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology U) (O := O) (ell := t) n ⋙
        coefficientUnderlying (J := Scheme.ProEt.topology U) O t n ≅
      coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology T) (O := O) (ell := t) n ⋙
        coefficientUnderlying (J := Scheme.ProEt.topology T) O t n ⋙
          Scheme.proEtaleSheafDirectImage g (Type (u + 1)) :=
  Functor.isoWhiskerRight (B.rightEvaluation n)
      (coefficientUnderlying (J := Scheme.ProEt.topology U) O t n) ≪≫
    Functor.isoWhiskerLeft (coefficientEvaluation.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology T) (O := O) (ell := t) n)
      (B.rightUnderlying n)

private theorem constant_section_apply (W : Scheme.{u})
    (O : Type (u + 1)) [CommRing O] (t : O) (n : ℕ)
    (a : O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1)) (V : W.ProEtᵒᵖ)
    (z : ((constantSheaf (Scheme.ProEt.topology W) (Type (u + 1))).obj
      PUnit).obj.obj V) :
    (coefficientConstantSection (J := Scheme.ProEt.topology W) O t n a).hom.app V z =
      (toSheafify (Scheme.ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1))))).app V a := by
  let J := Scheme.ProEt.topology W
  let P := (Functor.const W.ProEtᵒᵖ).obj (PUnit : Type (u + 1))
  have hp : Presheaf.IsSheaf J P := Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit
  let := isIso_toSheafify J hp
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso ((toSheafify J P).app V)).surjective z
  subst z
  let Q := (sheafCompose J (CategoryTheory.forget CommRingCat.{u + 1})).obj
    (coefficientQuotientSheaf.{u + 1, u, u + 1} (J := J) O t n)
  let c : P ⟶ Q.obj :=
    (Functor.const W.ProEtᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{u + 2}) ↦ a)) ≫
      Functor.whiskerRight (toSheafify J ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1)))))
          (CategoryTheory.forget CommRingCat.{u + 1})
  have he : toSheafify J P ≫
      (coefficientConstantSection (J := J) O t n a).hom = c :=
    toSheafify_sheafifyLift J c Q.property
  exact congrArg (fun f ↦ f.app V x) he

/-- Transport a transition square across isomorphisms on its two levels. -/
private theorem inverse_transition_naturality
    {C D : Type*} [Category C] [Category D] (R : D ⥤ C)
    {A B X : C} {A' B' X' : D} (e : A ≅ B) (e' : A' ≅ B')
    (a : A ⟶ R.obj A') (b : B ⟶ R.obj B')
    (h : A ⟶ X) (h' : A' ⟶ X') (x : X ⟶ R.obj X')
    (ha : a ≫ R.map e'.hom = e.hom ≫ b)
    (hh : h ≫ x = a ≫ R.map h') :
    (e.inv ≫ h) ≫ x = b ≫ R.map (e'.inv ≫ h') := by
  have he : e.inv ≫ a = b ≫ R.map e'.inv := by
    apply (cancel_mono (R.map e'.hom)).mp
    simp only [Category.assoc, ← R.map_comp, e'.inv_hom_id, R.map_id,
      Category.comp_id]
    rw [ha, e.inv_hom_id_assoc]
  rw [Category.assoc, hh, ← Category.assoc, he]
  simp only [Functor.map_comp, Category.assoc]

/-- Apply a functor to a transition square and then a natural comparison. -/
private theorem map_transition_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (G : D ⥤ E) (F : C ⥤ E) (q : R ⋙ G ⟶ F)
    {A B I : D} {H M : C} (h : A ⟶ B) (t : B ⟶ R.obj M)
    (i : A ⟶ I) (r : I ⟶ R.obj H) (h' : H ⟶ M)
    (hh : h ≫ t = i ≫ r ≫ R.map h') :
    G.map h ≫ G.map t ≫ q.app M = G.map i ≫ G.map r ≫ q.app H ≫ F.map h' := by
  calc
    _ = G.map (h ≫ t) ≫ q.app M := by rw [Functor.map_comp, Category.assoc]
    _ = G.map (i ≫ r ≫ R.map h') ≫ q.app M :=
      congrArg (fun z : A ⟶ R.obj M ↦ G.map z ≫ q.app M) hh
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      have hq : G.map (R.map h') ≫ q.app M = q.app H ≫ F.map h' := q.naturality h'
      rw [hq]

/-- Transport a square to the specified adjunct comparison maps. -/
private theorem transpose_transition_naturality
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {V : D ⥤ C}
    (adj : L ⊣ V) {X X' : C} {Y Y' : D}
    (u : X ⟶ X') (v : Y ⟶ Y') (f : L.obj X ⟶ Y) (f' : L.obj X' ⟶ Y')
    (b : X ⟶ V.obj Y) (b' : X' ⟶ V.obj Y')
    (hb : b = adj.homEquiv _ _ f) (hb' : b' = adj.homEquiv _ _ f')
    (hf : f ≫ v = L.map u ≫ f') : u ≫ b' = b ≫ V.map v := by
  rw [hb, hb']
  exact adj.homEquiv_naturality_left_square u f' f v hf.symm

/-- Cancel underlying comparison isomorphisms in a three-square diagram. -/
private theorem underlying_transition_naturality
    {C : Type*} [Category C]
    {A B R S X Y Z A' B' R' : C}
    (e : A ≅ A') (d : B ≅ B') (f : R ≅ R')
    (i : A ⟶ R) (r : R ⟶ S) (q : S ⟶ B)
    (h : A ⟶ X) (h' : B ⟶ Z) (x : X ⟶ Y) (y : Y ⟶ Z)
    (j : A' ⟶ R') (k : R' ⟶ B')
    (hh : h ≫ x ≫ y = i ≫ r ≫ q ≫ h')
    (hr : r ≫ q ≫ d.hom = f.hom ≫ k)
    (hi : i ≫ f.hom = e.hom ≫ j) :
    (e.inv ≫ h) ≫ (x ≫ y) = (j ≫ k) ≫ d.inv ≫ h' := by
  apply (cancel_epi e.hom).mp
  simp only [← Category.assoc, e.hom_inv_id, Category.id_comp]
  rw [Category.assoc h x y, hh]
  have hq : r ≫ q = f.hom ≫ k ≫ d.inv := by
    apply (cancel_mono d.hom).mp
    simpa only [Category.assoc, d.inv_hom_id, Category.comp_id] using hr
  simp only [Category.assoc] at *
  rw [← Category.assoc r q h', hq]
  simp only [← Category.assoc]
  rw [hi]

/-! Helper for scalar action and transition laws.
(blueprint: lem-pur-ordinary-right-section-scalar-transition). -/
set_option maxHeartbeats 1600000 in
-- The proof combines several naturality squares over the large pro-etale categories.
/-- This is the corresponding strictly smaller clause of the ordinary right-section laws.
Source: Zheng, Construction 4.1 and the ordinary system morphism preceding Lemma 4.10,
printed pp. 21--23; Stacks Project Tags 00YV and 03D3.
Proof plan: Apply the module scalar graph equation to the universal product test object
and use naturality of the adjunction unit. The transition equality follows by substituting
the inverse-transition and restriction-underlying equations and cancelling the displayed
isomorphisms.
(blueprint: lem-pur-ordinary-right-section-scalar-transition). -/
theorem ordinaryRightSectionScalarTransition
    {T U : Scheme.{u}} (g : T ⟶ U) (O : Type (u + 1)) [CommRing O] (t : O)
    (B : CoefficientSystemOrdinaryImage.{u + 1, u, u + 1, u, u + 1}
      (J := Scheme.ProEt.topology U) (K := Scheme.ProEt.topology T) O t
      (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
      (Scheme.proEtaleSheafDirectImage g (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction g (Type (u + 1))))
    (M : CoefficientSystem (J := Scheme.ProEt.topology T) O t) (n : ℕ) :
    (∀ (V : U.ProEtᵒᵖ)
      (a : (coefficientQuotientSheaf (J := Scheme.ProEt.topology U) O t n).obj.obj V)
      (x : ((B.rightSystem.obj M).level n).val.obj V),
      ((ordinaryRightSectionScalarTransitionComparison g O t B n).hom.app M).hom.app V (a • x) =
        (Scheme.proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
          (CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1)))).hom.app V a •
        @id ((M.level n).val.obj ((Scheme.proEtaleBaseChange g).op.obj V))
          (((ordinaryRightSectionScalarTransitionComparison g O t B n).hom.app M).hom.app V x)) ∧
    ((coefficientUnderlying (J := Scheme.ProEt.topology U) O t (n + 1)).map
        ((B.rightSystem.obj M).transition n) ≫
      (coefficientRestrictionUnderlying (J := Scheme.ProEt.topology U)
        O t (Nat.le_succ n)).hom.app ((B.rightSystem.obj M).level n) ≫
      (ordinaryRightSectionScalarTransitionComparison g O t B n).hom.app M =
    (ordinaryRightSectionScalarTransitionComparison g O t B (n + 1)).hom.app M ≫
      (Scheme.proEtaleSheafDirectImage g (Type (u + 1))).map
        ((coefficientUnderlying (J := Scheme.ProEt.topology T) O t (n + 1)).map
            (M.transition n) ≫
          (coefficientRestrictionUnderlying (J := Scheme.ProEt.topology T)
            O t (Nat.le_succ n)).hom.app (M.level n))) := by
  let L := Scheme.proEtaleSheafInverseImage g (Type (u + 1))
  let V := Scheme.proEtaleSheafDirectImage g (Type (u + 1))
  let adj := Scheme.proEtaleSheafAdjunction g (Type (u + 1))
  let F := coefficientUnderlying.{u + 1, u, u + 1} (J := Scheme.ProEt.topology U) O t
  let G := coefficientUnderlying.{u + 1, u, u + 1} (J := Scheme.ProEt.topology T) O t
  let H := B.rightSystem.obj M
  let ε : B.inverse.obj H ⟶ M := B.systemAdj.counit.app M
  let α (i : ℕ) : (B.inverse.obj H).level i ≅
      (B.lift i).modules.obj (H.level i) := (B.inverseEvaluation i).app H
  let e (i : ℕ) (N : coefficientLevelModules (J := Scheme.ProEt.topology U) O t i) :
      (G i).obj ((B.lift i).modules.obj N) ≅ L.obj ((F i).obj N) :=
    (B.lift i).moduleUnderlying.app N
  let h (i : ℕ) : (B.lift i).modules.obj (H.level i) ⟶ M.level i :=
    (α i).inv ≫ ε.app i
  let f (i : ℕ) : L.obj ((F i).obj (H.level i)) ⟶ (G i).obj (M.level i) :=
    (e i (H.level i)).inv ≫ (G i).map (h i)
  have hb (i : ℕ) :
      (ordinaryRightSectionScalarTransitionComparison g O t B i).hom.app M =
        adj.homEquiv _ _ (f i) := by
    have heps : B.systemAdj.homEquiv H M ε = 𝟙 H := by
      dsimp only [ε]
      rw [← B.systemAdj.homEquiv_symm_id M, Equiv.apply_symm_apply]
    let E := coefficientEvaluation.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology U) (O := O) (ell := t) i
    have hepsmap : E.map (B.systemAdj.homEquiv H M ε) = 𝟙 (H.level i) :=
      (congrArg E.map heps).trans (E.map_id H)
    have hs' : (B.rightEvaluation i).hom.app M =
        (B.levelAdj i).homEquiv (H.level i) (M.level i) (h i) := by
      calc
        _ = (𝟙 (H.level i)) ≫ (B.rightEvaluation i).hom.app M :=
          (Category.id_comp _).symm
        _ = E.map (B.systemAdj.homEquiv H M ε) ≫
            (B.rightEvaluation i).hom.app M :=
          congrArg (fun q ↦ q ≫ (B.rightEvaluation i).hom.app M) hepsmap.symm
        _ = _ := B.systemTranspose H M ε i
    change (F i).map ((B.rightEvaluation i).hom.app M) ≫
      (B.rightUnderlying i).hom.app (M.level i) = _
    rw [hs']
    exact B.levelTranspose i _ _ (h i)
  constructor
  · let A := (sheafCompose (Scheme.ProEt.topology U)
      (CategoryTheory.forget CommRingCat.{u + 1})).obj
        (coefficientQuotientSheaf.{u + 1, u, u + 1} (J := Scheme.ProEt.topology U) O t n)
    let k := adj.homEquiv _ _ (B.lift n).ringUnderlying.hom
    let ρ := Scheme.proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
      (CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1)))
    have hk : k = (sheafCompose (Scheme.ProEt.topology U)
        (CategoryTheory.forget CommRingCat.{u + 1})).map ρ := by
      have hg (W : U.ProEtᵒᵖ) (a : O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1)) :
          k.hom.app W ((toSheafify (Scheme.ProEt.topology U)
            ((Functor.const U.ProEtᵒᵖ).obj
              (CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1))))).app W a) =
          ρ.hom.app W ((toSheafify (Scheme.ProEt.topology U)
            ((Functor.const U.ProEtᵒᵖ).obj
              (CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1))))).app W a) := by
        let z := (toSheafify (Scheme.ProEt.topology U)
          ((Functor.const U.ProEtᵒᵖ).obj (PUnit : Type (u + 1)))).app W PUnit.unit
        have hc : coefficientConstantSection (J := Scheme.ProEt.topology U) O t n a ≫ k =
            adj.homEquiv _ _ (B.singleton.hom ≫
              coefficientConstantSection (J := Scheme.ProEt.topology T) O t n a) := by
          rw [← adj.homEquiv_naturality_left, B.constants]
        have hc' := congrArg (fun q ↦ q.hom.app W z) hc
        rw [Adjunction.homEquiv_unit] at hc'
        change k.hom.app W
            ((coefficientConstantSection (J := Scheme.ProEt.topology U) O t n a).hom.app W z) =
          (coefficientConstantSection (J := Scheme.ProEt.topology T) O t n a).hom.app
            ((Scheme.proEtaleBaseChange g).op.obj W) _ at hc'
        rw [constant_section_apply, constant_section_apply] at hc'
        let R := CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1))
        let er := (sheafificationAdjunction (Scheme.ProEt.topology U)
          CommRingCat.{u + 1}).homEquiv ((Functor.const U.ProEtᵒᵖ).obj R)
            ((Scheme.proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
              ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj R))
        have hr := er.apply_symm_apply (Functor.whiskerLeft (Scheme.proEtaleBaseChange g).op
                    (toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj R)))
        rw [Adjunction.homEquiv_unit] at hr
        exact hc'.trans (congrArg (fun q ↦ q.app W a) hr).symm
      apply Sheaf.hom_ext
      let P := (Functor.const U.ProEtᵒᵖ).obj
        (CommRingCat.of (O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1)))
      let e := sheafifyComposeIso (Scheme.ProEt.topology U)
        (CategoryTheory.forget CommRingCat.{u + 1}) P
      apply (cancel_epi e.hom).mp
      apply sheafify_hom_ext _ _ _ ((V.obj
        ((sheafCompose (Scheme.ProEt.topology T)
          (CategoryTheory.forget CommRingCat.{u + 1})).obj
            (coefficientQuotientSheaf.{u + 1, u, u + 1}
              (J := Scheme.ProEt.topology T) O t n))).property)
      dsimp only [e]
      simp only [← Category.assoc, sheafComposeIso_hom_fac]
      ext W a
      exact hg W a
    let X := (F n).obj (H.level n)
    let P := A ⊗ X
    let a : P ⟶ A := CartesianMonoidalCategory.fst _ _
    let b : P ⟶ X := CartesianMonoidalCategory.snd _ _
    let μ : P ⟶ X := ⟨{
      app := fun W ↦ ↾fun z ↦
        @SMul.smul
          ((coefficientQuotientSheaf.{u + 1, u, u + 1}
            (J := Scheme.ProEt.topology U) O t n).obj.obj W)
          ((H.level n).val.obj W) inferInstance z.1 z.2
      naturality := by
        intro W Z i
        ext z
        exact (H.level n).val.map_smul i z.1 z.2 |>.symm }⟩
    intro W c x
    let z : P.obj.obj W := (c, x)
    let y := (adj.unit.app P).hom.app W z
    have hs := (B.lift n).moduleSMul (H.level n) P a b μ (fun _ _ ↦ rfl)
      ((Scheme.proEtaleBaseChange g).op.obj W) y
    have hn (Y : Sheaf (Scheme.ProEt.topology U) (Type (u + 1))) (q : P ⟶ Y) :
        (L.map q).hom.app ((Scheme.proEtaleBaseChange g).op.obj W) y =
          (adj.unit.app Y).hom.app W (q.hom.app W z) := by
      exact (congrArg (fun r ↦ r.hom.app W z) (adj.unit.naturality q)).symm
    rw [hn X μ, hn A a, hn X b] at hs
    have he := congrArg ((h n).val.app ((Scheme.proEtaleBaseChange g).op.obj W)) hs
    rw [map_smul] at he
    have heq := congrArg (fun q ↦ q.hom.app W) (hb n)
    rw [Adjunction.homEquiv_unit] at heq
    simp only [heq, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply]
    have hkc := congrArg (fun q ↦ q.hom.app W c) hk
    dsimp only [k] at hkc
    rw [Adjunction.homEquiv_unit] at hkc
    change _ = ρ.hom.app W c at hkc
    change (B.lift n).ringUnderlying.hom.hom.app
        ((Scheme.proEtaleBaseChange g).op.obj W) ((adj.unit.app A).hom.app W c) =
      ρ.hom.app W c at hkc
    change (h n).val.app ((Scheme.proEtaleBaseChange g).op.obj W)
        (((B.lift n).moduleUnderlying.inv.app (H.level n)).hom.app
          ((Scheme.proEtaleBaseChange g).op.obj W)
            ((adj.unit.app X).hom.app W (c • x))) =
      ρ.hom.app W c •
        (h n).val.app ((Scheme.proEtaleBaseChange g).op.obj W)
          (((B.lift n).moduleUnderlying.inv.app (H.level n)).hom.app
            ((Scheme.proEtaleBaseChange g).op.obj W) ((adj.unit.app X).hom.app W x))
    change (h n).val.app ((Scheme.proEtaleBaseChange g).op.obj W)
        (((B.lift n).moduleUnderlying.inv.app (H.level n)).hom.app
          ((Scheme.proEtaleBaseChange g).op.obj W)
            ((adj.unit.app X).hom.app W (c • x))) =
      (B.lift n).ringUnderlying.hom.hom.app
          ((Scheme.proEtaleBaseChange g).op.obj W) ((adj.unit.app A).hom.app W c) •
        (h n).val.app ((Scheme.proEtaleBaseChange g).op.obj W)
          (((B.lift n).moduleUnderlying.inv.app (H.level n)).hom.app
            ((Scheme.proEtaleBaseChange g).op.obj W) ((adj.unit.app X).hom.app W x)) at he
    rw [hkc] at he
    exact he
  · let qU := coefficientRestrictionUnderlying.{u + 1, u, u + 1} (J := Scheme.ProEt.topology U)
      O t (Nat.le_succ n)
    let qT := coefficientRestrictionUnderlying.{u + 1, u, u + 1} (J := Scheme.ProEt.topology T)
      O t (Nat.le_succ n)
    let RT := coefficientRestriction.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology T) O t (Nat.le_succ n)
    let RU := coefficientRestriction.{u + 1, u, u + 1}
      (J := Scheme.ProEt.topology U) O t (Nat.le_succ n)
    let r : (B.lift (n + 1)).modules.obj (RU.obj (H.level n)) ⟶
        RT.obj ((B.lift n).modules.obj (H.level n)) :=
      (B.restrictInverse (Nat.le_succ n)).hom.app (H.level n)
    let u := (F (n + 1)).map (H.transition n) ≫ qU.hom.app (H.level n)
    let v := (G (n + 1)).map (M.transition n) ≫ qT.hom.app (M.level n)
    have hh : h (n + 1) ≫ M.transition n =
        (B.lift (n + 1)).modules.map (H.transition n) ≫ r ≫ RT.map (h n) := by
      simpa only [h, Category.assoc] using
        inverse_transition_naturality RT (α (n + 1)) (α n)
        ((B.inverse.obj H).transition n)
        ((B.lift (n + 1)).modules.map (H.transition n) ≫ r)
        (ε.app (n + 1)) (ε.app n) (M.transition n)
        (B.inverseTransition n H) (ε.comm n)
    have hf : f (n + 1) ≫ v = L.map u ≫ f n := by
      have hr : (G (n + 1)).map r ≫
          qT.hom.app ((B.lift n).modules.obj (H.level n)) ≫ (e n (H.level n)).hom =
          (e (n + 1) (RU.obj (H.level n))).hom ≫ L.map (qU.hom.app (H.level n)) :=
        B.restrictInverseUnderlying (Nat.le_succ n) (H.level n)
      have he : (G (n + 1)).map ((B.lift (n + 1)).modules.map (H.transition n)) ≫
          (e (n + 1) (RU.obj (H.level n))).hom =
          (e (n + 1) (H.level (n + 1))).hom ≫
            L.map ((F (n + 1)).map (H.transition n)) :=
        (B.lift (n + 1)).moduleUnderlying.hom.naturality (H.transition n)
      have hhh := map_transition_naturality RT (G (n + 1)) (G n) qT.hom
        (h (n + 1)) (M.transition n)
        ((B.lift (n + 1)).modules.map (H.transition n)) r (h n) hh
      have hc := underlying_transition_naturality
        (e (n + 1) (H.level (n + 1))) (e n (H.level n))
        (e (n + 1) (RU.obj (H.level n)))
        ((G (n + 1)).map ((B.lift (n + 1)).modules.map (H.transition n)))
        ((G (n + 1)).map r) (qT.hom.app ((B.lift n).modules.obj (H.level n)))
        ((G (n + 1)).map (h (n + 1))) ((G n).map (h n))
        ((G (n + 1)).map (M.transition n)) (qT.hom.app (M.level n))
        (L.map ((F (n + 1)).map (H.transition n))) (L.map (qU.hom.app (H.level n)))
        hhh hr he
      simpa only [f, v, u, Functor.map_comp, Category.assoc] using hc
    simpa only [u, v, Category.assoc] using
      transpose_transition_naturality adj u v (f (n + 1)) (f n)
        ((ordinaryRightSectionScalarTransitionComparison g O t B (n + 1)).hom.app M)
        ((ordinaryRightSectionScalarTransitionComparison g O t B n).hom.app M)
        (hb (n + 1)) (hb n) hf

end SheafOfModules
