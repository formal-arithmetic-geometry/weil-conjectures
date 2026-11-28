/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedIntegralModel
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedRawIntegralFormula

/-! # Integral normalization of the ordinary finite closure comparison

Raw scalar change commutes with continuous integral realization.

## Implementation details

The inverse closure comparison is expanded into the ordinary coefficient compositor and the
scalar comparison. The raw scalar lift equation, naturality of
`continuousIntegralComparison` and the continuous integral normalization reduce the claim, after
cancelling the common invertible integral scalar comparison, to the inverse
`coefficientExtensionSquare` for the completed square of the scalar data.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.8.2 and
  Proposition 6.8.14(2)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AdicFiniteRealization

attribute [local irreducible] finiteCondensedClosureFunctor finiteFunctor
  pbcDerivedRestrict CoefficientPresentation.integralMap sections
  reductionDerivedChange integralDetailedTransport sfRationalConstructibleLocalization
  AlgebraicGeometry.Scheme.rationalCoefficientSheaf
  AlgebraicGeometry.Scheme.integralCoefficientSheaf pbcIntegralDatum
  completedIntegralCommRingSheafUnrestricted sfIntegralConstructible purCoefficientIso
set_option cleanup.letToHave false

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

variable [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

omit [AlgebraicGeometry.IsNoetherian X] [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] in
/-- The normalized scalar-extension square is the composite of the two balancing isomorphisms
through any common diagonal. -/
private theorem coefficientExtensionSquare_eq
    {R₀ R₁ R₂ S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R₀ ⟶ R₁) (b : R₁ ⟶ S) (c : R₀ ⟶ R₂) (d : R₂ ⟶ S) (h : a ≫ b = c ≫ d)
    (x : R₀ ⟶ S) (hx : a ≫ b = x) (hx' : c ≫ d = x) :
    coefficientExtensionSquare X a b c d h =
      Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a) (pbcDerivedScalarAdjunction b)
          (pbcDerivedScalarAdjunction x) (pbcDerivedRestrictComp a b x hx) ≪≫
        (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction c)
          (pbcDerivedScalarAdjunction d) (pbcDerivedScalarAdjunction x)
          (pbcDerivedRestrictComp c d x hx')).symm := by
  subst hx
  unfold coefficientExtensionSquare derivedRestrictionSquare
  ext : 1
  simp only [Adjunction.leftAdjointCompIso, conjugateIsoEquiv, Iso.trans_hom, Iso.symm_hom,
    Iso.symm_inv, Equiv.symm_mk, Equiv.coe_fn_mk]
  rw [conjugateEquiv_symm_comp]
  rfl

/-- Integral realization before flattening either coefficient extension. -/
@[irreducible] def finiteOrdinaryRawIntegralModel (A : FiniteCondensedData l X)
    (E : Index l (PadicAlgCl l)) :
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        finiteFunctor l X A.toCore E ⋙ pbcDerivedExtend (A.closure.leg E) ≅
      (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι ⋙
        integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) E) ⋙
          pbcDerivedExtend ((A.realization E).integralIso.hom ≫
            (A.realization E).inclusion) ⋙ pbcDerivedExtend (A.closure.leg E) := by
  let r := (A.realization E).integralIso.hom ≫ (A.realization E).inclusion
  let b := Functor.isoWhiskerRight (eqToIso (finiteRawIntegralFormula l X A E))
    (pbcDerivedExtend (A.closure.leg E))
  let d := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (A.stage E).integral.functor
      (continuousIntegralComparison l X A E)) (pbcDerivedExtend (A.closure.leg E))
  let g := Functor.isoWhiskerRight (eqToIso (A.stage E).integral_identity)
    (pbcDerivedExtend r ⋙ pbcDerivedExtend (A.closure.leg E))
  exact b ≪≫ d ≪≫ g

/-- The explicit ordinary arrow retaining the raw completed integral comparison. -/
@[irreducible] def finiteOrdinaryRawIntegralTransition (A : FiniteCondensedData l X)
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :=
  let rE := (A.realization E).integralIso.hom ≫ (A.realization E).inclusion
  let rL := (A.realization L).integralIso.hom ≫ (A.realization L).inclusion
  let c := (A.scalar.coefficient h).coefficient
  let j := Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction c)
    (pbcDerivedScalarAdjunction (A.closure.leg L))
    (pbcDerivedScalarAdjunction (A.closure.leg E))
    (pbcDerivedRestrictComp c (A.closure.leg L) (A.closure.leg E) (A.closure.cocone h))
  let n := coefficientExtensionSquare X (pbcCompletedScalarMap l (PadicAlgCl l) X h)
    rL rE c (A.scalar.completed_square h)
  j.inv.app ((pbcDerivedExtend rE).obj
      ((integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) E)).obj K.obj)) ≫
    (pbcDerivedExtend (A.closure.leg L)).map
      (n.inv.app
          ((integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) E)).obj K.obj) ≫
        (pbcDerivedExtend rL).map ((A.raw.integral.comparison h).hom.app K))

private theorem isoWhiskerRight_eqToIso_app {C D E : Type*} [Category C] [Category D]
    [Category E] {F F' : C ⥤ D} (e : F = F') (G : D ⥤ E) (K : C) :
    ∃ p, (Functor.isoWhiskerRight (eqToIso e) G).hom.app K = eqToHom p := by
  subst e
  exact ⟨rfl, by simp⟩

private theorem isoWhiskerRight_whiskerLeft_app {B C D E : Type*} [Category B] [Category C]
    [Category D] [Category E] (I : B ⥤ C) {F F' : C ⥤ D} (α : F ≅ F')
    (o : ∀ K, F.obj K = F'.obj K) (hα : ∀ K, α.hom.app K = eqToHom (o K)) (G : D ⥤ E)
    (K : B) : ∃ p, (Functor.isoWhiskerRight (Functor.isoWhiskerLeft I α) G).hom.app K =
      eqToHom p :=
  ⟨congrArg G.obj (o (I.obj K)), by simp [hα, eqToHom_map]⟩

private theorem trans_app_eqToHom {C D : Type*} [Category C] [Category D]
    {F₀ F₁ F₂ F₃ : C ⥤ D} (b : F₀ ≅ F₁) (d : F₁ ≅ F₂) (g : F₂ ≅ F₃) (K : C)
    (hb : ∃ p, b.hom.app K = eqToHom p) (hd : ∃ p, d.hom.app K = eqToHom p)
    (hg : ∃ p, g.hom.app K = eqToHom p) : ∃ p, ((b ≪≫ d ≪≫ g).app K).hom = eqToHom p := by
  obtain ⟨p, hp⟩ := hb
  obtain ⟨q, hq⟩ := hd
  obtain ⟨r, hr⟩ := hg
  exact ⟨p.trans (q.trans r), by simp [hp, hq, hr]⟩

/-- The components of `finiteOrdinaryRawIntegralModel` are object equalities. -/
private theorem finiteOrdinaryRawIntegralModel_app_hom (A : FiniteCondensedData l X)
    (E : Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    ∃ e, ((finiteOrdinaryRawIntegralModel l X A E).app K).hom = eqToHom e := by
  unfold finiteOrdinaryRawIntegralModel continuousIntegralComparison
  refine trans_app_eqToHom _ _ _ _ ?_ ?_ ?_
  · exact isoWhiskerRight_eqToIso_app (finiteRawIntegralFormula l X A E)
      (pbcDerivedExtend (A.closure.leg E)) K
  · exact isoWhiskerRight_whiskerLeft_app (A.stage E).integral.functor _
      (fun K ↦ (A.realization E).objects K) (fun _ ↦ rfl) (pbcDerivedExtend (A.closure.leg E)) K
  · exact isoWhiskerRight_eqToIso_app (A.stage E).integral_identity
      (pbcDerivedExtend ((A.realization E).integralIso.hom ≫ (A.realization E).inclusion) ⋙
        pbcDerivedExtend (A.closure.leg E)) K

private theorem heq_of_comp_eqToHom {C : Type*} [Category C] {X Y M N N' : C} (f : X ⟶ Y)
    (q : Y ⟶ N) (p : X ⟶ M) (t : M ⟶ N') (hq : ∃ e, q = eqToHom e) (hp : ∃ e, p = eqToHom e)
    (H : t ≍ f) : f ≫ q ≍ p ≫ t := by
  obtain ⟨e, rfl⟩ := hq
  obtain ⟨e', rfl⟩ := hp
  rw [comp_eqToHom_heq_iff]
  exact H.symm.trans (eqToHom_comp_heq t e').symm

private theorem heq_comp_map_comp {C D : Type*} [Category C] [Category D] (J : C ⥤ D)
    {Y₀ : D} {A B B' : C} (θ : Y₀ ⟶ J.obj A) (p : A ⟶ B) (q : B ⟶ B') (W : Y₀ ⟶ J.obj B)
    (hW : θ ≫ J.map p = W) (V : J.obj B ⟶ J.obj B') (hV : J.map q = V) {X₀ X₁ : D}
    (t : X₀ ⟶ X₁) (H : t ≍ W ≫ V) : t ≍ θ ≫ J.map (p ≫ q) := by
  rw [J.map_comp, ← Category.assoc, hW, hV]
  exact H

private theorem inv_app_comp_congr {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    {n n' : F ≅ G} (e : n = n') (Y : C) {Z : D} (m : F.obj Y ⟶ Z) :
    n.inv.app Y ≫ m = n'.inv.app Y ≫ m := by
  rw [e]

private theorem trans_symm_inv_heq {C D : Type*} [Category C] [Category D] {P Q R : C ⥤ D}
    (α : P ≅ Q) (β : R ≅ Q) {Y Y' : C} (hY : Y' = Y) {Z Z' Z'' W₀ W₁ : D}
    (m : R.obj Y ⟶ Z) (m' : R.obj Y' ⟶ Z') (hZ : Z' = Z) (hm : m' ≍ m) (f₀ : W₀ ⟶ P.obj Y')
    (hf₀ : ∃ e, f₀ = eqToHom e) (e₁ : R.obj Y' = W₁) (e₂ : W₁ = R.obj Y') (f₃ : Z' ⟶ Z'')
    (hf₃ : ∃ e, f₃ = eqToHom e) :
    (β ≪≫ α.symm).inv.app Y ≫ m ≍
      (f₀ ≫ α.hom.app Y' ≫ β.inv.app Y' ≫ eqToHom e₁) ≫ eqToHom e₂ ≫ m' ≫ f₃ := by
  subst hY hZ
  obtain ⟨e, rfl⟩ := hf₀
  obtain ⟨e', rfl⟩ := hf₃
  subst e e' e₁
  cases eq_of_heq hm
  simp [Iso.trans_inv]

private theorem map_heq_of_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y') (H : f ≍ g) :
    F.map f ≍ F.map g := by
  subst hX hY
  rw [eq_of_heq H]

/-- The integral normalization of the scalar data, solved for the inverse comparison. -/
private theorem theta_inv_comp (A : FiniteCondensedData l X) {E L : Index l (PadicAlgCl l)}
    (h : E ≤ L) (K : pbcIntegralStage l (PadicAlgCl l) X E) :
    (A.scalar.theta h).inv.app ((pbcStageLocalization l (PadicAlgCl l) X E).obj K) ≫
        (A.realization L).J.map
          ((pbcScalarIntegralComparison l (PadicAlgCl l) X _ _ h).hom.app K) =
      (pbcDerivedExtend (A.scalar.coefficient h).coefficient).map
          (eqToHom ((A.realization E).objects K)) ≫
        (Adjunction.leftAdjointCompIso
          (pbcDerivedScalarAdjunction
            ((A.realization E).integralIso.hom ≫ (A.realization E).inclusion))
          (pbcDerivedScalarAdjunction (A.scalar.coefficient h).coefficient)
          (pbcDerivedScalarAdjunction
            (((A.realization E).integralIso.hom ≫ (A.realization E).inclusion) ≫
              (A.scalar.coefficient h).coefficient))
          (pbcDerivedRestrictComp _ _ _ rfl)).hom.app K.obj ≫
        (Adjunction.leftAdjointCompIso
          (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l (PadicAlgCl l) X h))
          (pbcDerivedScalarAdjunction
            ((A.realization L).integralIso.hom ≫ (A.realization L).inclusion))
          (pbcDerivedScalarAdjunction
            (((A.realization E).integralIso.hom ≫ (A.realization E).inclusion) ≫
              (A.scalar.coefficient h).coefficient))
          (pbcDerivedRestrictComp _ _ _ (A.scalar.completed_square h))).inv.app K.obj ≫
        eqToHom ((A.realization L).objects
          ((pbcIntegralScalarExtension l (PadicAlgCl l) X _ _ h).obj K)).symm := by
  have H := A.scalar.integral
  unfold integralNormalization at H
  replace H := H h K
  rw [pbcReductionNormalization_hom_eq, pbcReductionNormalization_hom_eq] at H
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, reassoc_of% H]
  simp

/-- The source objects of the explicit ordinary arrow and of the closure comparison agree. -/
private theorem raw_source_eq (A : FiniteCondensedData l X) (E : Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    (pbcDerivedExtend ((A.realization E).integralIso.hom ≫ (A.realization E).inclusion)).obj
        ((integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) E)).obj K.obj) =
      (finiteFunctor l X A.toCore E).obj
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X).obj K) :=
  (congrArg (pbcDerivedExtend ((A.realization E).integralIso.hom ≫
      (A.realization E).inclusion)).obj
      (Functor.congr_obj (A.stage E).integral_identity K).symm).trans
    (((A.realization E).objects ((A.stage E).integral.functor.obj K)).symm.trans
      (Functor.congr_obj (finiteRawIntegralFormula l X A E) K).symm)

/-- The scalar comparison of the raw family on a rationalized integral object. -/
private theorem raw_beta (A : FiniteCondensedData l X) {E L : Index l (PadicAlgCl l)}
    (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    (A.raw.family.β h).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X).obj K) ≍
      (pbcScalarIntegralComparison l (PadicAlgCl l) X Fact.out Fact.out h).hom.app
          ((A.stage E).integral.functor.obj K) ≫
        (pbcStageLocalization l (PadicAlgCl l) X L).map
          ((A.raw.integral.integral h).hom.app K) := by
  exact A.raw.scalar_lift (E := E) (L := L) h K _ HEq.rfl

/-- The continuous realization of a localized integral arrow. -/
private theorem realization_map_stage (A : FiniteCondensedData l X) (L : Index l (PadicAlgCl l))
    {K K' : pbcIntegralStage l (PadicAlgCl l) X L} (g : K ⟶ K') :
    (A.realization L).J.map ((pbcStageLocalization l (PadicAlgCl l) X L).map g) =
      eqToHom ((A.realization L).objects K) ≫
        (pbcDerivedExtend ((A.realization L).integralIso.hom ≫ (A.realization L).inclusion)).map
          g.hom ≫ eqToHom ((A.realization L).objects K').symm := by
  have H := (A.realization L).fractions K K' g 0
  simp only [pow_zero, inv_one, map_one, one_smul] at H
  exact H

attribute [local semireducible] sfRationalConstructibleLocalization

/-- The target objects of the explicit ordinary arrow and of the closure comparison agree. -/
private theorem raw_target_eq (A : FiniteCondensedData l X) {E L : Index l (PadicAlgCl l)}
    (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    (pbcDerivedExtend ((A.realization L).integralIso.hom ≫ (A.realization L).inclusion)).obj
        ((GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X E L h ⋙
          (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) L) X).ι ⋙
            integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) L)).obj K) =
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h ⋙
          finiteFunctor l X A.toCore L).obj
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X).obj K) :=
  (congrArg (fun Z : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) L) X ↦
      (pbcDerivedExtend ((A.realization L).integralIso.hom ≫ (A.realization L).inclusion)).obj
        ((integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) L)).obj Z.obj))
      (finiteCondensedStageIntegralObject l X E L h K).symm).trans
    (raw_source_eq l X A L
      (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)).obj)


/-- The explicit raw scalar transport agrees with the inverse closure scalar comparison. -/
private theorem raw_core (A : FiniteCondensedData l X) {E L : Index l (PadicAlgCl l)}
    (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    (coefficientExtensionSquare X (pbcCompletedScalarMap l (PadicAlgCl l) X h)
        ((A.realization L).integralIso.hom ≫ (A.realization L).inclusion)
        ((A.realization E).integralIso.hom ≫ (A.realization E).inclusion)
        (A.scalar.coefficient h).coefficient (A.scalar.completed_square h)).inv.app
        ((integralDetailedTransport X l (Coefficient.{u} l (PadicAlgCl l) E)).obj K.obj) ≫
      (pbcDerivedExtend ((A.realization L).integralIso.hom ≫ (A.realization L).inclusion)).map
        ((A.raw.integral.comparison h).hom.app K) ≍
    (A.scalar.theta h).inv.app ((A.raw.family.Φ E).obj
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)) ≫
      (A.realization L).J.map ((A.raw.family.β h).hom.app
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X).obj
          K)) := by
  have hobj := Functor.congr_obj (finiteRawStageFormula l X A E) K
  have hobjL := (Functor.congr_obj (finiteRawStageFormula l X A L)
    (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X).obj
        K)).obj).trans
    (congrArg (fun Z ↦ (pbcStageLocalization l (PadicAlgCl l) X L).obj
      ((A.stage L).integral.functor.obj Z)) (finiteCondensedStageIntegralObject l X E L h K))
  refine HEq.trans ?_ (heq_comp (f := (A.scalar.theta h).inv.app
      ((pbcStageLocalization l (PadicAlgCl l) X E).obj ((A.stage E).integral.functor.obj K)))
    ?_ ?_ ?_ ?_ (map_heq_of_eq (A.realization L).J _ _ ?_ hobjL.symm (raw_beta l X A h K).symm))
  rotate_left
  · exact congrArg ((A.realization E).J ⋙
      pbcDerivedExtend (A.scalar.coefficient h).coefficient).obj hobj.symm
  · exact congrArg ((pbcScalarSystem l (PadicAlgCl l) X Fact.out Fact.out).T h ⋙
      (A.realization L).J).obj hobj.symm
  · exact congrArg (A.realization L).J.obj hobjL.symm
  · exact congr_arg_heq (fun Y ↦ (A.scalar.theta h).inv.app Y) hobj.symm
  · exact congrArg ((pbcScalarSystem l (PadicAlgCl l) X Fact.out Fact.out).T h).obj hobj.symm
  refine heq_comp_map_comp (A.realization L).J _ _ _ _ (theta_inv_comp l X A h _) _
    (realization_map_stage l X A L _) _ ?_
  refine HEq.trans (heq_of_eq (inv_app_comp_congr (coefficientExtensionSquare_eq X _ _ _ _ _ _
    (A.scalar.completed_square h) rfl) _ _)) ?_
  have hE := Functor.congr_obj (A.stage E).integral_identity K
  have hL := Functor.congr_obj (A.stage L).integral_identity
    ((GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X E L h).obj K)
  refine trans_symm_inv_heq _ _ hE _ _ ?_ ?_ _
    ⟨_, eqToHom_map (pbcDerivedExtend (A.scalar.coefficient h).coefficient) _⟩ _ _ _ ⟨_, rfl⟩
  · exact congrArg (pbcDerivedExtend ((A.realization L).integralIso.hom ≫
      (A.realization L).inclusion)).obj hL
  · exact map_heq_of_eq (pbcDerivedExtend ((A.realization L).integralIso.hom ≫
      (A.realization L).inclusion)) _ _
      (congrArg (pbcDerivedExtend (pbcCompletedScalarMap l (PadicAlgCl l) X h)).obj hE) hL
      (A.raw.integral.restriction (E := E) (L := L) h K)

/-- Raw scalar change commutes with continuous integral realization. -/
theorem finiteOrdinaryRawIntegralModel_transition
    (A : FiniteCondensedData l X)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    let B :=
      (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
        ((sfRationalConstructibleLocalization l
          (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)).obj
    integralTensorSquare
      ((closureComparison l X A.toCore A.scalar A.closure h).inv.app
        ((sfRationalConstructibleLocalization l
          (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))
      ((finiteOrdinaryRawIntegralModel l X A E).app K)
      ((finiteOrdinaryRawIntegralModel l X A L).app B)
      (finiteOrdinaryRawIntegralTransition l X A h K) := by
  intro B
  unfold integralTensorSquare
  refine heq_of_comp_eqToHom _ _ _ _ (finiteOrdinaryRawIntegralModel_app_hom l X A L B)
    (finiteOrdinaryRawIntegralModel_app_hom l X A E K) ?_
  unfold finiteOrdinaryRawIntegralTransition closureComparison scalarComparison
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have hY := raw_source_eq l X A E K
  have hZ := raw_target_eq l X A h K
  refine heq_comp (congrArg (pbcDerivedExtend (A.closure.leg E)).obj hY)
    (congrArg (pbcDerivedExtend (A.scalar.coefficient h).coefficient ⋙
      pbcDerivedExtend (A.closure.leg L)).obj hY)
    (congrArg (pbcDerivedExtend (A.closure.leg L)).obj hZ) ?_
    (map_heq_of_eq _ _ _ (congrArg (pbcDerivedExtend (A.scalar.coefficient h).coefficient).obj hY)
      hZ ?_)
  · rw [hY]
  · exact (raw_core l X A h K).trans (by with_unfolding_all exact HEq.rfl)

end WeilConjectures.LocallyFiniteAdicRealization
