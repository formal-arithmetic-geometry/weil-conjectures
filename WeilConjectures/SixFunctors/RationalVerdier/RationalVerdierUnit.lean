/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCocycles
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationNaturality
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationNaturalIso

/-! # Identity coefficient extension for normalized rational Verdier comparisons

Source: blueprint thm-coef-rational-verdier, proof
(blueprint: lem-coef-rational-verdier-unit). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

attribute [local irreducible] CategoryTheory.derivedInternalHomOfUniverses
  CategoryTheory.homComplexFunctor WeilConjectures.IntegralHom.totalTensor
  WeilConjectures.IntegralHom.homModelMap WeilConjectures.IntegralHom.projection
  WeilConjectures.IntegralHom.evaluate

namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem inverse_square {C : Type*} [Category* C]
    {A B A' B' : C} (e : A ≅ B) (e' : A' ≅ B')
    (f : A ⟶ A') (g : B ⟶ B') (h : f ≫ e'.hom = e.hom ≫ g) :
    g ≫ e'.inv = e.inv ≫ f := by
  apply e.eq_inv_comp.mpr
  rw [← Category.assoc, ← h, Category.assoc, e'.hom_inv_id, Category.comp_id]

private theorem paste_square {C : Type*} [Category* C]
    {A B C' D E F : C} {f : A ⟶ B} {a : A ⟶ C'} {b : B ⟶ D}
    {g : C' ⟶ D} {c : C' ⟶ E} {d : D ⟶ F} {h : E ⟶ F}
    (ha : f ≫ b = a ≫ g) (hb : g ≫ d = c ≫ h) :
    f ≫ (b ≫ d) = (a ≫ c) ≫ h := by
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

private theorem contra_map_heq {C C' : Type*} [Category* C] [Category* C']
    (F : Cᵒᵖ ⥤ C') {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (hf : HEq f g) : HEq (F.map f.op) (F.map g.op) := by
  cases hx
  cases hy
  exact heq_of_eq (congrArg (fun f ↦ F.map f.op) (eq_of_heq hf))

private theorem app_heq {C C' : Type*} [Category* C] [Category* C']
    {F G : C ⥤ C'} (a : NatTrans F G) {X Y : C} (h : X = Y) :
    HEq (a.app X) (a.app Y) := by
  cases h
  rfl

private theorem unit_factor
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    (IntegralFiniteExtension.unit l E X K hK).hom =
      (IntegralFiniteExtension.completion l E E (AlgHom.id (Padic l) E) X K hK).inv ≫
        ((eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
          (PurCompactSupport.completedMap_identity l E X))) ≪≫
            PurCompactSupport.tensorIdentity
              (completedIntegralCommRingSheafUnrestricted l E X)).hom.app K := by
  -- Use the component law without normalizing the concrete derived functors.
  have h := NatIso.trans_app
    (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
      (PurCompactSupport.completedMap_identity l E X)))
    (PurCompactSupport.tensorIdentity (completedIntegralCommRingSheafUnrestricted l E X)) K
  have h' := congrArg (fun i ↦
    (IntegralFiniteExtension.completion l E E (AlgHom.id (Padic l) E) X K hK).inv ≫ i.hom) h
  exact h'.symm

private theorem unit_natural
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K M : sfIntegralConstructibleCategory l E X) (f : K ⟶ M) :
    (integralScalar l X E E (AlgHom.id (Padic l) E)).map f ≫
        ObjectProperty.homMk
          (X := (integralScalar l X E E (AlgHom.id (Padic l) E)).obj M) (Y := M)
          (IntegralFiniteExtension.unit l E X M.obj M.property.1).hom =
      ObjectProperty.homMk
          (X := (integralScalar l X E E (AlgHom.id (Padic l) E)).obj K) (Y := K)
          (IntegralFiniteExtension.unit l E X K.obj K.property.1).hom ≫ f := by
  apply ObjectProperty.hom_ext
  let c := completedScalarComparison l E E (AlgHom.id (Padic l) E) X
  let v := eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
    (PurCompactSupport.completedMap_identity l E X)) ≪≫
      PurCompactSupport.tensorIdentity (completedIntegralCommRingSheafUnrestricted l E X)
  have hn := c.naturality f.hom
  have hv :
      (pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X)).map f.hom ≫
          v.hom.app M.obj = v.hom.app K.obj ≫ f.hom := v.hom.naturality f.hom
  have hc := inverse_square
    (IntegralFiniteExtension.completion l E E (AlgHom.id (Padic l) E) X K.obj K.property.1)
    (IntegralFiniteExtension.completion l E E (AlgHom.id (Padic l) E) X M.obj M.property.1)
    ((pbcDerivedExtend (completedCoefficientMap l E E (AlgHom.id (Padic l) E) X)).map f.hom)
    ((integralScalarExtensionOfUniverses l E E (AlgHom.id (Padic l) E) X).map f.hom) hn
  have hp := paste_square hc hv
  have hp' :
      (integralScalarExtensionOfUniverses l E E (AlgHom.id (Padic l) E) X).map f.hom ≫
          (IntegralFiniteExtension.unit l E X M.obj M.property.1).hom =
        (IntegralFiniteExtension.unit l E X K.obj K.property.1).hom ≫ f.hom := by
    rw [unit_factor, unit_factor]
    exact hp
  exact hp'

private def integral_unit_iso
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    integralScalar l X E E (AlgHom.id (Padic l) E) ≅
      𝟭 (sfIntegralConstructibleCategory l E X) :=
  NatIso.ofComponents (fun K ↦
    { hom := ObjectProperty.homMk
        (IntegralFiniteExtension.unit l E X K.obj K.property.1).hom
      inv := ObjectProperty.homMk
        (IntegralFiniteExtension.unit l E X K.obj K.property.1).inv
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        exact (IntegralFiniteExtension.unit l E X K.obj K.property.1).hom_inv_id
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        exact (IntegralFiniteExtension.unit l E X K.obj K.property.1).inv_hom_id })
    (fun f ↦ unit_natural l X E _ _ f)

/-- The specified rational comparison obeys the integral tensor unit equation.
Source: thm-coef-rational-verdier, proof step 7, identity-extension clause;
current blueprint proof, paragraph 3
(blueprint: lem-coef-rational-verdier-unit).

Proof: the integral tensor multiplication unit is a natural isomorphism on
complete inputs. Its localization defines j on the unchanged objects. Its
naturality on a pure tensor is integral naturality times that coefficient;
additivity extends it to all maps, and the integral inverse localizes. This
also gives the displayed normalization. The integral identity-extension
formula says beta is the tensor unit at the integral dual followed by the
dual of the unit at K. It holds for A.ordinary because representative
normalization identifies its evaluation transpose with the canonical one.
Apply localization to this equality. ExtensionProperties identifies its
left side with e.comparison, and A.pure at coefficient one identifies the
dual of the localized unit on the right. A.objects fixes the endpoints.
Every rational object is literally an integral representative, so this
proves the equation for all K. No faithfulness of localization is used;
in particular torsion objects and the empty scheme are included. -/
theorem extension_unit
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (A : Datum D l hl X E wE)
    (e : Extension D l hl X E E (AlgHom.id (Padic l) E) wE wE A A)
    (he : ExtensionProperties D l hl X E E (AlgHom.id (Padic l) E) wE wE A A e) :
    ∃ j : scalar l X E E (AlgHom.id (Padic l) E) ≅ 𝟭 (sfRationalConstructibleCategory l E X),
      (∀ K : sfIntegralConstructibleCategory l E X,
        HEq (j.hom.app ((sfRationalConstructibleLocalization l E X).obj K))
          ((sfRationalConstructibleLocalization l E X).map
            (ObjectProperty.homMk
              (X := (integralScalar l X E E (AlgHom.id (Padic l) E)).obj K) (Y := K)
              (IntegralFiniteExtension.unit l E X K.obj K.property.1).hom))) ∧
      ∀ K : sfRationalConstructibleCategory l E X,
        e.comparison.hom.app (op K) =
          j.hom.app (A.dual.obj (op K)) ≫
            A.dual.map (j.hom.app K).op := by
  let Q := sfRationalConstructibleLocalization l E X
  let T := integralScalar l X E E (AlgHom.id (Padic l) E)
  let F := scalar l X E E (AlgHom.id (Padic l) E)
  have hobj := sfRationalScalarExtension_obj l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E (AlgHom.id (Padic l) E)
  let c : Q ⋙ F ≅ T ⋙ Q := NatIso.ofComponents
    (fun K ↦ eqToIso (hobj (Q.obj K))) (by
      intro K M f
      change F.map (Q.map f) ≫ eqToHom (hobj (Q.obj M)) =
        eqToHom (hobj (Q.obj K)) ≫ Q.map (T.map f)
      have hm := sfRationalScalarExtension_map_tmul l E X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E (AlgHom.id (Padic l) E) K M f 1
      simp only [map_one] at hm
      have hm' : HEq (F.map (Q.map f)) (Q.map (T.map f)) := hm
      exact eq_of_heq ((comp_eqToHom_heq _ _).trans
        (hm'.trans (eqToHom_comp_heq _ _).symm)))
  let d : Q ⋙ F ≅ Q ⋙ 𝟭 _ := c ≪≫
    Functor.isoWhiskerRight (integral_unit_iso l X E) Q
  obtain ⟨j, hj, _⟩ := ScalarLocalization.naturalIso_of_integral
    (Padic.coefficientExtensionIntegers l E) (sfIntegralConstructibleCategory l E X)
    (Padic.coefficientExtensionUniformizer l E) F (𝟭 _) d
  have hj' (K : sfIntegralConstructibleCategory l E X) :
      HEq (j.hom.app (Q.obj K))
        (Q.map (ObjectProperty.homMk (X := T.obj K) (Y := K)
          (IntegralFiniteExtension.unit l E X K.obj K.property.1).hom)) := by
    exact (heq_of_eq (hj K)).trans
      (eqToHom_comp_heq (Q.map ((integral_unit_iso l X E).hom.app K)) (hobj (Q.obj K)))
  refine ⟨j, hj', ?_⟩
  let I := IntegralVerdier.restrictedDual l E X wE.omega.obj A.preserves
  let U := integral_unit_iso l X E
  have hnat := IntegralHom.evaluation_naturality X
    (completedIntegralCommRingSheafUnrestricted l E X) A.ordinary
  have hidentity := (IntegralFiniteExtension.comparison_cocycles
    l E E (AlgHom.id (Padic l) E) X D hl wE wE A.ordinary A.ordinary hnat hnat).1
  have hbeta (K : sfIntegralConstructibleCategory l E X) :
      ObjectProperty.homMk (X := T.obj (I.obj (op K))) (Y := I.obj (op (T.obj K)))
          (IntegralFiniteExtension.beta l E E (AlgHom.id (Padic l) E) X D hl
            wE wE A.ordinary A.ordinary K.obj K.property.1) =
        U.hom.app (I.obj (op K)) ≫ I.map (U.hom.app K).op := by
    apply ObjectProperty.hom_ext
    exact ((IntegralVerdier.dual l E X wE.omega.obj).mapIso
      (IntegralFiniteExtension.unit l E X K.obj K.property.1).op).comp_inv_eq.mp
        (hidentity.2.2 K)
  intro K
  have hK : K = Q.obj K.obj := rfl
  have ht : F.obj K = Q.obj (T.obj K.obj) := hobj K
  have hd : A.dual.obj (op K) = Q.obj (I.obj (op K.obj)) := A.objects K
  have hdt : A.dual.obj (op (F.obj K)) = Q.obj (I.obj (op (T.obj K.obj))) :=
    (congrArg (fun M ↦ A.dual.obj (op M)) ht).trans (A.objects _)
  have hh : HEq (j.hom.app (A.dual.obj (op K)))
      (Q.map (U.hom.app (I.obj (op K.obj)))) :=
    (app_heq j.hom hd).trans (hj' (I.obj (op K.obj)))
  have hp := A.pure (T.obj K.obj) K.obj (U.hom.app K.obj) 1
  have hp' : HEq (A.dual.map (Q.map (U.hom.app K.obj)).op)
      (Q.map (I.map (U.hom.app K.obj).op)) := hp
  have hm : HEq (A.dual.map (j.hom.app K).op)
      (Q.map (I.map (U.hom.app K.obj).op)) :=
    (contra_map_heq A.dual ht hK (hj' K.obj)).trans hp'
  have heq := he.2.1 K.obj
  have hend : F.obj (A.dual.obj (op K)) = Q.obj (T.obj (I.obj (op K.obj))) :=
    (congrArg F.obj hd).trans (hobj _)
  apply eq_of_heq
  exact heq.trans ((heq_of_eq (congrArg Q.map (hbeta K.obj))).trans
    ((heq_of_eq (Q.map_comp _ _)).trans
      (heq_comp hend hd hdt hh hm).symm))

end WeilConjectures.RationalVerdier
