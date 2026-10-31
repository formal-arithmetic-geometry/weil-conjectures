/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonComponent

/-! # Naturality of the integral completed tensor components

Source: BS Remark 6.8.15; HRS Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.AdicQbarRealization.ordinary

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)

attribute [local irreducible] sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear
  ObjectProperty.FullSubcategory.category
  constructibleIntegralTensor

open scoped TensorProduct

private theorem chosen_spec {A : Sort*} {p : A → Prop} (h : ∃! a, p a)
    (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

private abbrev tensor_spec
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :=
  chosen_spec (rationalDerivedTensor_existsUnique l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (rationalDerivedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) rfl

attribute [local irreducible] rationalDerivedTensor

private theorem localization_map_heq
    {A : Type*} [CommRing A] {C : Type*} [Category* C] [Preadditive C] [Linear A C]
    (t : A) {K L : C} (f : K ⟶ L) :
    HEq ((ScalarLocalization.localization A C t).map f)
      ((1 : Localization.Away t) ⊗ₜ[A] f) := HEq.rfl

private theorem integral_tensor_object_naturality
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    {P Q : sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ×
      sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X}
    (f : P ⟶ Q) :
    let q := sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
    (rationalDerivedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).map
        ((q.prod q).map f) ≫ (tensorIntegralObjectIso l X E Q.1 Q.2).hom =
      (tensorIntegralObjectIso l X E P.1 P.2).hom ≫
        q.map ((constructibleIntegralTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).map f) := by
  rcases P with ⟨K, L⟩
  rcases Q with ⟨K', L'⟩
  rcases f with ⟨f, g⟩
  let P := (K, L)
  let Q := (K', L')
  let f := Prod.mkHom f g
  let q := sfRationalConstructibleLocalization l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let T := constructibleIntegralTensor l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let A := (q.prod q) ⋙ rationalDerivedTensor l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let B := T ⋙ q
  have hobj (P) : A.obj P = B.obj P :=
    (tensor_spec l X E).1
      ((q.prod q).obj P)
  have hm : HEq (A.map f) (B.map f) := by
    have hs := ((tensor_spec l X E).2
      (q.obj P.1) (q.obj Q.1) (q.obj P.2) (q.obj Q.2)).choose_spec
    have hb := hs.1
    have pb := hs.2
    change HEq ((rationalDerivedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).map
        (Prod.mkHom (q.map f.1) (q.map f.2))) _
    refine (heq_of_eq (hb (q.map f.1) (q.map f.2))).trans ?_
    have hp := pb f.1 f.2 1 1
    simp only [one_mul] at hp
    exact hp.trans (localization_map_heq
      (Padic.coefficientExtensionUniformizer l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)) (T.map f)).symm
  have he := (conj_eqToHom_iff_heq (A.map f) (B.map f) (hobj P) (hobj Q)).2 hm
  change A.map f ≫ eqToHom (hobj Q) = eqToHom (hobj P) ≫ B.map f
  rw [he]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

attribute [local semireducible] ObjectProperty.FullSubcategory.category constructibleIntegralTensor
attribute [local irreducible] ScalarLocalization.category
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.Stage
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

private def integral_component_iso
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : CompletedTensorFiniteModel l X R closed models E) :
    let q := sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E
    let F := ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor
    let G := rationalDerivedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙ I ⋙ ordinary l X R
    (q.prod q) ⋙ (I.prod I) ⋙ F ≅ (q.prod q) ⋙ G := by
  let q := sfRationalConstructibleLocalization l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let I := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E
  let H := (sfIntegralConstructible l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).ι
  let B := pbcDerivedExtend (coefficientMap l X R E)
  let T := constructibleIntegralTensor l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let r : q ⋙ I ⋙ ordinary l X R ≅ H ⋙ B := by
    unfold ordinary
    exact R.integral E
  let c : (H.prod H) ⋙ N.completion.tensor ≅ T ⋙ H :=
    NatIso.ofComponents (fun P ↦ tensorQuotientIso l X E N.completion P.1 P.2) (by
      intro P Q f
      exact N.completion.comparison.naturality (Prod.mkHom f.1.hom f.2.hom))
  let d : (q.prod q) ⋙ rationalDerivedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ≅ T ⋙ q :=
    NatIso.ofComponents (fun P ↦ tensorIntegralObjectIso l X E P.1 P.2)
      (fun f ↦ integral_tensor_object_naturality l X E f)
  exact Functor.isoWhiskerRight (NatIso.prod r r) closed.tensor ≪≫
    Functor.isoWhiskerLeft (H.prod H) N.ordinary.symm ≪≫
    Functor.isoWhiskerRight c B ≪≫
    Functor.isoWhiskerLeft T r.symm ≪≫
    Functor.isoWhiskerRight d.symm (I ⋙ ordinary l X R)

attribute [local irreducible] integral_component_iso

private theorem integral_component_iso_app
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : CompletedTensorFiniteModel l X R closed models E)
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    (integral_component_iso l X R closed models E N).hom.app (K, L) =
      (completedTensorIntegralComponent l X R closed models E N K L).hom := by
  unfold integral_component_iso completedTensorIntegralComponent
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, NatIso.ofComponents_inv_app,
    Functor.comp_obj, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
    NatIso.prod, NatTrans.prod, Iso.prod]
  dsimp only [Iso.trans, Iso.symm, Functor.mapIso, NatIso.ofComponents,
    Functor.comp, Iso.app, id_eq]
  unfold ordinary
  dsimp only [Functor.prod, ObjectProperty.ι, inducedFunctor, id]
  rfl

/-- The explicit integral completed tensor components form a natural isomorphism.
Source: BS Definition 3.4.10 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-integral-naturality).

Proof: paste the integral realization isomorphism in the two inputs, the inverse
ordinary tensor comparison, the natural quotient-completion map, the inverse
integral realization at the tensor output, and the inverse integral-to-rational
object identification. The last identification is natural because the rational
tensor's prescribed bilinear action on pure localized integral arrows agrees
with localized integral tensor: evaluate its scalar formula at 1 and 1 and use
the conjugation equation for equality-induced isomorphisms. Expanding the pasted
isomorphism gives exactly completedTensorIntegralComponent. No nonzero or
nonempty hypotheses enter this argument. -/
theorem completedTensorIntegralComponent_natural_iso
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : CompletedTensorFiniteModel l X R closed models E) :
    let q := sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E
    let F := ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor
    let G := rationalDerivedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙ I ⋙ ordinary l X R
    ∃ e : (q.prod q) ⋙ (I.prod I) ⋙ F ≅ (q.prod q) ⋙ G,
      ∀ P, e.hom.app P =
        (completedTensorIntegralComponent l X R closed models E N P.1 P.2).hom := by
  exact ⟨integral_component_iso l X R closed models E N,
    fun P ↦ integral_component_iso_app l X R closed models E N P.1 P.2⟩

end WeilConjectures.AdicQbarRealization
