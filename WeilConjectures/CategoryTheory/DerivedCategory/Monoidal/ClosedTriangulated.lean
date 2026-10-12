/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed

/-!
# The derived internal hom is triangulated in its first variable

Let `C` be a monoidal closed Grothendieck abelian category as in
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`, so that `D(C)` is monoidal
closed for the derived tensor product, with internal hom `RHom(K, M) = (ihom K).obj M`. This file
shows that the internal hom is exact in its first variable: for a distinguished triangle
`K' ⟶ K ⟶ K'' ⟶ K'[1]` of `D(C)` and any `M`, there is a distinguished triangle

`RHom(K'', M) ⟶ RHom(K, M) ⟶ RHom(K', M) ⟶ RHom(K'', M)[1]`

whose first two maps are induced by the given ones
(`DerivedCategory.exists_distinguished_ihom_pre`).

## Strategy

The derived internal hom is not constructed as a bifunctor by hand, so the statement is proved
on a model. Write `M = Q I` for a K-injective complex `I`.

* On cochain complexes, precomposition `iHom(P', I) ⟶ iHom(P, I)` with a morphism `P ⟶ P'`
  (`CochainComplex.internalHomPre`) is given in each degree by the maps
  `[P'ᵖ, Iᵠ] ⟶ [Pᵖ, Iᵠ]` on the factors of the products defining the internal hom complexes.
  Hence it carries a degreewise split short exact sequence of complexes to one
  (`CochainComplex.internalHomShortComplexSplitting`).
* The map `Q iHom(P, I) ⟶ RHom(Q P, Q I)` adjoint to the evaluation
  (`DerivedCategory.qhInternalHomToIhom`) is natural in `P` and is an isomorphism, `I` being
  K-injective: it is the unit of the right derived functor of `iHom(P, -)`, followed by the
  identification of the derived adjunction with the closed structure of `D(C)`.
* Every distinguished triangle of `D(C)` is isomorphic to the image of the triangle attached to
  a degreewise split short exact sequence of complexes.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Pretriangulated
open MonoidalClosed hiding assoc id_comp comp_id

universe w v u

namespace CochainComplex

section Pre

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C] [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- Precomposition with a sum is the sum of the precompositions. -/
lemma _root_.CategoryTheory.MonoidalClosed.pre_add_app {A B : C} (f g : B ⟶ A) (X : C) :
    (pre (f + g)).app X = (pre f).app X + (pre g).app X :=
  uncurry_injective (by
    rw [uncurry_pre, uncurry_add, uncurry_pre, uncurry_pre, MonoidalPreadditive.add_whiskerRight,
      Preadditive.add_comp])

/-- The morphism `f ▷ K` on the summand `P.X p ⊗ K.X q` of `(P ⊗ K).X r`. -/
@[reassoc]
lemma ιTensorObj_whiskerRight_f {P P' : CochainComplex C ℤ} (f : P ⟶ P')
    (K : CochainComplex C ℤ) (p q r : ℤ) (h : p + q = r) :
    HomologicalComplex.ιTensorObj P K p q r h ≫ (f ▷ K).f r =
      f.f p ▷ K.X q ≫ HomologicalComplex.ιTensorObj P' K p q r h := by
  have : (f ▷ K).f r = (HomologicalComplex.tensorHom f (𝟙 K)).f r := rfl
  rw [this]
  simp

variable {P P' P'' : CochainComplex C ℤ} (f : P ⟶ P') (g : P' ⟶ P'') (Y : CochainComplex C ℤ)

/-- Precomposition `iHom(P', Y) ⟶ iHom(P, Y)` of internal hom complexes with a morphism
`f : P ⟶ P'` of cochain complexes: the map corresponding under the tensor-hom adjunction to
`P ⊗ iHom(P', Y) ⟶ P' ⊗ iHom(P', Y) ⟶ Y`. -/
noncomputable def internalHomPre : internalHomObj P' Y ⟶ internalHomObj P Y :=
  internalHomEquiv P Y _ (f ▷ internalHomObj P' Y ≫ (tensorHomAdjunction P').counit.app Y)

/-- The evaluation is dinatural: `P ⊗ iHom(P', Y)` maps to `Y` in the same way through
`P ⊗ iHom(P, Y)` and through `P' ⊗ iHom(P', Y)`. -/
@[reassoc]
lemma whiskerLeft_internalHomPre_comp_counit :
    P ◁ internalHomPre f Y ≫ (tensorHomAdjunction P).counit.app Y =
      f ▷ internalHomObj P' Y ≫ (tensorHomAdjunction P').counit.app Y := by
  rw [internalHomPre, ← tensorHomAdjunction_homEquiv]
  exact ((tensorHomAdjunction P).homEquiv_counit _ _ _).symm.trans (Equiv.symm_apply_apply _ _)

/-- The components of `internalHomPre f Y`, where `[A, B]` denotes `(ihom A).obj B`: on the
factor `[P'.X p, Y.X q]` it is precomposition `[P'.X p, Y.X q] ⟶ [P.X p, Y.X q]` with `f.f p`. -/
@[reassoc (attr := simp)]
lemma internalHomPre_f_π (n p q : ℤ) (h : p + n = q) :
    (internalHomPre f Y).f n ≫ internalHomπ P Y n p q h =
      internalHomπ P' Y n p q h ≫ (pre (f.f p)).app (Y.X q) := by
  rw [internalHomPre, internalHomEquiv_f_π, HomologicalComplex.comp_f,
    ιTensorObj_whiskerRight_f_assoc, tensorHomAdjunction_counit_app]
  rw [ιTensorObj_internalHomEquiv_symm_f, HomologicalComplex.id_f, id_comp, ← curry_pre_app,
    curry_uncurry]

@[simp]
lemma internalHomPre_id : internalHomPre (𝟙 P) Y = 𝟙 _ := by
  ext n p q h
  simp

@[reassoc]
lemma internalHomPre_comp : internalHomPre (f ≫ g) Y = internalHomPre g Y ≫ internalHomPre f Y := by
  ext n p q h
  simp

@[simp]
lemma internalHomPre_zero : internalHomPre (0 : P ⟶ P') Y = 0 := by
  ext n p q h
  simp [pre_zero_app]

/-- Precomposition carries a short complex `S` of cochain complexes to the short complex
`iHom(S.X₃, Y) ⟶ iHom(S.X₂, Y) ⟶ iHom(S.X₁, Y)`. -/
@[simps]
noncomputable def internalHomShortComplex (S : ShortComplex (CochainComplex C ℤ)) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (internalHomPre S.g Y) (internalHomPre S.f Y) (by
    rw [← internalHomPre_comp, S.zero, internalHomPre_zero])

omit [HasZeroObject C] [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄] in
@[reassoc (attr := simp)]
lemma lift_internalHomπ {Z : C} {Q : CochainComplex C ℤ} {n : ℤ}
    (φ : ∀ T : HomComplex.Triplet n, Z ⟶ (ihom (Q.X T.p)).obj (Y.X T.q)) (p q : ℤ)
    (h : p + n = q) :
    Pi.lift φ ≫ internalHomπ Q Y n p q h = φ ⟨p, q, h⟩ :=
  Pi.lift_π _ _

/-- A degreewise splitting of `S` induces a degreewise splitting of
`iHom(S.X₃, Y) ⟶ iHom(S.X₂, Y) ⟶ iHom(S.X₁, Y)`. -/
@[simps]
noncomputable def internalHomShortComplexSplitting (S : ShortComplex (CochainComplex C ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval C _ n)).Splitting) (n : ℤ) :
    ((internalHomShortComplex Y S).map (HomologicalComplex.eval C _ n)).Splitting where
  r := Pi.lift fun T ↦ internalHomπ S.X₂ Y n T.p T.q T.hpq ≫ (pre (σ T.p).s).app (Y.X T.q)
  s := Pi.lift fun T ↦ internalHomπ S.X₁ Y n T.p T.q T.hpq ≫ (pre (σ T.p).r).app (Y.X T.q)
  f_r := by
    refine internalHomObj_hom_ext fun p q h ↦ ?_
    have : (σ p).s ≫ S.g.f p = 𝟙 _ := (σ p).s_g
    dsimp
    rw [assoc, lift_internalHomπ, internalHomPre_f_π_assoc, ← NatTrans.comp_app, ← pre_map,
      this]
    simp
  s_g := by
    refine internalHomObj_hom_ext fun p q h ↦ ?_
    have : S.f.f p ≫ (σ p).r = 𝟙 _ := (σ p).f_r
    dsimp
    rw [assoc, internalHomPre_f_π, lift_internalHomπ_assoc, assoc, ← NatTrans.comp_app,
      ← pre_map, this]
    simp
  id := by
    refine internalHomObj_hom_ext fun p q h ↦ ?_
    have : (σ p).r ≫ S.f.f p + S.g.f p ≫ (σ p).s = 𝟙 _ := (σ p).id
    dsimp
    rw [Preadditive.add_comp, assoc, assoc, internalHomPre_f_π, lift_internalHomπ_assoc, assoc,
      lift_internalHomπ, internalHomPre_f_π_assoc, ← NatTrans.comp_app, ← NatTrans.comp_app,
      ← pre_map, ← pre_map, ← Preadditive.comp_add, ← pre_add_app, add_comm, this]
    simp

end Pre

end CochainComplex

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [(HomotopyCategory.quasiIso C
    (ComplexShape.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure]

open HomotopyCategory in
/-- The comparison `Q iHom(P, I) ⟶ RHom(Q P, Q I)` between the image in `D(C)` of the internal
hom complex and the derived internal hom: the map adjoint to
`Q P ⊗ᴸ Q iHom(P, I) ⟶ Q (P ⊗ iHom(P, I)) ⟶ Q I`, the last map being the evaluation. -/
noncomputable def qhInternalHomToIhom (P I : CochainComplex C ℤ) :
    Qh.obj ((quotient C (ComplexShape.up ℤ)).obj (CochainComplex.internalHomObj P I)) ⟶
      (ihom (Qh.obj ((quotient C (ComplexShape.up ℤ)).obj P))).obj
        (Qh.obj ((quotient C (ComplexShape.up ℤ)).obj I)) :=
  curry (Functor.LaxMonoidal.μ Qh _ _ ≫
    Qh.map ((quotient C (ComplexShape.up ℤ)).map
      ((CochainComplex.tensorHomAdjunction P).counit.app I)))

open HomotopyCategory in
/-- `qhInternalHomToIhom P I` is natural in `P`. -/
lemma qhInternalHomToIhom_naturality {P P' : CochainComplex C ℤ} (f : P ⟶ P')
    (I : CochainComplex C ℤ) :
    Qh.map ((quotient C (ComplexShape.up ℤ)).map (CochainComplex.internalHomPre f I)) ≫
        qhInternalHomToIhom P I =
      qhInternalHomToIhom P' I ≫
        (pre (Qh.map ((quotient C (ComplexShape.up ℤ)).map f))).app _ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app, qhInternalHomToIhom, qhInternalHomToIhom,
    uncurry_curry, uncurry_curry, Functor.LaxMonoidal.μ_natural_right_assoc,
    Functor.LaxMonoidal.μ_natural_left_assoc, ← Qh.map_comp, ← Qh.map_comp]
  congr 1
  have := (quotient C (ComplexShape.up ℤ)).congr_map
    (CochainComplex.whiskerLeft_internalHomPre_comp_counit f I)
  simp only [Functor.map_comp] at this
  exact this

open HomotopyCategory in
/-- `qhInternalHomToIhom P I` is an isomorphism when `I` is K-injective. -/
instance isIso_qhInternalHomToIhom (P I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso (qhInternalHomToIhom P I) := by
  let P' := (quotient C (ComplexShape.up ℤ)).obj P
  let e := (tensorHomAdjunctionQhObj P').rightAdjointUniq (ihom.adjunction (Qh.obj P'))
  have := isLeftDerivedFunctor_tensorLeft_comp_internalHomQhObj P'
  have := isRightDerivedFunctor_internalHomQhObj_comp_tensorLeft P'
  have h : qhInternalHomToIhom P I =
      (internalHomQhObjUnit P').app ((quotient C (ComplexShape.up ℤ)).obj I) ≫
        e.hom.app _ := by
    apply uncurry_injective
    rw [qhInternalHomToIhom, uncurry_curry, uncurry_eq, MonoidalCategory.whiskerLeft_comp,
      assoc]
    erw [Adjunction.rightAdjointUniq_hom_app_counit]
    dsimp only [tensorHomAdjunctionQhObj]
    erw [Adjunction.derived_counit, Adjunction.derivedε_fac_app]
    erw [tensorHomAdjunction_counit_app]
    rfl
  rw [h]
  infer_instance

open HomotopyCategory in
/-- The first-variable exactness of the derived internal hom on a model: for a degreewise split
short exact sequence `S` of cochain complexes and a K-injective complex `I`, the images under
`RHom(-, Q I)` of the maps `Q S.f` and `Q S.g` extend to a distinguished triangle
`RHom(Q S.X₃, Q I) ⟶ RHom(Q S.X₂, Q I) ⟶ RHom(Q S.X₁, Q I) ⟶ RHom(Q S.X₃, Q I)[1]`. It is the
image of the distinguished triangle attached to the degreewise split short exact sequence
`iHom(S.X₃, I) ⟶ iHom(S.X₂, I) ⟶ iHom(S.X₁, I)` under the isomorphisms
`qhInternalHomToIhom`. -/
lemma exists_distinguished_ihom_pre_of_degreewiseSplit
    (S : ShortComplex (CochainComplex C ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval C _ n)).Splitting)
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    ∃ h, Triangle.mk
      ((pre (Qh.map ((quotient C (ComplexShape.up ℤ)).map S.g))).app
        (Qh.obj ((quotient C (ComplexShape.up ℤ)).obj I)))
      ((pre (Qh.map ((quotient C (ComplexShape.up ℤ)).map S.f))).app
        (Qh.obj ((quotient C (ComplexShape.up ℤ)).obj I))) h ∈ distTriang _ := by
  let S' := CochainComplex.internalHomShortComplex I S
  let σ' := CochainComplex.internalHomShortComplexSplitting I S σ
  have hT' : Qh.mapTriangle.obj (CochainComplex.trianglehOfDegreewiseSplit S' σ') ∈
      distTriang _ :=
    Qh.map_distinguished _
      ((distinguished_iff_iso_trianglehOfDegreewiseSplit _).2 ⟨S', σ', ⟨Iso.refl _⟩⟩)
  have H₁ : Qh.map ((quotient C (ComplexShape.up ℤ)).map S'.f) ≫ qhInternalHomToIhom S.X₂ I =
      qhInternalHomToIhom S.X₃ I ≫
        (pre (Qh.map ((quotient C (ComplexShape.up ℤ)).map S.g))).app _ :=
    qhInternalHomToIhom_naturality S.g I
  have H₂ : Qh.map ((quotient C (ComplexShape.up ℤ)).map S'.g) ≫ qhInternalHomToIhom S.X₁ I =
      qhInternalHomToIhom S.X₂ I ≫
        (pre (Qh.map ((quotient C (ComplexShape.up ℤ)).map S.f))).app _ :=
    qhInternalHomToIhom_naturality S.f I
  refine ⟨inv (qhInternalHomToIhom S.X₁ I) ≫
    (Qh.mapTriangle.obj (CochainComplex.trianglehOfDegreewiseSplit S' σ')).mor₃ ≫
      (qhInternalHomToIhom S.X₃ I)⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT' _
    (Triangle.isoMk _ _ (asIso (qhInternalHomToIhom S.X₃ I)).symm
      (asIso (qhInternalHomToIhom S.X₂ I)).symm (asIso (qhInternalHomToIhom S.X₁ I)).symm
      ((IsIso.comp_inv_eq _).2 ((IsIso.eq_inv_comp _).2 (by rw [← assoc]; exact H₁.symm)))
      ((IsIso.comp_inv_eq _).2 ((IsIso.eq_inv_comp _).2 (by rw [← assoc]; exact H₂.symm)))
      ?_)⟩
  simp only [Triangle.mk_mor₃, Iso.symm_hom, asIso_inv, assoc, ← Functor.map_comp,
    IsIso.hom_inv_id, Functor.map_id, comp_id]
  rfl

/-- The first-variable exactness of the internal hom is invariant under isomorphisms of
triangles and of the second variable. -/
lemma exists_distinguished_ihom_pre_of_iso {T T' : Triangle (DerivedCategory C)} (e : T ≅ T')
    {M M' : DerivedCategory C} (eM : M ≅ M')
    (h' : ∃ h, Triangle.mk ((pre T'.mor₂).app M') ((pre T'.mor₁).app M') h ∈ distTriang _) :
    ∃ h, Triangle.mk ((pre T.mor₂).app M) ((pre T.mor₁).app M) h ∈ distTriang _ := by
  obtain ⟨h', hh'⟩ := h'
  let φ : ∀ {X X' : DerivedCategory C} (_ : X ≅ X'), (ihom X).obj M ≅ (ihom X').obj M' :=
    fun e' ↦ (MonoidalClosed.internalHom.mapIso e'.symm.op).app M ≪≫ (ihom _).mapIso eM
  have hφ : ∀ {X X' : DerivedCategory C} (e' : X ≅ X'),
      (φ e').hom = (pre e'.inv).app M ≫ (ihom X').map eM.hom := fun _ ↦ rfl
  let e₁ : T.obj₁ ≅ T'.obj₁ := Triangle.π₁.mapIso e
  let e₂ : T.obj₂ ≅ T'.obj₂ := Triangle.π₂.mapIso e
  let e₃ : T.obj₃ ≅ T'.obj₃ := Triangle.π₃.mapIso e
  have c₁ : T'.mor₁ ≫ e₂.inv = e₁.inv ≫ T.mor₁ := e.inv.comm₁
  have c₂ : T'.mor₂ ≫ e₃.inv = e₂.inv ≫ T.mor₂ := e.inv.comm₂
  refine ⟨(φ e₁).hom ≫ h' ≫ (φ e₃).inv⟦(1 : ℤ)⟧',
    isomorphic_distinguished _ hh' _ (Triangle.isoMk _ _ (φ e₃) (φ e₂) (φ e₁) ?_ ?_ ?_)⟩
  · change (pre T.mor₂).app M ≫ (φ e₂).hom = (φ e₃).hom ≫ (pre T'.mor₂).app M'
    rw [hφ, hφ, assoc, NatTrans.naturality, ← NatTrans.comp_app_assoc,
      ← NatTrans.comp_app_assoc, ← pre_map, ← pre_map, c₂]
  · change (pre T.mor₁).app M ≫ (φ e₁).hom = (φ e₂).hom ≫ (pre T'.mor₁).app M'
    rw [hφ, hφ, assoc, NatTrans.naturality, ← NatTrans.comp_app_assoc,
      ← NatTrans.comp_app_assoc, ← pre_map, ← pre_map, c₁]
  · change ((φ e₁).hom ≫ h' ≫ (φ e₃).inv⟦(1 : ℤ)⟧') ≫ (φ e₃).hom⟦(1 : ℤ)⟧' = (φ e₁).hom ≫ h'
    simp only [assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, comp_id]

/-- Blueprint `lem-sf-hom-triangulated`: Exactness of the internal Hom in each variable, first
variable.

For a distinguished triangle `K' ⟶ K ⟶ K'' ⟶ K'[1]` of `D(C)` and any `M`, the maps
`RHom(K'', M) ⟶ RHom(K, M) ⟶ RHom(K', M)` induced by the first two maps extend to a
distinguished triangle `RHom(K'', M) ⟶ RHom(K, M) ⟶ RHom(K', M) ⟶ RHom(K'', M)[1]`, the
internal hom being that of the closed structure of `D(C)`.

As in the blueprint, `M` is represented by a K-injective complex `I` and the internal hom by the
internal hom complex into `I` (`DerivedCategory.qhInternalHomToIhom`), which carries degreewise
split short exact sequences of complexes to degreewise split short exact sequences. -/
theorem exists_distinguished_ihom_pre (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (M : DerivedCategory C) :
    ∃ h, Triangle.mk ((pre T.mor₂).app M) ((pre T.mor₁).app M) h ∈ distTriang _ := by
  obtain ⟨T', e, hT'⟩ := hT
  rw [HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit] at hT'
  obtain ⟨S, σ, ⟨e'⟩⟩ := hT'
  obtain ⟨X, ⟨eM⟩⟩ := Functor.EssSurj.mem_essImage (F := HomotopyCategory.KInjectives.Qh) M
  obtain ⟨I, _, rfl⟩ := X.mk_surjective
  exact exists_distinguished_ihom_pre_of_iso (e ≪≫ Qh.mapTriangle.mapIso e') eM.symm
    (exists_distinguished_ihom_pre_of_degreewiseSplit S σ I)

end DerivedCategory
