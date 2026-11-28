/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationPureTensor
import all WeilConjectures.PoincareDuality.Pod.Integral.PodIntegralHomComparisonNaturality
public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroCycleFormal

/-! # Rational inverse transposition under scalar extension of coefficients

For a finite extension `E → L` of coefficient fields, scalar extension carries inverse
transposition of the normalized rational closed datum over `E`, conjugated by the tensor and
internal-Hom scalar comparisons, to inverse transposition over `L`.

## Main statements

* `localizedInverseTranspose_scalar`: the statement for an arbitrary functor of scalar
  localizations acting on pure tensors through an integral functor.
* `completedTranspose_scalar`: the integral statement for abstract closed structures, given
  compatibility of the completion units with the tensor scalar comparisons.
* `podCompletedTensorUnit_scalar`: that compatibility for the ordinary-to-completed tensor
  unit and ordinary scalar extension.
* `podIntegralClosed_scalar_symm`: the integral statement.
* `podRationalClosed_scalar_symm`: the statement for rational constructible complexes.

## Implementation details

Integrally, the completion maps of scalar extension are invertible on complete objects, and
the Hom scalar comparison is the transpose of scalar-extended evaluation, so naturality of
transposition reduces the statement to the completion-unit compatibility. Rationally, all maps
are additive in the localized arrow, so tensor induction reduces the identity to pure
tensors, where it is the integral identity tensored with a scalar.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

section Localization
open TensorProduct
variable {R : Type*} [CommRing R] {A : Type*} [Category* A] [Preadditive A] [Linear R A]
  {R' : Type*} [CommRing R'] {A' : Type*} [Category* A'] [Preadditive A'] [Linear R' A']

-- Induction on localized arrows into an object with a recorded integral representative.
private theorem localizedHom_induction' (p : R)
    (M N : ScalarLocalization R A p) (N₀ : A) (hN : N = ⟨N₀⟩)
    (Q : (M ⟶ N) → Prop) (q : M ⟶ N)
    (ht : ∀ (a : Localization.Away p) (f : M.obj ⟶ N₀) (q : M ⟶ N),
      HEq q (a ⊗ₜ[R] f) → Q q)
    (ha : ∀ q q', Q q → Q q' → Q (q + q')) : Q q := by
  cases hN
  induction q using TensorProduct.inductionOn with
  | tmul a f => exact ht a f _ HEq.rfl
  | add q q' hq hq' => exact ha q q' hq hq'

-- A functor acting on pure tensors through an integral functor, on recorded representatives.
private theorem map_heq_tmul (p : R) (p' : R') (c : Localization.Away p → Localization.Away p')
    (F₀ : A ⥤ A') (F : ScalarLocalization R A p ⥤ ScalarLocalization R' A' p')
    (hFm : ∀ (K M : A) (f : K ⟶ M) (a : Localization.Away p),
      HEq (F.map (a ⊗ₜ[R] f : (⟨K⟩ : ScalarLocalization R A p) ⟶ ⟨M⟩))
        (c a ⊗ₜ[R'] F₀.map f : (⟨F₀.obj K⟩ : ScalarLocalization R' A' p') ⟶ ⟨F₀.obj M⟩))
    {X Y : ScalarLocalization R A p} {X₀ Y₀ : A} (hX : X = ⟨X₀⟩) (hY : Y = ⟨Y₀⟩)
    (x : X ⟶ Y) (a : Localization.Away p) (g : X₀ ⟶ Y₀)
    (hx : HEq x (a ⊗ₜ[R] g : (⟨X₀⟩ : ScalarLocalization R A p) ⟶ ⟨Y₀⟩)) :
    HEq (F.map x)
      (c a ⊗ₜ[R'] F₀.map g : (⟨F₀.obj X₀⟩ : ScalarLocalization R' A' p') ⟶ ⟨F₀.obj Y₀⟩) := by
  subst hX hY
  rw [eq_of_heq hx]
  exact hFm X₀ Y₀ g a

-- The pure-tensor normalization of a localized closed datum, for any equal integral pair.
private theorem symm_heq_tmul (p : R) (T₀ : A × A ⥤ A) {J₀ : ObjectProperty (Aᵒᵖ × A)}
    (H₀ : J₀.FullSubcategory ⥤ A) (S₀ : PodPartialClosed T₀ J₀ H₀)
    {J : ObjectProperty ((ScalarLocalization R A p)ᵒᵖ × ScalarLocalization R A p)}
    (hJ : ∀ MN, J MN → J₀ (op MN.1.unop.obj, MN.2.obj))
    (T : ScalarLocalization R A p × ScalarLocalization R A p ⥤ ScalarLocalization R A p)
    (H : J.FullSubcategory ⥤ ScalarLocalization R A p) (S : PodPartialClosed T J H)
    (hS : ∀ (L : ScalarLocalization R A p) (P : J.FullSubcategory)
      (f : L.obj ⟶ H₀.obj ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ _ P.property⟩)
      (a : Localization.Away p) (q : L ⟶ H.obj P),
      HEq q (a ⊗ₜ[R] f) →
        HEq ((S.transpose L P).symm q) (a ⊗ₜ[R] (S₀.transpose L.obj _).symm f))
    (L : ScalarLocalization R A p) (L₀ : A) (hL : L = ⟨L₀⟩)
    (P : J.FullSubcategory) (Q₀ : J₀.FullSubcategory)
    (hQ : (⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ _ P.property⟩ : J₀.FullSubcategory) = Q₀)
    (f : L₀ ⟶ H₀.obj Q₀) (a : Localization.Away p) (q : L ⟶ H.obj P)
    (hq : HEq q (a ⊗ₜ[R] f : (⟨L₀⟩ : ScalarLocalization R A p) ⟶ ⟨H₀.obj Q₀⟩)) :
    HEq ((S.transpose L P).symm q)
      (a ⊗ₜ[R] (S₀.transpose L₀ Q₀).symm f :
        (⟨T₀.obj (L₀, Q₀.obj.1.unop)⟩ : ScalarLocalization R A p) ⟶ ⟨Q₀.obj.2⟩) := by
  subst hQ hL
  exact hS _ P f a q hq

/-- Let `F` be a functor of scalar localizations acting on pure tensors through an integral
functor `F₀`, and let `S`, `S'` be localized partial closed data with the pure-tensor
normalization over integral data `S₀`, `S₀'`. If the integral inverse transposition commutes
with `F₀`, conjugated by integral tensor and Hom comparisons `τ₀`, `η₀`, then the localized
inverse transposition commutes with `F`, conjugated by their localizations `τ`, `η`. -/
theorem localizedInverseTranspose_scalar (p : R) (p' : R')
    (c : Localization.Away p → Localization.Away p')
    (T₀ : A × A ⥤ A) {J₀ : ObjectProperty (Aᵒᵖ × A)} (H₀ : J₀.FullSubcategory ⥤ A)
    (S₀ : PodPartialClosed T₀ J₀ H₀)
    (T₀' : A' × A' ⥤ A') {J₀' : ObjectProperty (A'ᵒᵖ × A')} (H₀' : J₀'.FullSubcategory ⥤ A')
    (S₀' : PodPartialClosed T₀' J₀' H₀')
    (T : ScalarLocalization R A p × ScalarLocalization R A p ⥤ ScalarLocalization R A p)
    (hTo : ∀ MN, T.obj MN = ⟨T₀.obj (MN.1.obj, MN.2.obj)⟩)
    {J : ObjectProperty ((ScalarLocalization R A p)ᵒᵖ × ScalarLocalization R A p)}
    (hJ : ∀ MN, J MN → J₀ (op MN.1.unop.obj, MN.2.obj))
    (H : J.FullSubcategory ⥤ ScalarLocalization R A p)
    (hHo : ∀ P : J.FullSubcategory,
      H.obj P = ⟨H₀.obj ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ _ P.property⟩⟩)
    (S : PodPartialClosed T J H)
    (hS : ∀ (L : ScalarLocalization R A p) (P : J.FullSubcategory)
      (f : L.obj ⟶ H₀.obj ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ _ P.property⟩)
      (a : Localization.Away p) (q : L ⟶ H.obj P),
      HEq q (a ⊗ₜ[R] f) →
        HEq ((S.transpose L P).symm q) (a ⊗ₜ[R] (S₀.transpose L.obj _).symm f))
    (T' : ScalarLocalization R' A' p' × ScalarLocalization R' A' p' ⥤
      ScalarLocalization R' A' p')
    (hTo' : ∀ MN, T'.obj MN = ⟨T₀'.obj (MN.1.obj, MN.2.obj)⟩)
    {J' : ObjectProperty ((ScalarLocalization R' A' p')ᵒᵖ × ScalarLocalization R' A' p')}
    (hJ' : ∀ MN, J' MN → J₀' (op MN.1.unop.obj, MN.2.obj))
    (H' : J'.FullSubcategory ⥤ ScalarLocalization R' A' p')
    (hHo' : ∀ P : J'.FullSubcategory,
      H'.obj P = ⟨H₀'.obj ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ' _ P.property⟩⟩)
    (S' : PodPartialClosed T' J' H')
    (hS' : ∀ (L : ScalarLocalization R' A' p') (P : J'.FullSubcategory)
      (f : L.obj ⟶ H₀'.obj ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ' _ P.property⟩)
      (a : Localization.Away p') (q : L ⟶ H'.obj P),
      HEq q (a ⊗ₜ[R'] f) →
        HEq ((S'.transpose L P).symm q) (a ⊗ₜ[R'] (S₀'.transpose L.obj _).symm f))
    (F₀ : A ⥤ A') (F : ScalarLocalization R A p ⥤ ScalarLocalization R' A' p') [F.Additive]
    (hFo : ∀ K, F.obj K = ⟨F₀.obj K.obj⟩)
    (hFm : ∀ (K M : A) (f : K ⟶ M) (a : Localization.Away p),
      HEq (F.map (a ⊗ₜ[R] f : (⟨K⟩ : ScalarLocalization R A p) ⟶ ⟨M⟩))
        (c a ⊗ₜ[R'] F₀.map f : (⟨F₀.obj K⟩ : ScalarLocalization R' A' p') ⟶ ⟨F₀.obj M⟩))
    (L : ScalarLocalization R A p) (P : J.FullSubcategory)
    (hP' : J' (op (F.obj P.obj.1.unop), F.obj P.obj.2))
    (hP₀' : J₀' (op (F₀.obj P.obj.1.unop.obj), F₀.obj P.obj.2.obj))
    (τ : F.obj (T.obj (L, P.obj.1.unop)) ⟶ T'.obj (F.obj L, F.obj P.obj.1.unop))
    (τ₀ : F₀.obj (T₀.obj (L.obj, P.obj.1.unop.obj)) ⟶
      T₀'.obj (F₀.obj L.obj, F₀.obj P.obj.1.unop.obj))
    (hτ : HEq τ ((1 : Localization.Away p') ⊗ₜ[R'] τ₀ :
      (⟨F₀.obj (T₀.obj (L.obj, P.obj.1.unop.obj))⟩ : ScalarLocalization R' A' p') ⟶
        ⟨T₀'.obj (F₀.obj L.obj, F₀.obj P.obj.1.unop.obj)⟩))
    (η : F.obj (H.obj P) ⟶ H'.obj ⟨(op (F.obj P.obj.1.unop), F.obj P.obj.2), hP'⟩)
    (η₀ : F₀.obj (H₀.obj ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ _ P.property⟩) ⟶
      H₀'.obj ⟨(op (F₀.obj P.obj.1.unop.obj), F₀.obj P.obj.2.obj), hP₀'⟩)
    (hη : HEq η ((1 : Localization.Away p') ⊗ₜ[R'] η₀ :
      (⟨F₀.obj (H₀.obj ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ _ P.property⟩)⟩ :
        ScalarLocalization R' A' p') ⟶
        ⟨H₀'.obj ⟨(op (F₀.obj P.obj.1.unop.obj), F₀.obj P.obj.2.obj), hP₀'⟩⟩))
    (hcore : ∀ f : L.obj ⟶ H₀.obj ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ _ P.property⟩,
      F₀.map ((S₀.transpose L.obj _).symm f) =
        τ₀ ≫ (S₀'.transpose (F₀.obj L.obj)
          ⟨(op (F₀.obj P.obj.1.unop.obj), F₀.obj P.obj.2.obj), hP₀'⟩).symm (F₀.map f ≫ η₀))
    (φ : L ⟶ H.obj P) :
    F.map ((S.transpose L P).symm φ) =
      τ ≫ (S'.transpose (F.obj L) ⟨(op (F.obj P.obj.1.unop), F.obj P.obj.2), hP'⟩).symm
        (F.map φ ≫ η) := by
  have hQ : (⟨(op (F.obj P.obj.1.unop).obj, (F.obj P.obj.2).obj), hJ' _ hP'⟩ :
      J₀'.FullSubcategory) = ⟨(op (F₀.obj P.obj.1.unop.obj), F₀.obj P.obj.2.obj), hP₀'⟩ := by
    exact ObjectProperty.FullSubcategory.ext (Prod.ext
      (congrArg (fun X ↦ op X.obj) (hFo P.obj.1.unop)) (congrArg (·.obj) (hFo P.obj.2)))
  apply localizedHom_induction' p L (H.obj P) _ (hHo P) _ φ
  · intro a f q hq
    have eL : F.obj L = ⟨F₀.obj L.obj⟩ := hFo L
    have eH : F.obj (H.obj P) =
        ⟨F₀.obj (H₀.obj ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hJ _ P.property⟩)⟩ :=
      (hFo _).trans (congrArg (fun X : ScalarLocalization R A p ↦
        (⟨F₀.obj X.obj⟩ : ScalarLocalization R' A' p')) (hHo P))
    have eH' : H'.obj ⟨(op (F.obj P.obj.1.unop), F.obj P.obj.2), hP'⟩ =
        ⟨H₀'.obj ⟨(op (F₀.obj P.obj.1.unop.obj), F₀.obj P.obj.2.obj), hP₀'⟩⟩ :=
      (hHo' _).trans (congrArg (fun Q ↦ (⟨H₀'.obj Q⟩ : ScalarLocalization R' A' p')) hQ)
    have eT : F.obj (T.obj (L, P.obj.1.unop)) =
        ⟨F₀.obj (T₀.obj (L.obj, P.obj.1.unop.obj))⟩ :=
      (hFo _).trans (congrArg (fun X : ScalarLocalization R A p ↦
        (⟨F₀.obj X.obj⟩ : ScalarLocalization R' A' p')) (hTo _))
    have eT' : T'.obj (F.obj L, F.obj P.obj.1.unop) =
        ⟨T₀'.obj (F₀.obj L.obj, F₀.obj P.obj.1.unop.obj)⟩ := by
      rw [hTo', hFo L, hFo P.obj.1.unop]
    -- The left side on a pure tensor.
    have hl := map_heq_tmul p p' c F₀ F hFm (hTo _) rfl _ a _ (hS L P f a q hq)
    -- The right side on a pure tensor.
    have h₄ := (heq_comp eL eH eH' (map_heq_tmul p p' c F₀ F hFm rfl (hHo P) q a f hq)
      hη).trans (heq_of_eq (ScalarLocalization.tmul_comp_tmul _ _ _ _))
    have h₅ := symm_heq_tmul p' T₀' H₀' S₀' hJ' T' H' S' hS' (F.obj L) (F₀.obj L.obj) eL _ _
      hQ _ _ _ h₄
    have hr := (heq_comp eT eT' (hFo _) hτ h₅).trans
      (heq_of_eq (ScalarLocalization.tmul_comp_tmul _ _ _ _))
    apply eq_of_heq
    refine hl.trans (HEq.trans (heq_of_eq ?_) hr.symm)
    rw [hcore, mul_one, one_mul]
  · intro q q' hq hq'
    rw [map_add, F.map_add, hq, hq', F.map_add, Preadditive.add_comp, map_add,
      Preadditive.comp_add]

end Localization



section Closed
universe a b c d
variable {A : Type a} {B : Type b} [Category.{c} A] [Category.{d} B]
  {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}

-- Transposition is natural in the tensor parameter.
private theorem transpose_tensor_comp (S : CoefficientClosedStructure HB) {T' T P Q : B}
    (k : T' ⟶ T) (f : S.tensor.obj (T, P) ⟶ Q) :
    S.transpose T' P Q (S.tensor.map (Prod.mkHom k (𝟙 P)) ≫ f) = k ≫ S.transpose T P Q f := by
  have h := S.comp_transpose_comp k f (𝟙 Q)
  have hid : HB.map (Prod.mkHom (𝟙 (op P)) (𝟙 Q)) = 𝟙 _ := by
    rw [← HB.map_id]
    rfl
  rw [hid, Category.comp_id, Category.comp_id] at h
  exact h.symm

/-- Let `Fo` be a functor with a closed tensor comparison `μ`, and let `F` receive a
completion map `c` from `Fo`. For completion units `uA`, `uB` from the closed tensors to
completed tensors `CA`, `CB`, compatible with `μ` and a completed tensor comparison `sto`,
transposition of completion-unit precompositions commutes with `F`, conjugated by the
completed tensor and Hom comparisons `tc`, `hc` built from `sto` and the evaluation-defined
base change of `μ`. -/
theorem completedTranspose_scalar (SA : CoefficientClosedStructure HA)
    (SB : CoefficientClosedStructure HB) (CA : A × A ⥤ A) (CB : B × B ⥤ B)
    (uA : ∀ X Y : A, SA.tensor.obj (X, Y) ⟶ CA.obj (X, Y))
    (uB : ∀ X Y : B, SB.tensor.obj (X, Y) ⟶ CB.obj (X, Y))
    (huB : ∀ (X Y X' Y' : B) (f : X ⟶ X') (g : Y ⟶ Y'),
      SB.tensor.map (Prod.mkHom f g) ≫ uB X' Y' = uB X Y ≫ CB.map (Prod.mkHom f g))
    (Fo F : A ⥤ B) (c : Fo ⟶ F) (μ : SA.tensor ⋙ Fo ≅ Fo.prod Fo ⋙ SB.tensor)
    (sto : CA ⋙ Fo ≅ Fo.prod Fo ⋙ CB)
    (hunit : ∀ X Y : A,
      Fo.map (uA X Y) ≫ sto.hom.app (X, Y) = μ.hom.app (X, Y) ≫ uB (Fo.obj X) (Fo.obj Y))
    (K M N : A) (cK : Fo.obj K ≅ F.obj K) (hcK : cK.hom = c.app K)
    (cM : Fo.obj M ≅ F.obj M)
    (cN : Fo.obj N ≅ F.obj N) (hcN : cN.hom = c.app N)
    (cT : Fo.obj (CA.obj (K, M)) ≅ F.obj (CA.obj (K, M))) (hcT : cT.hom = c.app _)
    (cH : Fo.obj (HA.obj (op M, N)) ≅ F.obj (HA.obj (op M, N))) (hcH : cH.hom = c.app _)
    (tc : F.obj (CA.obj (K, M)) ≅ CB.obj (F.obj K, F.obj M))
    (htc : tc.hom = cT.inv ≫ sto.hom.app (K, M) ≫ CB.map (Prod.mkHom cK.hom cM.hom))
    (hc : F.obj (HA.obj (op M, N)) ≅ HB.obj (op (F.obj M), F.obj N))
    (hhc : hc.hom = cH.inv ≫ coefficientBaseChangeHom SA SB Fo μ M N ≫
      HB.map (Prod.mkHom cM.inv.op cN.hom))
    (g : CA.obj (K, M) ⟶ N) :
    F.map (SA.transpose K M N (uA K M ≫ g)) ≫ hc.hom =
      SB.transpose (F.obj K) (F.obj M) (F.obj N) (uB _ _ ≫ tc.inv ≫ F.map g) := by
  -- Replace `F` by `Fo` on the transpose.
  have hF : F.map (SA.transpose K M N (uA K M ≫ g)) ≫ cH.inv =
      cK.inv ≫ Fo.map (SA.transpose K M N (uA K M ≫ g)) := by
    rw [Iso.comp_inv_eq, Category.assoc, hcH, c.naturality, ← Category.assoc, ← hcK,
      Iso.inv_hom_id, Category.id_comp]
  have hsplit : HB.map (Prod.mkHom cM.inv.op cN.hom) =
      HB.map (Prod.mkHom (𝟙 (op (Fo.obj M))) cN.hom) ≫
        HB.map (Prod.mkHom cM.inv.op (𝟙 (F.obj N))) := by
    rw [← HB.map_comp]
    congr 1
    ext <;> simp
  have hb := coefficientBaseChangeHom_comp SA SB Fo μ (𝟙 (Fo.obj K))
    (SA.transpose K M N (uA K M ≫ g)) cN.hom
  rw [Category.id_comp, Equiv.symm_apply_apply] at hb
  rw [hhc, reassoc_of% hF, hsplit]
  rw [reassoc_of% hb, SB.transpose_comp_map_op, ← transpose_tensor_comp]
  congr 1
  have htc' : tc.inv = CB.map (Prod.mkHom cK.inv cM.inv) ≫ sto.inv.app (K, M) ≫ cT.hom := by
    rw [← cancel_epi tc.hom, Iso.hom_inv_id, htc]
    simp only [Category.assoc]
    rw [← CB.map_comp_assoc]
    simp
  have hun : uB _ _ ≫ sto.inv.app (K, M) = μ.inv.app (K, M) ≫ Fo.map (uA K M) := by
    rw [← cancel_epi (μ.hom.app (K, M)), ← reassoc_of% (hunit K M)]
    simp
  have hng : cT.hom ≫ F.map g = Fo.map g ≫ cN.hom := by
    rw [hcT, hcN, c.naturality]
  have hten : SB.tensor.map (Prod.mkHom cK.inv (𝟙 (F.obj M))) ≫
      SB.tensor.map (Prod.mkHom (𝟙 (Fo.obj K)) cM.inv) ≫
        SB.tensor.map (Prod.mkHom (𝟙 (Fo.obj K)) (𝟙 (Fo.obj M))) =
      SB.tensor.map (Prod.mkHom cK.inv cM.inv) := by
    rw [← SB.tensor.map_comp, ← SB.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [htc', Category.assoc, Category.assoc, ← reassoc_of% (huB _ _ _ _ cK.inv cM.inv),
    reassoc_of% hun, hng, reassoc_of% hten,
    Fo.map_comp, Category.assoc]

end Closed

section Coefficients
open TensorProduct
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]

/-- Ordinary scalar extension carries the ordinary-to-completed tensor unit to the
ordinary-to-completed tensor unit, conjugated by the closed and completed tensor scalar
comparisons. -/
theorem podCompletedTensorUnit_scalar (M N : DerivedCategory (integralTowerModules l E W)) :
    (integralOrdinaryDerivedScalar l E L ι W).map (podCompletedTensorUnit l E W M N) ≫
        (scalarTensorOrdinary l E L ι W).hom.app (M, N) =
      (scalarClosedTensor l E L ι W).hom.app (M, N) ≫
        podCompletedTensorUnit l L W ((integralOrdinaryDerivedScalar l E L ι W).obj M)
          ((integralOrdinaryDerivedScalar l E L ι W).obj N) := by
  sorry

/-- Completed scalar extension carries integral inverse transposition, conjugated by the
integral tensor and internal-Hom scalar comparisons, to integral inverse transposition. -/
theorem podIntegralClosed_scalar_symm (K : sfIntegralConstructibleCategory l E W)
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
    (f : K ⟶ (constructibleIntegralHom l E W).obj P) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι W).map (((podIntegralClosed l E W).transpose K P).symm f) =
      (integralTensorScalarComparison l E L ι W K P.obj.1.unop).hom ≫
        ((podIntegralClosed l L W).transpose
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj K)
          (integralHomScalarPair l E L ι W P)).symm
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map f ≫
            (integralHomScalarComparison l E L ι W P).hom) := by
  obtain ⟨g, rfl⟩ : ∃ g, f = (podIntegralClosed l E W).transpose K P g :=
    ⟨_, (AddEquiv.apply_symm_apply _ f).symm⟩
  rw [AddEquiv.symm_apply_apply]
  have key : (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
          ((podIntegralClosed l E W).transpose K P g) ≫
        (integralHomScalarComparison l E L ι W P).hom =
      (podIntegralClosed l L W).transpose
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).obj K)
        (integralHomScalarPair l E L ι W P)
        ((integralTensorScalarComparison l E L ι W K P.obj.1.unop).inv ≫
          (sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map g) := by
    apply ObjectProperty.hom_ext
    have hS : ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W).map
          ((podIntegralClosed l E W).transpose K P g)).hom =
        (integralScalarExtension l E L ι W).map
          ((podIntegralClosed l E W).transpose K P g).hom := rfl
    rw [integralTranspose_normalization, ObjectProperty.FullSubcategory.comp_hom, hS,
      integralTranspose_normalization]
    exact completedTranspose_scalar (pullbackTensorCalculus l E W).integralClosed
      (pullbackTensorCalculus l L W).integralClosed (integralCompletedTensor l E W)
      (integralCompletedTensor l L W) (podCompletedTensorUnit l E W)
      (podCompletedTensorUnit l L W) (completedTensorUnit_naturality l L W)
      (integralOrdinaryDerivedScalar l E L ι W) (integralScalarExtension l E L ι W)
      (scalarCompletion l E L ι W) (scalarClosedTensor l E L ι W)
      (scalarTensorOrdinary l E L ι W) (podCompletedTensorUnit_scalar l E L ι W)
      K.obj P.obj.1.unop.obj P.obj.2.obj
      (scalarCompletionIso l E L ι W _ K.property.1) rfl
      (scalarCompletionIso l E L ι W _ P.obj.1.unop.property.1)
      (scalarCompletionIso l E L ι W _ P.obj.2.property.1) rfl
      (scalarCompletionIso l E L ι W _
        ((constructibleIntegralTensor l E W).obj (K, P.obj.1.unop)).property.1) rfl
      (scalarCompletionIso l E L ι W _ P.property.1) rfl
      (scalarTensorCompleted l E L ι W K.obj P.obj.1.unop.obj K.property.1
        P.obj.1.unop.property.1
        ((constructibleIntegralTensor l E W).obj (K, P.obj.1.unop)).property.1) rfl
      (scalarHomCompleted l E L ι W P.obj.1.unop.obj P.obj.2.obj P.obj.1.unop.property.1
        P.obj.2.property.1 P.property.1) rfl g.hom
  rw [key, AddEquiv.symm_apply_apply, Iso.hom_inv_id_assoc]

/-- Rational scalar extension carries inverse transposition of a normalized rational closed
datum, conjugated by the rational tensor and internal-Hom scalar comparisons, to inverse
transposition of a normalized rational closed datum. -/
theorem podRationalClosed_scalar_symm
    (S : PodPartialClosed (rationalDerivedTensor l E W)
      (constructibleRationalHomPairs l E W) (rationalDerivedInternalHom l E W))
    (hS : ∀ (K : sfRationalConstructibleCategory l E W)
      (P : (constructibleRationalHomPairs l E W).FullSubcategory)
      (f : K.obj ⟶ (constructibleIntegralHom l E W).obj
        (integralPairOfRationalHomPair l E W P))
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
      (q : K ⟶ (rationalDerivedInternalHom l E W).obj P),
      HEq q (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) →
      HEq ((S.transpose K P).symm q)
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
          ((podIntegralClosed l E W).transpose K.obj
            (integralPairOfRationalHomPair l E W P)).symm f))
    (S' : PodPartialClosed (rationalDerivedTensor l L W)
      (constructibleRationalHomPairs l L W) (rationalDerivedInternalHom l L W))
    (hS' : ∀ (K : sfRationalConstructibleCategory l L W)
      (P : (constructibleRationalHomPairs l L W).FullSubcategory)
      (f : K.obj ⟶ (constructibleIntegralHom l L W).obj
        (integralPairOfRationalHomPair l L W P))
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l L))
      (q : K ⟶ (rationalDerivedInternalHom l L W).obj P),
      HEq q (a ⊗ₜ[Padic.coefficientExtensionIntegers l L] f) →
      HEq ((S'.transpose K P).symm q)
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l L]
          ((podIntegralClosed l L W).transpose K.obj
            (integralPairOfRationalHomPair l L W P)).symm f))
    (K : sfRationalConstructibleCategory l E W)
    (P : (constructibleRationalHomPairs l E W).FullSubcategory)
    (φ : K ⟶ (rationalDerivedInternalHom l E W).obj P) :
    (sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        ((S.transpose K P).symm φ) =
      (rationalTensorScalarComparison l E L ι W).hom.app (K, P.obj.1.unop) ≫
        (S'.transpose ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K)
          (rationalHomScalarPair l E L ι W P)).symm
          ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map φ ≫
            (rationalHomScalarComparison l E L ι W P).hom) := by
  have hF := (sfRationalScalarExtension_existsUnique l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec
  have : (sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).Additive := hF.1
  have hT := (rationalDerivedTensor_existsUnique l E W).exists.choose_spec
  have hT' := (rationalDerivedTensor_existsUnique l L W).exists.choose_spec
  have hH := (rationalDerivedInternalHom_existsUnique l E W).exists.choose_spec
  have hH' := (rationalDerivedInternalHom_existsUnique l L W).exists.choose_spec
  exact localizedInverseTranspose_scalar (Padic.coefficientExtensionUniformizer l E)
    (Padic.coefficientExtensionUniformizer l L)
    (fun a ↦ (sfRationalCoefficientEquiv l L).symm (ι (sfRationalCoefficientEquiv l E a)))
    (constructibleIntegralTensor l E W) (constructibleIntegralHom l E W)
    (podIntegralClosed l E W)
    (constructibleIntegralTensor l L W) (constructibleIntegralHom l L W)
    (podIntegralClosed l L W)
    (rationalDerivedTensor l E W) hT.1 (fun _ h ↦ h) (rationalDerivedInternalHom l E W) hH.1
    S hS (rationalDerivedTensor l L W) hT'.1 (fun _ h ↦ h) (rationalDerivedInternalHom l L W)
    hH'.1 S' hS'
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι W)
    (sfRationalScalarExtension l E W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι)
    (sfRationalScalarExtension_obj l E W 0 _ L ι)
    (sfRationalScalarExtension_map_tmul l E W 0 _ L ι) K P
    (rationalHomScalarPair_permitted l E L ι W P)
    (integralHomScalarPair_permitted l E L ι W (integralPairOfRationalHomPair l E W P))
    _ _ ((rationalTensorScalarComparison_existsUnique l E L ι W).exists.choose_spec K _)
    _ _ ((rationalHomScalarComparison_existsUnique l E L ι W P).exists.choose_spec)
    (podIntegralClosed_scalar_symm l E L ι W K.obj (integralPairOfRationalHomPair l E W P)) φ

end Coefficients

end WeilConjectures
