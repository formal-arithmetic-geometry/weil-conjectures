/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!
# The internal hom of cochain complexes

Let `C` be a monoidal closed preadditive category (with `MonoidalPreadditive C`) which has
countable products. For cochain complexes `P` and `Y` in `C` indexed by `ℤ`, we construct the
internal hom complex `CochainComplex.internalHomObj P Y`, whose object in degree `n` is
`∏_{p + n = q} (P.X p ⟶[C] Y.X q)`, and whose differential has component
`(-1) ^ p • (f_{p, q - 1} ≫ d_Y - d_P ≫ f_{p + 1, q})` on the factor indexed by `(p, q)`.

When the tensor product of cochain complexes is defined (the `GradedObject` hypotheses of
`Mathlib.Algebra.Homology.Monoidal`), we construct the tensor-hom adjunction
`CochainComplex.tensorHomAdjunction P : tensorLeft P ⊣ CochainComplex.internalHom P`. Its unit
and counit are the coevaluation `K ⟶ internalHomObj P (P ⊗ K)` and the evaluation
`P ⊗ internalHomObj P Y ⟶ Y`.

The hom bijection is obtained from an isomorphism of groups of cochains
`CochainComplex.InternalHom.cochainEquiv P Y K n` between `Cochain (P ⊗ K) Y n` and
`Cochain K (internalHomObj P Y) n`, which commutes with the differentials of the hom complexes
(`curryCochain_δ`). It sends cocycles of degree `0` (i.e. morphisms of complexes) to cocycles
of degree `0`, and coboundaries to coboundaries, so that the tensor-hom bijection is compatible
with homotopies (`internalHomEquivHomotopy`); this is used in
`WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom` to descend the adjunction to
the homotopy category.

The sign `(-1) ^ p` in the differential is the one forced by the sign conventions for the
tensor product in `Mathlib.Algebra.Homology.Monoidal` (where the differential on
`P.X p ⊗ K.X q` is `d_P ⊗ 1 + (-1) ^ p • 1 ⊗ d_K`) if the hom bijection is to be given by plain
currying on morphisms of complexes.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory
open MonoidalClosed hiding assoc id_comp comp_id

universe v u

namespace CochainComplex

open HomComplex

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [HasCountableProducts C] (P Y : CochainComplex C ℤ)

namespace InternalHom

omit [MonoidalPreadditive C] in
/-- The object of degree `n` of the internal hom complex. -/
noncomputable def X (n : ℤ) : C :=
  ∏ᶜ fun T : Triplet n ↦ (ihom (P.X T.p)).obj (Y.X T.q)

omit [MonoidalPreadditive C] in
/-- The projection from the object of degree `n` of the internal hom complex to a factor. -/
noncomputable def π (n p q : ℤ) (h : p + n = q) : X P Y n ⟶ (ihom (P.X p)).obj (Y.X q) :=
  Pi.π _ (⟨p, q, h⟩ : Triplet n)

omit [MonoidalPreadditive C] in
variable {P Y} in
@[ext]
lemma hom_ext {A : C} {n : ℤ} {f g : A ⟶ X P Y n}
    (h : ∀ p q hpq, f ≫ π P Y n p q hpq = g ≫ π P Y n p q hpq) : f = g :=
  Pi.hom_ext _ _ (fun T ↦ h T.p T.q T.hpq)

omit [MonoidalPreadditive C] in
/-- The differential of the internal hom complex. -/
noncomputable def d (n m : ℤ) : X P Y n ⟶ X P Y m :=
  Pi.lift fun T ↦ T.p.negOnePow •
    (π P Y n T.p (T.p + n) rfl ≫ (ihom _).map (Y.d (T.p + n) T.q) -
      π P Y n (T.p + m - n) T.q (by have := T.hpq; lia) ≫ (pre (P.d T.p (T.p + m - n))).app _)

omit [MonoidalPreadditive C] in
lemma d_π (n m p q : ℤ) (hpq : p + m = q) (q' p' : ℤ) (hq' : p + n = q') (hp' : p' + n = q) :
    d P Y n m ≫ π P Y m p q hpq = p.negOnePow •
      (π P Y n p q' hq' ≫ (ihom _).map (Y.d q' q) -
        π P Y n p' q hp' ≫ (pre (P.d p p')).app _) := by
  subst hq'
  obtain rfl : p' = p + m - n := by lia
  simp only [d, π, X, Pi.lift_π]

lemma shape (n m : ℤ) (hnm : ¬ n + 1 = m) : d P Y n m = 0 := by
  ext p q hpq
  rw [d_π P Y n m p q hpq (p + n) (p + m - n) rfl (by lia), Y.shape, P.shape]
  · simp [pre_zero_app]
  all_goals simp only [ComplexShape.up_Rel]; lia

lemma d_comp_d (n₁ n₂ n₃ : ℤ) : d P Y n₁ n₂ ≫ d P Y n₂ n₃ = 0 := by
  by_cases h₁₂ : n₁ + 1 = n₂
  · by_cases h₂₃ : n₂ + 1 = n₃
    · ext p q hpq
      rw [assoc, d_π P Y n₂ n₃ p q hpq (q - 1) (p + 1) (by lia) (by lia), Linear.comp_units_smul,
        Preadditive.comp_sub, reassoc_of% (d_π P Y n₁ n₂ p (q - 1) (by lia) (q - 2) (p + 1)
          (by lia) (by lia)), reassoc_of% (d_π P Y n₁ n₂ (p + 1) q (by lia) (q - 1) (p + 2)
          (by lia) (by lia))]
      simp only [Linear.units_smul_comp, Preadditive.sub_comp, assoc, ← Functor.map_comp,
        HomologicalComplex.d_comp_d, Functor.map_zero, comp_zero, ← NatTrans.comp_app, ← pre_map,
        pre_zero_app, zero_comp, pre_comm_ihom_map, sub_zero, zero_sub]
      rw [Int.negOnePow_succ]
      simp only [Units.neg_smul, smul_neg, smul_sub, smul_smul, Int.units_mul_self, one_smul]
      abel
    · rw [shape P Y n₂ n₃ h₂₃, comp_zero]
  · rw [shape P Y n₁ n₂ h₁₂, zero_comp]

end InternalHom

/-- The internal hom complex of two cochain complexes: in degree `n`, it is the product
of the internal homs `P.X p ⟶[C] Y.X q` for `p + n = q`. -/
noncomputable def internalHomObj : CochainComplex C ℤ where
  X := InternalHom.X P Y
  d := InternalHom.d P Y
  shape n m h := InternalHom.shape P Y n m h
  d_comp_d' _ _ _ _ _ := InternalHom.d_comp_d P Y _ _ _

/-- The projection from the object of degree `n` of `internalHomObj P Y` to the factor
`P.X p ⟶[C] Y.X q`, for `p + n = q`. -/
noncomputable def internalHomπ (n p q : ℤ) (h : p + n = q) :
    (internalHomObj P Y).X n ⟶ (ihom (P.X p)).obj (Y.X q) :=
  InternalHom.π P Y n p q h

variable {P Y} in
@[ext]
lemma internalHomObj_hom_ext {A : C} {n : ℤ} {f g : A ⟶ (internalHomObj P Y).X n}
    (h : ∀ p q hpq, f ≫ internalHomπ P Y n p q hpq = g ≫ internalHomπ P Y n p q hpq) :
    f = g :=
  InternalHom.hom_ext h

@[reassoc]
lemma internalHomObj_d_π (n m p q : ℤ) (hpq : p + m = q) (q' p' : ℤ) (hq' : p + n = q')
    (hp' : p' + n = q) :
    (internalHomObj P Y).d n m ≫ internalHomπ P Y m p q hpq = p.negOnePow •
      (internalHomπ P Y n p q' hq' ≫ (ihom _).map (Y.d q' q) -
        internalHomπ P Y n p' q hp' ≫ (pre (P.d p p')).app _) :=
  InternalHom.d_π P Y n m p q hpq q' p' hq' hp'

end

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C] [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {P Y : CochainComplex C ℤ} (K : CochainComplex C ℤ)

namespace InternalHom

open HomologicalComplex

variable {K} in
/-- The cochain `K ⟶ internalHomObj P Y` of degree `n` corresponding to a cochain
`P ⊗ K ⟶ Y` of degree `n`: its component `K.X q ⟶ P.X p ⟶[C] Y.X (p + q + n)` is the
curried component `P.X p ⊗ K.X q ⟶ Y.X (p + q + n)`, with the sign `(-1) ^ (p * n)`. -/
noncomputable def curryCochain {n : ℤ} (z : Cochain (P ⊗ K) Y n) :
    Cochain K (internalHomObj P Y) n :=
  Cochain.mk fun q _ _ ↦ Pi.lift fun T ↦ (T.p * n).negOnePow •
    curry (ιTensorObj P K T.p q (T.p + q) rfl ≫ z.v (T.p + q) T.q (by have := T.hpq; lia))

variable {K} in
/-- The inverse of `curryCochain`. -/
noncomputable def uncurryCochain {n : ℤ} (w : Cochain K (internalHomObj P Y) n) :
    Cochain (P ⊗ K) Y n :=
  Cochain.mk fun _ s _ ↦ mapBifunctorDesc fun p q hpq ↦ (p * n).negOnePow •
    uncurry (w.v q (s - p) (by simp at hpq; lia) ≫ internalHomπ P Y (s - p) p s (by lia))

variable {K}

@[reassoc]
lemma curryCochain_v_π {n : ℤ} (z : Cochain (P ⊗ K) Y n) (q q' : ℤ) (hqq' : q + n = q')
    (p s : ℤ) (hps : p + q' = s) (r : ℤ) (hr : p + q = r) (hrs : r + n = s) :
    (curryCochain z).v q q' hqq' ≫ internalHomπ P Y q' p s hps =
      (p * n).negOnePow • curry (ιTensorObj P K p q r hr ≫ z.v r s hrs) := by
  subst hr
  exact Pi.lift_π _ _

@[reassoc]
lemma ι_uncurryCochain_v {n : ℤ} (w : Cochain K (internalHomObj P Y) n) (r s : ℤ)
    (hrs : r + n = s) (p q : ℤ) (hpq : p + q = r) (q' : ℤ) (hqq' : q + n = q')
    (hps : p + q' = s) :
    ιTensorObj P K p q r hpq ≫ (uncurryCochain w).v r s hrs =
      (p * n).negOnePow • uncurry (w.v q q' hqq' ≫ internalHomπ P Y q' p s hps) := by
  obtain rfl : q' = s - p := by lia
  rw [uncurryCochain, Cochain.mk_v, ι_mapBifunctorDesc]

variable (P Y K) in
/-- The bijection between cochains `P ⊗ K ⟶ Y` of degree `n` and cochains
`K ⟶ internalHomObj P Y` of degree `n`. -/
noncomputable def cochainEquiv (n : ℤ) :
    Cochain (P ⊗ K) Y n ≃+ Cochain K (internalHomObj P Y) n where
  toFun := curryCochain
  invFun := uncurryCochain
  left_inv z := by
    ext r s hrs
    apply mapBifunctor.hom_ext
    intro p q hpq
    replace hpq : p + q = r := hpq
    rw [ι_uncurryCochain_v _ r s hrs p q hpq (q + n) rfl (by lia),
      curryCochain_v_π _ q (q + n) rfl p s (by lia) r hpq hrs, uncurry_units_smul, uncurry_curry,
      smul_smul, Int.units_mul_self, one_smul]
  right_inv w := by
    ext q q' hqq' p s hps
    rw [curryCochain_v_π _ q q' hqq' p s hps (p + q) rfl (by lia),
      ι_uncurryCochain_v _ (p + q) s (by lia) p q rfl q' hqq' hps, curry_units_smul, curry_uncurry,
      smul_smul, Int.units_mul_self, one_smul]
  map_add' z z' := by
    ext q q' hqq' p s hps
    rw [Cochain.add_v, Preadditive.add_comp,
      curryCochain_v_π _ q q' hqq' p s hps (p + q) rfl (by lia),
      curryCochain_v_π _ q q' hqq' p s hps (p + q) rfl (by lia),
      curryCochain_v_π _ q q' hqq' p s hps (p + q) rfl (by lia), Cochain.add_v,
      Preadditive.comp_add, curry_add, smul_add]

@[simp]
lemma cochainEquiv_apply {n : ℤ} (z : Cochain (P ⊗ K) Y n) :
    cochainEquiv P Y K n z = curryCochain z := rfl

@[simp]
lemma cochainEquiv_symm_apply {n : ℤ} (w : Cochain K (internalHomObj P Y) n) :
    (cochainEquiv P Y K n).symm w = uncurryCochain w := rfl

@[simp]
lemma curryCochain_uncurryCochain {n : ℤ} (w : Cochain K (internalHomObj P Y) n) :
    curryCochain (uncurryCochain w) = w :=
  (cochainEquiv P Y K n).apply_symm_apply w

@[simp]
lemma uncurryCochain_curryCochain {n : ℤ} (z : Cochain (P ⊗ K) Y n) :
    uncurryCochain (curryCochain z) = z :=
  (cochainEquiv P Y K n).symm_apply_apply z

lemma curryCochain_δ (n m : ℤ) (z : Cochain (P ⊗ K) Y n) :
    curryCochain (δ n m z) = δ n m (curryCochain z) := by
  by_cases hnm : n + 1 = m
  · subst hnm
    ext q q' hqq' p s hps
    rw [curryCochain_v_π _ q q' hqq' p s hps (p + q) rfl (by lia),
      δ_v n (n + 1) rfl z (p + q) s (by lia) (s - 1) (p + q + 1) (by lia) rfl,
      δ_v n (n + 1) rfl (curryCochain z) q q' hqq' (q' - 1) (q + 1) rfl rfl,
      Preadditive.add_comp, assoc, internalHomObj_d_π P Y (q' - 1) q' p s hps (s - 1) (p + 1)
        (by lia) (by lia), Linear.units_smul_comp, assoc,
      curryCochain_v_π _ (q + 1) q' (by lia) p s hps (p + q + 1) (by lia) (by lia),
      Linear.comp_units_smul, Preadditive.comp_sub, ← assoc, ← assoc,
      curryCochain_v_π _ q (q' - 1) (by lia) p (s - 1) (by lia) (p + q) rfl (by lia),
      curryCochain_v_π _ q (q' - 1) (by lia) (p + 1) s (by lia) (p + q + 1) (by lia) (by lia)]
    simp only [← curry_natural_right, curry_pre_app, ← curry_natural_left, Preadditive.comp_add,
      Linear.comp_units_smul, assoc, ιTensorObj_d_assoc P K p q (p + q) (p + q + 1) rfl rfl,
      Linear.units_smul_comp, ← curry_units_smul, ← curry_sub, ← curry_add]
    congr 1
    rw [mul_add, mul_one, add_mul, one_mul]
    simp only [Preadditive.add_comp, Linear.units_smul_comp, assoc, Int.negOnePow_add, smul_add,
      smul_sub, smul_smul, Int.negOnePow_one, mul_neg, neg_mul, mul_one, Units.neg_smul]
    have e₁ : (p * n).negOnePow * p.negOnePow = p.negOnePow * (p * n).negOnePow := mul_comm _ _
    have e₂ : (p * n).negOnePow * p.negOnePow * n.negOnePow =
        p.negOnePow * ((p * n).negOnePow * n.negOnePow) := by
      rw [e₁, mul_assoc]
    have e₃ : (p * n).negOnePow * p.negOnePow * (n.negOnePow * p.negOnePow) =
        n.negOnePow * (p * n).negOnePow := by
      rw [show (p * n).negOnePow * p.negOnePow * (n.negOnePow * p.negOnePow) =
        (p.negOnePow * p.negOnePow) * (n.negOnePow * (p * n).negOnePow) by ac_rfl,
        Int.units_mul_self, one_mul]
    simp only [smul_neg, smul_smul, e₁]
    rw [← e₁, e₂, e₃]
    abel
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm]
    exact (cochainEquiv P Y K m).map_zero

lemma uncurryCochain_δ (n m : ℤ) (w : Cochain K (internalHomObj P Y) n) :
    uncurryCochain (δ n m w) = δ n m (uncurryCochain w) :=
  (cochainEquiv P Y K m).injective (by
    rw [cochainEquiv_apply, cochainEquiv_apply, curryCochain_δ, curryCochain_uncurryCochain,
      curryCochain_uncurryCochain])

lemma curryCochain_ofHom_whiskerLeft_comp {K' : CochainComplex C ℤ} (f : K' ⟶ K) {n : ℤ}
    (z : Cochain (P ⊗ K) Y n) :
    curryCochain ((Cochain.ofHom (P ◁ f)).comp z (zero_add n)) =
      (Cochain.ofHom f).comp (curryCochain z) (zero_add n) := by
  ext q q' hqq' p s hps
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, assoc,
    curryCochain_v_π _ q q' hqq' p s hps (p + q) rfl (by lia),
    curryCochain_v_π _ q q' hqq' p s hps (p + q) rfl (by lia), Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, ιTensorObj_whiskerLeft_f_assoc, curry_natural_left, Linear.comp_units_smul]

end InternalHom

open InternalHom

variable (P Y) in
/-- The tensor-hom bijection `(P ⊗ K ⟶ Y) ≃ (K ⟶ internalHomObj P Y)` for cochain
complexes. -/
noncomputable def internalHomEquiv : (P ⊗ K ⟶ Y) ≃ (K ⟶ internalHomObj P Y) where
  toFun f := Cocycle.homOf (Cocycle.mk (curryCochain (Cochain.ofHom f)) 1 (zero_add 1) (by
    rw [← curryCochain_δ, δ_ofHom, ← cochainEquiv_apply, map_zero]))
  invFun g := Cocycle.homOf (Cocycle.mk (uncurryCochain (Cochain.ofHom g)) 1 (zero_add 1) (by
    rw [← uncurryCochain_δ, δ_ofHom, ← cochainEquiv_symm_apply, map_zero]))
  left_inv f := Cochain.ofHom_injective (by
    rw [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe, Cocycle.cochain_ofHom_homOf_eq_coe,
      Cocycle.mk_coe, uncurryCochain_curryCochain])
  right_inv g := Cochain.ofHom_injective (by
    rw [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe, Cocycle.cochain_ofHom_homOf_eq_coe,
      Cocycle.mk_coe, curryCochain_uncurryCochain])

@[simp]
lemma ofHom_internalHomEquiv (f : P ⊗ K ⟶ Y) :
    Cochain.ofHom (internalHomEquiv P Y K f) = curryCochain (Cochain.ofHom f) := by
  simp [internalHomEquiv]

@[simp]
lemma ofHom_internalHomEquiv_symm (g : K ⟶ internalHomObj P Y) :
    Cochain.ofHom ((internalHomEquiv P Y K).symm g) = uncurryCochain (Cochain.ofHom g) := by
  simp [internalHomEquiv]

lemma internalHomEquiv_whiskerLeft_comp {K' : CochainComplex C ℤ} (f : K' ⟶ K)
    (g : P ⊗ K ⟶ Y) :
    internalHomEquiv P Y K' (P ◁ f ≫ g) = f ≫ internalHomEquiv P Y K g :=
  Cochain.ofHom_injective (by
    rw [ofHom_internalHomEquiv, Cochain.ofHom_comp, Cochain.ofHom_comp, ofHom_internalHomEquiv,
      curryCochain_ofHom_whiskerLeft_comp])

variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

variable (P) in
/-- The internal hom functor `Y ↦ internalHomObj P Y` on cochain complexes, the right adjoint
of `P ⊗ -`. -/
noncomputable def internalHom : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  Adjunction.rightAdjointOfEquiv (F := tensorLeft P) (G_obj := internalHomObj P)
    (fun K Y ↦ internalHomEquiv P Y K) (fun _ _ _ f g ↦ internalHomEquiv_whiskerLeft_comp _ f g)

variable (P) in
/-- The tensor-hom adjunction `P ⊗ - ⊣ internalHom P` on cochain complexes. -/
noncomputable def tensorHomAdjunction : tensorLeft P ⊣ internalHom P :=
  Adjunction.adjunctionOfEquivRight _ _

@[simp]
lemma internalHom_obj : (internalHom P).obj Y = internalHomObj P Y := rfl

lemma tensorHomAdjunction_homEquiv (f : P ⊗ K ⟶ Y) :
    (tensorHomAdjunction P).homEquiv K Y f = internalHomEquiv P Y K f :=
  DFunLike.congr_fun (congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) K) Y) f

/-- The tensor-hom bijection sends homotopic morphisms to homotopic morphisms. -/
noncomputable def internalHomEquivHomotopy {f f' : P ⊗ K ⟶ Y} (h : Homotopy f f') :
    Homotopy (internalHomEquiv P Y K f) (internalHomEquiv P Y K f') :=
  (Cochain.equivHomotopy _ _).symm ⟨curryCochain (Cochain.ofHomotopy h), by
    rw [ofHom_internalHomEquiv, ofHom_internalHomEquiv, ← curryCochain_δ, δ_ofHomotopy,
      ← cochainEquiv_apply, ← cochainEquiv_apply, ← cochainEquiv_apply, ← map_add,
      sub_add_cancel]⟩

/-- The inverse of the tensor-hom bijection sends homotopic morphisms to homotopic
morphisms. -/
noncomputable def internalHomEquivSymmHomotopy {g g' : K ⟶ internalHomObj P Y}
    (h : Homotopy g g') :
    Homotopy ((internalHomEquiv P Y K).symm g) ((internalHomEquiv P Y K).symm g') :=
  (Cochain.equivHomotopy _ _).symm ⟨uncurryCochain (Cochain.ofHomotopy h), by
    rw [ofHom_internalHomEquiv_symm, ofHom_internalHomEquiv_symm, ← uncurryCochain_δ,
      δ_ofHomotopy, ← cochainEquiv_symm_apply, ← cochainEquiv_symm_apply,
      ← cochainEquiv_symm_apply, ← map_add, sub_add_cancel]⟩

end CochainComplex
