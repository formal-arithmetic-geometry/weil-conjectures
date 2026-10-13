module

public import Sheaf.Algebra.Homology.HomTensorDegreewise
import Sheaf.Algebra.Homology.HomTensorSummandPureExt
import Sheaf.Algebra.Homology.HomTensorPureDifferentials
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.HomComplex

/-!
# Three-term expansion of the iterated Hom differential

Source: Stacks Project, Tag 0A90 and the calculation in Tag 0A5Y.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

private lemma homTensorProjection_d (L M : CochainComplex Mod ℤ)
    (n m p r r' p' : ℤ) (hnm : n + 1 = m) (hr : p + m = r)
    (hr' : p + n = r') (hp' : p' + n = r) :
    (homComplex (R := R) L M).d n m ≫ homTensorProjection R L M m p r hr =
      homTensorProjection R L M n p r' hr' ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (L.X p)) (M.d r' r) -
        n.negOnePow • (homTensorProjection R L M n p' r hp' ≫
          SheafOfModules.homObjMap (R := R) (L.d p p') (𝟙 (M.X r))) := by
  exact (Classical.choose_spec (Classical.choose_spec
    (homComplex_exists.{u, v, max u v, max u v} (R := R)))).2.1
      L M n m p r r' p' hnm hr hr' hp'

attribute [local irreducible] homComplex homComplexFunctor

private noncomputable def localizedHomEvaluation {X A B : Mod} (U : Cᵒᵖ) (s : X.val.obj U)
    (W : (Over U.unop)ᵒᵖ) (z : A.val.obj (op W.unop.left)) :
    (X ⟶ SheafOfModules.homObj (R := R) A B) →+ B.val.obj (op W.unop.left) where
  toFun f := (((f.val.app U).hom s).app W).hom z
  map_zero' := rfl
  map_add' _ _ := rfl

private noncomputable def localizedHomSectionEvaluation {X A B : Mod}
    (f : X ⟶ SheafOfModules.homObj (R := R) A B) (U : Cᵒᵖ)
    (W : (Over U.unop)ᵒᵖ) (z : A.val.obj (op W.unop.left)) :
    X.val.obj U →+ B.val.obj (op W.unop.left) where
  toFun s := localizedHomEvaluation R U s W z f
  map_zero' := by
    dsimp only [localizedHomEvaluation, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [map_zero]
    rfl
  map_add' s s' := by
    dsimp only [localizedHomEvaluation, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [map_add]
    rfl

private lemma localizedHomEvaluation_map {X A A' B B' : Mod}
    (f : X ⟶ SheafOfModules.homObj (R := R) A B) (g : A' ⟶ A) (k : B ⟶ B')
    (U : Cᵒᵖ) (s : X.val.obj U) (W : (Over U.unop)ᵒᵖ)
    (z : A'.val.obj (op W.unop.left)) :
    localizedHomEvaluation R U s W z (f ≫ SheafOfModules.homObjMap (R := R) g k) =
      (k.val.app (op W.unop.left)).hom
        (localizedHomEvaluation R U s W ((g.val.app (op W.unop.left)).hom z) f) := rfl

private lemma localizedHomEvaluation_zsmul {X A B : Mod} (U : Cᵒᵖ) (s : X.val.obj U)
    (W : (Over U.unop)ᵒᵖ) (z : A.val.obj (op W.unop.left)) (r : ℤ)
    (f : X ⟶ SheafOfModules.homObj (R := R) A B) :
    localizedHomEvaluation R U s W (r • z) f =
      r • localizedHomEvaluation R U s W z f :=
  map_zsmul (((f.val.app U).hom s).app W).hom r z

private lemma localizedHomEvaluation_comp {X X' A B : Mod}
    (f : X' ⟶ X) (g : X ⟶ SheafOfModules.homObj (R := R) A B)
    (U : Cᵒᵖ) (s : X'.val.obj U) (W : (Over U.unop)ᵒᵖ)
    (z : A.val.obj (op W.unop.left)) :
    localizedHomEvaluation R U s W z (f ≫ g) =
      localizedHomEvaluation R U ((f.val.app U).hom s) W z g := rfl

private lemma localizedHomProjection_d (L M : CochainComplex Mod ℤ)
    (n m p r r' p' : ℤ) (hnm : n + 1 = m) (hr : p + m = r)
    (hr' : p + n = r') (hp' : p' + n = r) (U : Cᵒᵖ)
    (s : (homComplex (R := R) L M).X n |>.val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (L.X p).val.obj (op W.unop.left)) :
    localizedHomEvaluation R U
      ((((homComplex (R := R) L M).d n m).val.app U).hom s) W x
      (homTensorProjection R L M m p r hr) =
    ((M.d r' r).val.app (op W.unop.left)).hom
        (localizedHomEvaluation R U s W x (homTensorProjection R L M n p r' hr')) -
      (n.negOnePow : ℤ) • localizedHomEvaluation R U s W
        (((L.d p p').val.app (op W.unop.left)).hom x)
        (homTensorProjection R L M n p' r hp') := by
  have h := congrArg (localizedHomEvaluation R U s W x)
    (homTensorProjection_d R L M n m p r r' p' hnm hr hr' hp')
  simp only [map_sub, Units.smul_def, map_zsmul, localizedHomEvaluation_map,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.hom_id,
    LinearMap.id_apply] at h
  exact h

set_option synthInstance.maxSize 256 in
private lemma localizedHomEvaluation_curry
    (K L M : CochainComplex Mod ℤ) (n t p q r : ℤ) (h : p + q = t) (hr : t + n = r)
    (k : ℤ) (hk : p + n = k) (U : Cᵒᵖ)
    (s : (homComplex (R := R) K (homComplex (R := R) L M)).X n |>.val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (K.X p).val.obj (op W.unop.left))
    (y : (L.X q).val.obj (op W.unop.left)) :
    letI := SheafOfModules.monoidalCategory R
    localizedHomEvaluation R U s W
      (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
        p q t h).val.app (op W.unop.left)).hom
        (((homTensorSectionMap R (K.X p) (L.X q)).app (op W.unop.left)).hom
          (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)))
      (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M
          n t r hr) =
      localizedHomEvaluation R (op W.unop.left)
        (localizedHomEvaluation R U s W x
          (homTensorProjection R K (homComplex (R := R) L M) n p k hk))
        (op (Over.mk (𝟙 W.unop.left))) y
        (homTensorProjection R L M k q r (by omega)) := by
  subst t r k
  exact (homTensorDegreewiseMap_spec R K L M n).1 p q U s W x y

attribute [local irreducible] homTensorDegreewiseMap homTensorProjection

set_option maxHeartbeats 1000000 in
-- Localized evaluation of the chosen projections needs extra elaboration heartbeats.
set_option synthInstance.maxSize 256 in
/-- On one tensor summand the curried iterated Hom differential has three terms.
Source: Stacks Project, Tag 0A90, using the sign calculation of Tag 0A5Y
(blueprint: lem-sc-hom-tensor-iterated-differential-summand).

Proof: Restrict to K^p tensor L^q. On any localized site expand the outer Hom
projection formula in homComplex_exists: its postcomposition term applies the
inner Hom differential to f(x), and its precomposition term evaluates f(d_K x).
Expand the inner differential to obtain d_M(f(x)(y)) minus
(-1)^(p+n) f(x)(d_L y); the outer precomposition contributes
minus (-1)^n f(d_K x)(y). Use homTensorDegreewiseMap_spec to identify
all evaluations with the degreewise comparison. Mathlib's d1 summand map is
x tensor y mapped to d_K x tensor y, while its d2 summand map is
(-1)^p x tensor d_L y. The identity (-1)^(p+n)=(-1)^n*(-1)^p
therefore gives the three displayed terms. Bilinearity extends from pure
tensors in the presheaf tensor, and the sheafification adjunction gives the
identity on the sheaf tensor summand. Localized evaluation identifies the
resulting internal Hom maps. The argument applies to all integer degrees and
also when any differential or complex vanishes. It does not assemble the
summands or combine the two tensor differential terms. -/
theorem homTensorDegreewiseMap_iteratedDifferential_summand
    (K L M : CochainComplex Mod ℤ) (n t p q : ℤ) (h : p + q = t) :
    letI := SheafOfModules.monoidalCategory R
    let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
    let ι := CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q t h
    (homComplex (R := R) K (homComplex (R := R) L M)).d n (n + 1) ≫
        homTensorDegreewiseMap R K L M (n + 1) ≫
          homTensorProjection R T M (n + 1) t (t + (n + 1)) rfl ≫
            SheafOfModules.homObjMap (R := R) ι (𝟙 (M.X (t + (n + 1)))) =
      (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n t (t + n) rfl ≫
          SheafOfModules.homObjMap (R := R) ι (M.d (t + n) (t + (n + 1)))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor Mod)
              (ComplexShape.up ℤ) p q (t + 1)) (𝟙 (M.X (t + (n + 1))))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor Mod)
              (ComplexShape.up ℤ) p q (t + 1)) (𝟙 (M.X (t + (n + 1))))) := by
  let := SheafOfModules.monoidalCategory R
  subst t
  let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
  let ι := CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q (p + q) rfl
  apply homTensorSummandPure_ext R (K.X p) (L.X q) (M.X (p + q + (n + 1)))
  intro U s W x y
  let ev := localizedHomEvaluation R (B := M.X (p + q + (n + 1))) U s W
    (((homTensorSectionMap R (K.X p) (L.X q)).app (op W.unop.left)).hom
      (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))
  change ev ((homComplex (R := R) K (homComplex (R := R) L M)).d n (n + 1) ≫
        homTensorDegreewiseMap R K L M (n + 1) ≫
          homTensorProjection R T M (n + 1) (p + q) (p + q + (n + 1)) rfl ≫
            SheafOfModules.homObjMap (R := R) ι (𝟙 (M.X (p + q + (n + 1))))) =
    ev ((homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (p + q) (p + q + n) rfl ≫
          SheafOfModules.homObjMap (R := R) ι (M.d (p + q + n) (p + q + (n + 1)))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (p + q + 1) (p + q + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor Mod)
              (ComplexShape.up ℤ) p q (p + q + 1)) (𝟙 (M.X (p + q + (n + 1))))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (p + q + 1) (p + q + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor Mod)
              (ComplexShape.up ℤ) p q (p + q + 1)) (𝟙 (M.X (p + q + (n + 1))))))
  dsimp only [ev]
  simp only [map_sub, Units.smul_def, map_zsmul]
  simp only [← Category.assoc, localizedHomEvaluation_map, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.hom_id, LinearMap.id_apply]
  have hd := homTensor_pure_differentials R K L p q (p + q) rfl
    (op W.unop.left) x y
  erw [hd.1, hd.2]
  simp only [Units.smul_def, localizedHomEvaluation_zsmul]
  rw [Category.assoc, localizedHomEvaluation_comp]
  have hc := localizedHomEvaluation_curry R K L M n (p + q) p q (p + q + n)
    rfl rfl (p + n) rfl U s W x y
  have hcK := localizedHomEvaluation_curry R K L M n (p + q + 1) (p + 1) q
    (p + q + (n + 1)) (by omega) (by omega) (p + (n + 1)) (by omega) U s W
    (((K.d p (p + 1)).val.app (op W.unop.left)).hom x) y
  have hcL := localizedHomEvaluation_curry R K L M n (p + q + 1) p (q + 1)
    (p + q + (n + 1)) (by omega) (by omega) (p + n) rfl U s W x
    (((L.d q (q + 1)).val.app (op W.unop.left)).hom y)
  have hcD := localizedHomEvaluation_curry R K L M (n + 1) (p + q) p q
    (p + q + (n + 1)) rfl rfl (p + (n + 1)) rfl U
    ((((homComplex (R := R) K (homComplex (R := R) L M)).d n (n + 1)).val.app U).hom s)
    W x y
  refine hcD.trans ?_
  refine Eq.trans ?_ (congrArg₂ (fun a b => a - b)
    (congrArg₂ (fun a b => a - b)
      (congrArg ((M.d (p + q + n) (p + q + (n + 1))).val.app
        (op W.unop.left)).hom hc.symm)
      (congrArg (fun z => (n.negOnePow : ℤ) • z) hcK.symm))
    (congrArg (fun z => (n.negOnePow : ℤ) • (p.negOnePow : ℤ) • z) hcL.symm))
  have ho := localizedHomProjection_d R K (homComplex (R := R) L M)
    n (n + 1) p (p + (n + 1)) (p + n) (p + 1) rfl rfl rfl (by omega) U s W x
  let e := localizedHomSectionEvaluation R
    (homTensorProjection R L M (p + (n + 1)) q (p + q + (n + 1)) (by omega))
    (op W.unop.left) (op (Over.mk (𝟙 W.unop.left))) y
  have hoe := congrArg e ho
  simp only [map_sub, map_zsmul] at hoe
  refine hoe.trans ?_
  let sx := localizedHomEvaluation R U s W x
    (homTensorProjection R K (homComplex (R := R) L M) n p (p + n) rfl)
  have hi := localizedHomProjection_d R L M (p + n) (p + (n + 1))
    q (p + q + (n + 1)) (p + q + n) (q + 1) (by omega) (by omega)
      (by omega) (by omega) (op W.unop.left) sx (op (Over.mk (𝟙 W.unop.left))) y
  refine (congrArg (fun z => z - (n.negOnePow : ℤ) • e
    (localizedHomEvaluation R U s W
      (((K.d p (p + 1)).val.app (op W.unop.left)).hom x)
      (homTensorProjection R K (homComplex (R := R) L M) n (p + 1)
        (p + (n + 1)) (by omega)))) hi).trans ?_
  dsimp only [e, sx, localizedHomSectionEvaluation, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Over.mk, Over.left, CostructuredArrow.mk]
  simp only [Int.negOnePow_add, Units.val_mul, mul_smul]
  rw [smul_comm (p.negOnePow : ℤ) (n.negOnePow : ℤ)]
  abel

end CategoryTheory
