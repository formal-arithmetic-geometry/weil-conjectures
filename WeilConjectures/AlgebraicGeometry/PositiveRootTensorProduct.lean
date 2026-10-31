/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherenceSupplement

/-! # Multiplication of unshifted positive root powers

Source: coefficient-twist tensor-power conventions and orientation comparison conventions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u c v r
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open SheafOfModules
namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted Padic
  SheafOfModules.monoidalCategory

section PowerConstruction
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  (L : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

private def powerProduct : (d e : ℕ) →
    (siteSheafTensorRight (scalarTensorPower R L e)).obj (scalarTensorPower R L d) ≅
      scalarTensorPower R L (d + e)
  | _, 0 => scalarTensorRightUnitor R _
  | 0, 1 => scalarTensorLeftUnitor R _
  | _ + 1, 1 => Iso.refl _
  | d, e + 2 =>
    (scalarTensorAssociatorIso R (scalarTensorPower R L d)
      (scalarTensorPower R L (e + 1)) L).symm ≪≫
        (siteSheafTensorRight L).mapIso (powerProduct d (e + 1))

private theorem assoc_inv_pure
    (M N P : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) (z : P.val.obj U) :
    (scalarTensorAssociatorIso R M N P).inv.val.app U
      (siteSheafTensorTmul M _ U x (siteSheafTensorTmul N P U y z)) =
    siteSheafTensorTmul _ P U (siteSheafTensorTmul M N U x y) z := by
  erw [← scalarTensorAssociatorIso_tmul R M N P U x y z]
  exact congrArg (fun f ↦ f.val.app U
    (siteSheafTensorTmul _ P U (siteSheafTensorTmul M N U x y) z))
      (scalarTensorAssociatorIso R M N P).hom_inv_id
end PowerConstruction

section RootFormulas
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (X : Scheme.{u})

open FrobeniusCoefficientTwists

private theorem generator_smul (U : X.ProEtᵒᵖ)
    (a b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
    (d : ℕ) (x : Fin d → (purTwistZlOne X l).obj.obj U) :
    a • generator l E X U b d x = generator l E X U (a * b) d x := by
  induction d using Nat.twoStepInduction with
  | zero => rfl
  | one => exact (mul_smul a b _).symm
  | more d _ ih =>
    let M := positiveLine l E X (d + 1)
    let L := purTwistIntegralModule X l E
    let z := purTwistIntegralTensor X l E U 1 (x (Fin.last (d + 1)))
    let T := siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) M L U
    exact (scalarTensorTmul_smul_first
      (R := completedIntegralCommRingSheafUnrestricted l E X) M L U a
        (generator l E X U b (d + 1) (fun i ↦ x i.castSucc)) z).symm.trans
      (congrArg (fun w ↦ T w z) (ih (fun i ↦ x i.castSucc)))

private theorem generator_snoc (U : X.ProEtᵒᵖ)
    (a : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
    (d : ℕ) (x : Fin (d + 1) → (purTwistZlOne X l).obj.obj U)
    (z : (purTwistZlOne X l).obj.obj U) :
    generator l E X U a (d + 2) (Fin.snoc x z) =
      siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) _ _ U (generator l E X U a (d + 1) x)
        (purTwistIntegralTensor X l E U 1 z) := by
  simp only [generator, Fin.snoc_castSucc, Fin.snoc_last]

private theorem powerProduct_generator (d e : ℕ) (U : X.ProEtᵒᵖ)
    (a b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
    (x : Fin d → (purTwistZlOne X l).obj.obj U)
    (y : Fin e → (purTwistZlOne X l).obj.obj U) :
    (powerProduct (completedIntegralCommRingSheafUnrestricted l E X)
      (purTwistIntegralModule X l E) d e).hom.val.app U
      (siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) _ _ U (generator l E X U a d x)
        (generator l E X U b e y)) =
    generator l E X U (a * b) (d + e) (Fin.append x y) := by
  let A := completedIntegralCommRingSheafUnrestricted l E X
  let L := purTwistIntegralModule X l E
  let P := positiveLine l E X
  let T (i j : ℕ) := siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
    (A := A) (P i) (P j) U
  induction e using Nat.twoStepInduction generalizing d with
  | zero =>
    have hxy : Fin.append x y = x := Fin.append_right_nil x y rfl
    exact (scalarTensorRightUnitor_tmul A (P d) U (generator l E X U a d x) b).trans
      ((generator_smul l E X U b a d x).trans
        ((congrArg (fun c ↦ generator l E X U c d x)
          (completedIntegralCoefficient_mul_commUnrestricted l E X U b a)).trans
            (congrArg (fun z ↦ generator l E X U (a * b) d z) hxy).symm))
  | one =>
    cases d with
    | zero =>
      exact (scalarTensorLeftUnitor_tmul A L U a (generator l E X U b 1 y)).trans
        (generator_smul l E X U a b 1 y)
    | succ d =>
      let z := purTwistIntegralTensor X l E U 1 (y 0)
      calc
        _ = b • T (d + 1) 1 (generator l E X U a (d + 1) x) z :=
          scalarTensorTmul_smul_second (R := A) (P (d + 1)) (P 1) U b _ z
        _ = T (d + 1) 1 (b • generator l E X U a (d + 1) x) z :=
          (scalarTensorTmul_smul_first (R := A) (P (d + 1)) (P 1) U b _ z).symm
        _ = T (d + 1) 1 (generator l E X U (b * a) (d + 1) x) z :=
          congrArg (fun w ↦ T (d + 1) 1 w z) (generator_smul l E X U b a (d + 1) x)
        _ = generator l E X U (b * a) (d + 2) (Fin.snoc x (y 0)) :=
          (generator_snoc l E X U (b * a) d x (y 0)).symm
        _ = generator l E X U (a * b) (d + 1 + 1) (Fin.append x y) :=
          congrArg₂ (fun c w ↦ generator l E X U c (d + 2) w)
            (completedIntegralCoefficient_mul_commUnrestricted l E X U b a)
            (Fin.append_right_eq_snoc x y).symm
  | more e _ ih =>
    let z := purTwistIntegralTensor X l E U 1 (y (Fin.last (e + 1)))
    let q := powerProduct A L d (e + 1)
    let Q := (siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := A) (P (e + 1))).obj (P d)
    let S := siteSheafTensorTmul.{u + 1, u, u + 1, u + 1} (A := A) Q L U
    let F := ((siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := A) L).map q.hom).val.app U
    let I := (scalarTensorAssociatorIso A (P d) (P (e + 1)) L).inv.val.app U
    have hy : generator l E X U b (e + 2) y =
        T (e + 1) 1 (generator l E X U b (e + 1) (Fin.init y)) z :=
      (congrArg (fun w ↦ generator l E X U b (e + 2) w)
        (Fin.snoc_init_self y).symm).trans
          (generator_snoc l E X U b e (Fin.init y) (y (Fin.last (e + 1))))
    have hxy : Fin.append x y =
        Fin.snoc (Fin.append (m := d) (n := e + 1) x (Fin.init y)) (y (Fin.last (e + 1))) :=
      (congrArg (fun w ↦ Fin.append x w) (Fin.snoc_init_self y).symm).trans
        (Fin.append_snoc x (Fin.init y) (y (Fin.last (e + 1))))
    calc
      _ = F (I (T d (e + 2) (generator l E X U a d x)
          (T (e + 1) 1 (generator l E X U b (e + 1) (Fin.init y)) z))) :=
        congrArg (fun w ↦ F (I (T d (e + 2) (generator l E X U a d x) w))) hy
      _ = F (S (T d (e + 1) (generator l E X U a d x)
          (generator l E X U b (e + 1) (Fin.init y))) z) :=
        congrArg (fun w ↦ F w) (assoc_inv_pure A (P d) (P (e + 1)) L U
          (generator l E X U a d x) (generator l E X U b (e + 1) (Fin.init y)) z)
      _ = T (d + (e + 1)) 1 (q.hom.val.app U
          (T d (e + 1) (generator l E X U a d x)
            (generator l E X U b (e + 1) (Fin.init y)))) z :=
        scalarTensor_first_tmul (R := A) q.hom L U _ z
      _ = T (d + (e + 1)) 1
          (generator l E X U (a * b) (d + (e + 1))
            (Fin.append (m := d) (n := e + 1) x (Fin.init y))) z :=
        congrArg (fun w ↦ T (d + (e + 1)) 1 w z) (ih d x (Fin.init y))
      _ = generator l E X U (a * b) (d + e + 2)
          (Fin.snoc (Fin.append (m := d) (n := e + 1) x (Fin.init y)) (y (Fin.last (e + 1)))) :=
        (generator_snoc l E X U (a * b) (d + e)
          (Fin.append (m := d) (n := e + 1) x (Fin.init y)) (y (Fin.last (e + 1)))).symm
      _ = generator l E X U (a * b) (d + (e + 2)) (Fin.append x y) :=
        congrArg (fun w ↦ generator l E X U (a * b) (d + (e + 2)) w) hxy.symm

private theorem rootTensor_restrict {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (purTwistZlOne X l).obj.obj U) :
    (purTwistIntegralModule X l E).val.map f (purTwistIntegralTensor X l E U 1 x) =
      purTwistIntegralTensor X l E V 1 ((purTwistZlOne X l).obj.map f x) := by
  change (purTwistIntegralOne X l E).val.map f
    (purTwistIntegralTensor X l E U 1 x) =
      purTwistIntegralTensor X l E V 1 ((purTwistZlModule X l).val.map f x)
  have h := scalarExtensionSection_naturality.{u + 1, u, u + 1, u + 1}
    (purTwistConstantIntegersMap X l E)
    ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (purTwistZlCompletionMap X l))).obj (purTwistZlModule X l)) f 1 x
  rw [map_one] at h
  exact h

private theorem generator_restrict {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (a : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
    (d : ℕ) (x : Fin d → (purTwistZlOne X l).obj.obj U) :
    (positiveLine l E X d).val.map f (generator l E X U a d x) =
      generator l E X V
        ((completedIntegralCoefficientSheafUnrestricted l E X).obj.map f a) d
        (fun i ↦ (purTwistZlOne X l).obj.map f (x i)) := by
  induction d using Nat.twoStepInduction with
  | zero => rfl
  | one =>
    change (purTwistIntegralModule X l E).val.map f
      (@SMul.smul _ _ (purTwistIntegralAction X l E U).toSMul a
            (purTwistIntegralTensor X l E U 1 (x 0))) = _
    erw [(purTwistIntegralModule X l E).val.map_smul, rootTensor_restrict]
    rfl
  | more d _ ih =>
    let M := positiveLine l E X (d + 1)
    let L := purTwistIntegralModule X l E
    exact (scalarTensorTmul_naturality
      (R := completedIntegralCommRingSheafUnrestricted l E X) M L f
        (generator l E X U a (d + 1) (fun i ↦ x i.castSucc))
        (purTwistIntegralTensor X l E U 1 (x (Fin.last (d + 1))))).trans
      (congrArg₂ (siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) M L V) (ih (fun i ↦ x i.castSucc))
        (rootTensor_restrict l E X f (x (Fin.last (d + 1)))))

private def generatorSpan (d : ℕ) (U : X.ProEtᵒᵖ) :
    Submodule ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
      ((positiveLine l E X d).val.obj U) :=
  Submodule.span _ (Set.range (fun q :
    ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U) ×
      (Fin d → (purTwistZlOne X l).obj.obj U) ↦ generator l E X U q.1 d q.2))

private theorem generatorSpan_restrict (d : ℕ) {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (positiveLine l E X d).val.obj U) (hx : x ∈ generatorSpan l E X d U) :
    (positiveLine l E X d).val.map f x ∈ generatorSpan l E X d V := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, z⟩, rfl⟩ := hx
    erw [generator_restrict]
    exact Submodule.subset_span ⟨(_, _), rfl⟩
  | zero => simpa only [map_zero] using (generatorSpan l E X d V).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    erw [(positiveLine l E X d).val.map_smul]
    exact Submodule.smul_mem _ _ hx

private def spanSieve (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (positiveLine l E X d).val.obj U) : Sieve U.unop where
  arrows V f := (positiveLine l E X d).val.map f.op x ∈ generatorSpan l E X d (op V)
  downward_closed := by
    intro V W f hf g
    simpa only [op_comp, PresheafOfModules.map_comp_apply] using
      generatorSpan_restrict l E X d g.op _ hf

private def localSpan (d : ℕ) (U : X.ProEtᵒᵖ) :
    Submodule ((completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
      ((positiveLine l E X d).val.obj U) where
  carrier := {x | spanSieve l E X d U x ∈ ProEt.topology X U.unop}
  zero_mem' := by
    apply (ProEt.topology X).superset_covering _ ((ProEt.topology X).top_mem _)
    intro V f _
    change (positiveLine l E X d).val.map f.op 0 ∈ generatorSpan l E X d (op V)
    simpa only [map_zero] using (generatorSpan l E X d (op V)).zero_mem
  add_mem' := by
    intro x y hx hy
    apply (ProEt.topology X).superset_covering _
      ((ProEt.topology X).intersection_covering hx hy)
    intro V f hf
    change (positiveLine l E X d).val.map f.op (x + y) ∈ _
    simpa only [map_add] using (generatorSpan l E X d (op V)).add_mem hf.1 hf.2
  smul_mem' := by
    intro a x hx
    apply (ProEt.topology X).superset_covering _ hx
    intro V f hf
    change (positiveLine l E X d).val.map f.op (a • x) ∈ _
    erw [(positiveLine l E X d).val.map_smul]
    exact Submodule.smul_mem _ _ hf

private theorem span_mem_localSpan (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (positiveLine l E X d).val.obj U) (hx : x ∈ generatorSpan l E X d U) :
    x ∈ localSpan l E X d U := by
  apply (ProEt.topology X).superset_covering _ ((ProEt.topology X).top_mem _)
  intro V f _
  exact generatorSpan_restrict l E X d f.op x hx

private theorem localSpan_descent (d : ℕ)
    (P : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (φ : P ⟶ (positiveLine l E X d).val.presheaf)
    [Presheaf.IsLocallySurjective (ProEt.topology X) φ]
    (h : ∀ U t, φ.app U t ∈ localSpan l E X d U)
    (U : X.ProEtᵒᵖ) (x : (positiveLine l E X d).val.obj U) :
    x ∈ localSpan l E X d U := by
  apply (ProEt.topology X).transitive (Presheaf.imageSieve_mem _ φ x)
  rintro V f ⟨t, ht⟩
  change φ.app (op V) t = (positiveLine l E X d).val.map f.op x at ht
  have he : (spanSieve l E X d U x).pullback f =
      spanSieve l E X d (op V) (φ.app (op V) t) := by
    ext W g
    change ((positiveLine l E X d).val.map (g ≫ f).op x ∈ _) ↔ _
    erw [op_comp, PresheafOfModules.map_comp_apply, ← ht]
    rfl
  erw [he]
  exact h (op V) t

private theorem tensor_mem_span (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (positiveLine l E X (d + 1)).val.obj U)
    (y : (positiveLine l E X 1).val.obj U)
    (hx : x ∈ generatorSpan l E X (d + 1) U)
    (hy : y ∈ generatorSpan l E X 1 U) :
    siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) _ _ U x y ∈
      generatorSpan l E X (d + 2) U := by
  induction hx using Submodule.span_induction with
  | zero =>
    simpa only [scalarTensorTmul_zero_first] using (generatorSpan l E X (d + 2) U).zero_mem
  | add x x' _ _ hx hx' =>
    simpa only [scalarTensorTmul_add_first] using Submodule.add_mem _ hx hx'
  | smul a x _ hx =>
    exact (congrArg (fun z ↦ z ∈ generatorSpan l E X (d + 2) U)
      (scalarTensorTmul_smul_first
        (R := completedIntegralCommRingSheafUnrestricted l E X)
        (positiveLine l E X (d + 1)) (positiveLine l E X 1) U a x y)).mpr
          (Submodule.smul_mem _ a hx)
  | mem x hx =>
    obtain ⟨⟨a, z⟩, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | zero =>
      simpa only [siteSheafTensorTmul, TensorProduct.tmul_zero, map_zero] using
        (generatorSpan l E X (d + 2) U).zero_mem
    | add y y' _ _ hy hy' =>
      simpa only [siteSheafTensorTmul, TensorProduct.tmul_add, map_add] using
        Submodule.add_mem _ hy hy'
    | smul b y _ hy =>
      exact (congrArg (fun z ↦ z ∈ generatorSpan l E X (d + 2) U)
        (scalarTensorTmul_smul_second
          (R := completedIntegralCommRingSheafUnrestricted l E X)
          (positiveLine l E X (d + 1)) (positiveLine l E X 1) U b
          (generator l E X U a (d + 1) z) y)).mpr (Submodule.smul_mem _ b hy)
    | mem y hy =>
      obtain ⟨⟨b, w⟩, rfl⟩ := hy
      exact (congrArg (fun t ↦ t ∈ generatorSpan l E X (d + 2) U)
        (scalarTensorTmul_smul_second
          (R := completedIntegralCommRingSheafUnrestricted l E X)
          (positiveLine l E X (d + 1)) (positiveLine l E X 1) U b
          (generator l E X U a (d + 1) z)
          (purTwistIntegralTensor X l E U 1 (w 0)))).mpr
        (Submodule.smul_mem _ b (Submodule.subset_span
          ⟨(a, Fin.snoc z (w 0)), generator_snoc l E X U a d z (w 0)⟩))

private theorem tensor_mem_localSpan (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (positiveLine l E X (d + 1)).val.obj U)
    (y : (positiveLine l E X 1).val.obj U)
    (hx : x ∈ localSpan l E X (d + 1) U) (hy : y ∈ localSpan l E X 1 U) :
    siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) _ _ U x y ∈
      localSpan l E X (d + 2) U := by
  apply (ProEt.topology X).superset_covering _
    ((ProEt.topology X).intersection_covering hx hy)
  intro V f hf
  exact (congrArg (fun z ↦ z ∈ generatorSpan l E X (d + 2) (op V))
    (scalarTensorTmul_naturality
      (R := completedIntegralCommRingSheafUnrestricted l E X)
      (positiveLine l E X (d + 1)) (positiveLine l E X 1) f.op x y)).mpr
        (tensor_mem_span l E X d (op V) _ _ hf.1 hf.2)

private theorem integralTensor_generator (U : X.ProEtᵒᵖ)
    (b : (purTwistIntegralConstant X l E).obj.obj U)
    (x : (purTwistZlOne X l).obj.obj U) :
    purTwistIntegralTensor X l E U b x =
      generator l E X U ((purTwistIntegralCompletionMap X l E).hom.app U b) 1
        (fun _ ↦ x) := by
  have h := (purTwistIntegralAction_existsUnique X l E).exists.choose_spec.2.1 U b
    (purTwistIntegralTensor X l E U 1 x)
  change _ = @SMul.smul _ _ (purTwistIntegralAction X l E U).toSMul _ _
  erw [show @SMul.smul _ _ (purTwistIntegralAction X l E U).toSMul _ _ = _ from h]
  dsimp only [purTwistIntegralTensor]
  erw [← map_smul]
  congr 1
  let N := ((SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistZlCompletionMap X l))).obj (purTwistZlModule X l))
  simpa only [mul_one] using
    (ModuleCat.ExtendScalars.smul_tmul
      ((purTwistConstantIntegersMap X l E).hom.app U).hom
      (M := N.val.obj U) b 1 x).symm

private theorem first_locally_span (U : X.ProEtᵒᵖ)
    (x : (positiveLine l E X 1).val.obj U) : x ∈ localSpan l E X 1 U := by
  let P := changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
    (purTwistConstantIntegersMap X l E)
    ((SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistZlCompletionMap X l))).obj (purTwistZlModule X l))
  let φ := (PresheafOfModules.toPresheaf _).map
    (scalarSheafificationUnit (J := ProEt.topology X) P)
  have : Presheaf.IsLocallySurjective (ProEt.topology X) φ := by
    change Presheaf.IsLocallySurjective _ (toSheafify _ P.presheaf)
    infer_instance
  apply localSpan_descent l E X 1 P.presheaf φ _ U x
  intro V t
  induction t using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using (localSpan l E X 1 V).zero_mem
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | tmul b z =>
    apply span_mem_localSpan
    change purTwistIntegralTensor X l E V b z ∈ _
    erw [integralTensor_generator]
    exact Submodule.subset_span ⟨(_, _), rfl⟩


private theorem generator_locally_span (d : ℕ) (U : X.ProEtᵒᵖ)
    (x : (positiveLine l E X d).val.obj U) : x ∈ localSpan l E X d U := by
  induction d using Nat.twoStepInduction generalizing U with
  | zero =>
    apply span_mem_localSpan
    exact Submodule.subset_span ⟨(x, Fin.elim0), rfl⟩
  | one => exact first_locally_span l E X U x
  | more d _ hd =>
    let P := siteTensorPresheaf (positiveLine l E X (d + 1)).val
      (purTwistIntegralModule X l E).val
    let φ := (PresheafOfModules.toPresheaf _).map
      (scalarSheafificationUnit (J := ProEt.topology X) P)
    have : Presheaf.IsLocallySurjective (ProEt.topology X) φ := by
      change Presheaf.IsLocallySurjective _ (toSheafify _ P.presheaf)
      infer_instance
    apply localSpan_descent l E X (d + 2) P.presheaf φ _ U x
    intro V t
    induction t using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using (localSpan l E X (d + 2) V).zero_mem
    | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
    | tmul a b =>
      apply tensor_mem_localSpan l E X d V a b (hd V a)
      -- The degree-one case is independent of the induction index.
      exact first_locally_span l E X V b

private theorem pairs_mem_span_ext (d e : ℕ)
    (H : integralTowerModules l E X)
    (f g : (siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) (positiveLine l E X e)).obj
      (positiveLine l E X d) ⟶ H)
    (h : ∀ U a b x y, f.val.app U
      (siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) _ _ U (generator l E X U a d x)
        (generator l E X U b e y)) =
      g.val.app U (siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) _ _ U (generator l E X U a d x)
        (generator l E X U b e y)))
    (U : X.ProEtᵒᵖ) (p : (positiveLine l E X d).val.obj U)
    (q : (positiveLine l E X e).val.obj U)
    (hp : p ∈ generatorSpan l E X d U) (hq : q ∈ generatorSpan l E X e U) :
    f.val.app U (siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) _ _ U p q) =
      g.val.app U (siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) _ _ U p q) := by
  induction hp using Submodule.span_induction with
  | zero => simp only [scalarTensorTmul_zero_first, map_zero]
  | add x y _ _ hx hy => simp only [scalarTensorTmul_add_first, map_add, hx, hy]
  | smul a x _ hx =>
    let t := siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X)
      (positiveLine l E X d) (positiveLine l E X e) U x q
    have ht := scalarTensorTmul_smul_first
      (R := completedIntegralCommRingSheafUnrestricted l E X)
      (positiveLine l E X d) (positiveLine l E X e) U a x q
    exact (congrArg (fun z ↦ f.val.app U z) ht).trans
      (((f.val.app U).hom.map_smul a t).trans
        ((congrArg (fun z ↦ a • z) hx).trans
          (((g.val.app U).hom.map_smul a t).symm.trans
            (congrArg (fun z ↦ g.val.app U z) ht).symm)))
  | mem p hp =>
    obtain ⟨⟨a, x⟩, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | zero => simp only [siteSheafTensorTmul, TensorProduct.tmul_zero, map_zero]
    | add y z _ _ hy hz =>
      simp only [siteSheafTensorTmul, TensorProduct.tmul_add, map_add] at hy hz ⊢
      erw [hy, hz]
    | smul b y _ hy =>
      let t := siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
        (A := completedIntegralCommRingSheafUnrestricted l E X)
        (positiveLine l E X d) (positiveLine l E X e) U
        (generator l E X U a d x) y
      have ht := scalarTensorTmul_smul_second
        (R := completedIntegralCommRingSheafUnrestricted l E X)
        (positiveLine l E X d) (positiveLine l E X e) U b
        (generator l E X U a d x) y
      exact (congrArg (fun z ↦ f.val.app U z) ht).trans
        (((f.val.app U).hom.map_smul b t).trans
          ((congrArg (fun z ↦ b • z) hy).trans
            (((g.val.app U).hom.map_smul b t).symm.trans
              (congrArg (fun z ↦ g.val.app U z) ht).symm)))
    | mem q hq =>
      obtain ⟨⟨b, y⟩, rfl⟩ := hq
      exact h U a b x y

private theorem root_pairs_ext (d e : ℕ)
    (H : integralTowerModules l E X)
    (f g : (siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) (positiveLine l E X e)).obj
      (positiveLine l E X d) ⟶ H)
    (h : ∀ U a b x y, f.val.app U
      (siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) _ _ U (generator l E X U a d x)
        (generator l E X U b e y)) =
      g.val.app U (siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
      (A := completedIntegralCommRingSheafUnrestricted l E X) _ _ U (generator l E X U a d x)
        (generator l E X U b e y))) : f = g := by
  apply scalarTensor_hom_ext
  intro U p q
  apply H.isSheaf.isSeparated _ _ ((ProEt.topology X).intersection_covering
    (generator_locally_span l E X d U p) (generator_locally_span l E X e U q))
  intro V i hi
  change H.val.map i.op (f.val.app U _) = H.val.map i.op (g.val.app U _)
  let t := siteSheafTensorTmul.{u + 1, u, u + 1, u + 1}
    (A := completedIntegralCommRingSheafUnrestricted l E X)
    (positiveLine l E X d) (positiveLine l E X e) U p q
  have ht := scalarTensorTmul_naturality
    (R := completedIntegralCommRingSheafUnrestricted l E X)
    (positiveLine l E X d) (positiveLine l E X e) i.op p q
  exact (PresheafOfModules.naturality_apply f.val i.op t).symm.trans
    ((congrArg (fun z ↦ f.val.app (op V) z) ht).trans
      ((pairs_mem_span_ext l E X d e H f g h (op V) _ _ hi.1 hi.2).trans
        ((congrArg (fun z ↦ g.val.app (op V) z) ht).symm.trans
          (PresheafOfModules.naturality_apply g.val i.op t))))

end RootFormulas

/-- Multiplication of the actual module sheaves of positive completed root powers.
Source: `def-coefficient-twists-detailed`, positive tensor powers, and
`def-sf-orientation`, coefficient-line multiplication conventions.
(blueprint: lem-sf-positive-root-tensor-product).
Proof: at exponent zero use the scalar tensor unitors. For positive exponents,
reassociate the ordered tensor factors, splitting after the first d roots. The
inverse reassociates in the opposite direction. Tensor balancing moves the scalar
b from the second block into the first, giving the scalar ab, and concatenation
preserves the order of all roots. The unitors and associators are inverse maps,
so this is an isomorphism. Pure tensors generate each presheaf tensor product;
after sheafification they generate locally. The integral first-line tensor
construction is likewise locally generated by scalar/root tensors. Induction on
the two powers therefore shows that the displayed formulas determine the map,
and hence the isomorphism, uniquely. The same unit formulas cover d=0 or e=0,
including d=e=0, and sheaf separation covers the empty scheme as well. -/
theorem positiveRootTensorProduct_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (d e : ℕ) :
    ∃! m : (SheafOfModules.monoidalCategory
        (completedIntegralCommRingSheafUnrestricted l E X)).tensorObj
          (FrobeniusCoefficientTwists.positiveLine l E X d)
          (FrobeniusCoefficientTwists.positiveLine l E X e) ≅
        FrobeniusCoefficientTwists.positiveLine l E X (d + e),
      ∀ (U : X.ProEtᵒᵖ)
        (a b : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
        (x : Fin d → (purTwistZlOne X l).obj.obj U)
        (y : Fin e → (purTwistZlOne X l).obj.obj U),
        m.hom.val.app U
          (SheafOfModules.ScalarHomOrdinary.pure
            (completedIntegralCommRingSheafUnrestricted l E X) _ _ U
            (FrobeniusCoefficientTwists.generator l E X U a d x)
            (FrobeniusCoefficientTwists.generator l E X U b e y)) =
          FrobeniusCoefficientTwists.generator l E X U (a * b) (d + e)
            (Fin.addCases x y) := by
  let A := completedIntegralCommRingSheafUnrestricted l E X
  let L := purTwistIntegralModule X l E
  let M := FrobeniusCoefficientTwists.positiveLine l E X d
  let N := FrobeniusCoefficientTwists.positiveLine l E X e
  let t := SheafOfModules.ScalarHomOrdinary.tensorIsoSite A M N
  let p := powerProduct A L d e
  let m := t ≪≫ p
  refine ⟨m, ?_, ?_⟩
  · intro U a b x y
    change p.hom.val.app U (t.hom.val.app U _) = _
    exact (congrArg (fun z ↦ p.hom.val.app U z)
      (SheafOfModules.ScalarHomOrdinary.tensorIsoSite_pure A M N U
        (FrobeniusCoefficientTwists.generator l E X U a d x)
        (FrobeniusCoefficientTwists.generator l E X U b e y))).trans
          (powerProduct_generator l E X d e U a b x y)
  · intro m' hm'
    apply Iso.ext
    apply (cancel_epi t.inv).mp
    calc
      t.inv ≫ m'.hom = p.hom := by
        apply root_pairs_ext l E X d e _
        intro U a b x y
        change m'.hom.val.app U (t.inv.val.app U _) = p.hom.val.app U _
        exact ((congrArg (fun z ↦ m'.hom.val.app U z)
          (SheafOfModules.ScalarHomOrdinary.tensorIsoSite_inv_pure A M N U
            (FrobeniusCoefficientTwists.generator l E X U a d x)
            (FrobeniusCoefficientTwists.generator l E X U b e y))).trans
              (hm' U a b x y)).trans
                (powerProduct_generator l E X d e U a b x y).symm
      _ = t.inv ≫ m.hom := by
        change p.hom = t.inv ≫ (t.hom ≫ p.hom)
        rw [← Category.assoc, t.inv_hom_id, Category.id_comp]

end WeilConjectures
