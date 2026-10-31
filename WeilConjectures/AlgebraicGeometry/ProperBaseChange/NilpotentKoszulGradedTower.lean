/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicKoszulCompletion
public import Mathlib.CategoryTheory.Functor.OfSequence
import all WeilConjectures.AlgebraicGeometry.Koszul.KoszulQuotientLimit
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicKoszulCompletion

/-! # The graded nilpotent Koszul tower

Source: proper base change blueprint, order 1328, proof sentences three through five.
(blueprint: lem-weil-pbc-nilpotent-koszul-graded-tower).
-/

@[expose] public section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme
attribute [local instance] koszulConstantFunctor_preservesZero

variable (B : Type t) [CommRing B] (r : ℕ) (b : Fin r → B)
private theorem generator_single (j : Fin r) (c : ULift.{t + 1} B) :
    koszulPowerGenerator B r b (Finsupp.single j c) =
      Finsupp.single j (c * ULift.up (b j)) := by
  simp [koszulPowerGenerator, Finsupp.linearCombination_single]
private theorem generator_pow_single (k : ℕ) (j : Fin r) (c : ULift.{t + 1} B) :
    (koszulPowerGenerator B r b ^ k) (Finsupp.single j c) =
      Finsupp.single j (c * ULift.up (b j ^ k)) := by
  induction k generalizing c with
  | zero =>
    simp only [pow_zero, Module.End.one_apply]
    congr 1
    apply ULift.ext
    simp
  | succ k ih =>
    rw [pow_succ]
    change (koszulPowerGenerator B r b ^ k)
      (koszulPowerGenerator B r b (Finsupp.single j c)) = _
    rw [generator_single, ih]
    congr 1
    apply ULift.ext
    simp [pow_succ, mul_assoc, mul_comm]
private theorem generator_pow_zero (a : ℕ) (hb : ∀ j, b j ^ a = 0) :
    koszulPowerGenerator B r b ^ a = 0 := by
  apply Finsupp.lhom_ext
  intro j c
  change (koszulPowerGenerator B r b ^ a) (Finsupp.single j c) = 0
  rw [generator_pow_single, hb]
  change Finsupp.single j (c * 0) = 0
  simp
private theorem exterior_map_pow (g : (Fin r →₀ ULift.{t + 1} B) →ₗ[ULift.{t + 1} B]
    (Fin r →₀ ULift.{t + 1} B)) (q a : ℕ) :
    exteriorPower.map q (g ^ a) = exteriorPower.map q g ^ a := by
  induction a with
  | zero =>
    change exteriorPower.map q LinearMap.id = LinearMap.id
    exact exteriorPower.map_id
  | succ a ih =>
    rw [pow_succ, pow_succ]
    change exteriorPower.map q ((g ^ a).comp g) =
      (exteriorPower.map q g ^ a).comp (exteriorPower.map q g)
    rw [exteriorPower.map_comp, ih]
private theorem exterior_map_zero (q : ℕ) (hq : 0 < q) :
    exteriorPower.map q (0 : (Fin r →₀ ULift.{t + 1} B) →ₗ[ULift.{t + 1} B]
      (Fin r →₀ ULift.{t + 1} B)) = 0 := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [exteriorPower.map_comp_ιMulti, AlternatingMap.compLinearMap_apply,
    LinearMap.zero_compAlternatingMap, AlternatingMap.zero_apply]
  change (exteriorPower.ιMulti (ULift.{t + 1} B) q
    (M := Fin r →₀ ULift.{t + 1} B)) (fun _ ↦ 0) = 0
  exact (exteriorPower.ιMulti (ULift.{t + 1} B) q).map_coord_zero ⟨0, hq⟩ rfl

open CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_jump (n k q : ℕ) :
    let K := fun m ↦ ExteriorAlgebra.koszulComplex (ULift.{t + 1} B) r
      (fun j ↦ ULift.up (b j ^ (m + 1)))
    let e := fun m ↦ (K m).extendXIso ComplexShape.embeddingDownNat (i := q) rfl
    let T := Functor.ofOpSequence (koszulPowerTransition B r b)
    (T.map (homOfLE (Nat.le_add_right n k)).op).f
      (ComplexShape.embeddingDownNat.f q) =
      (e (n + k)).hom ≫ ModuleCat.ofHom
        (exteriorPower.map q (koszulPowerGenerator B r b ^ k)) ≫ (e n).inv := by
  dsimp only
  let K := fun m ↦ ExteriorAlgebra.koszulComplex (ULift.{t + 1} B) r
    (fun j ↦ ULift.up (b j ^ (m + 1)))
  let e := fun m ↦ (K m).extendXIso ComplexShape.embeddingDownNat (i := q) rfl
  let T := Functor.ofOpSequence (koszulPowerTransition B r b)
  change (T.map _).f _ = (e (n + k)).hom ≫ _ ≫ (e n).inv
  have hstep (m : ℕ) : (koszulPowerTransition B r b m).f (ComplexShape.embeddingDownNat.f q) =
      (e (m + 1)).hom ≫ ModuleCat.ofHom
        (exteriorPower.map q (koszulPowerGenerator B r b)) ≫ (e m).inv := by
    dsimp only [koszulPowerTransition]
    exact HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat rfl
  induction k with
  | zero =>
    have hm : (homOfLE (Nat.le_add_right n 0)).op = 𝟙 (op n) := Subsingleton.elim _ _
    rw [hm]
    erw [T.map_id]
    rw [HomologicalComplex.id_f, pow_zero]
    change 𝟙 _ = (e n).hom ≫ ModuleCat.ofHom (exteriorPower.map q LinearMap.id) ≫ (e n).inv
    rw [exteriorPower.map_id]
    change 𝟙 _ = (e n).hom ≫ 𝟙 _ ≫ (e n).inv
    rw [Category.id_comp, Iso.hom_inv_id]
  | succ k ih =>
    have hm : (homOfLE (Nat.le_add_right n (k + 1))).op =
        (homOfLE (Nat.le_succ (n + k))).op ≫
          (homOfLE (Nat.le_add_right n k)).op := Subsingleton.elim _ _
    rw [hm, T.map_comp, HomologicalComplex.comp_f, ih]
    dsimp only [T]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    erw [hstep]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [pow_succ]
    change _ = _ ≫ ModuleCat.ofHom
      (exteriorPower.map q ((koszulPowerGenerator B r b ^ k).comp
        (koszulPowerGenerator B r b))) ≫ _
    rw [exteriorPower.map_comp, ModuleCat.ofHom_comp]
    simp only [Category.assoc]
    rfl


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_jump_zero (n a : ℕ) (hb : ∀ j, b j ^ a = 0)
    (p : ℤ) (hp : p ≠ 0) :
    ((Functor.ofOpSequence (koszulPowerTransition B r b)).map
      (homOfLE (Nat.le_add_right n a)).op).f p = 0 := by
  cases p with
  | ofNat k =>
    have hk : 0 < k := Nat.pos_of_ne_zero (fun h ↦ hp (by subst k; rfl))
    have hz := HomologicalComplex.isZero_extend_X
      (ExteriorAlgebra.koszulComplex (ULift.{t + 1} B) r
        (fun j ↦ ULift.up (b j ^ (n + a + 1))))
      ComplexShape.embeddingDownNat (k : ℤ) (by
        intro i
        change -(i : ℤ) ≠ (k : ℤ)
        omega)
    exact hz.eq_of_src _ _
  | negSucc k =>
    change ((Functor.ofOpSequence (koszulPowerTransition B r b)).map
      (homOfLE (Nat.le_add_right n a)).op).f
        (ComplexShape.embeddingDownNat.f (k + 1)) = 0
    rw [coefficient_jump, generator_pow_zero B r b a hb,
      exterior_map_zero B r (k + 1) (Nat.succ_pos k)]
    simp only [ModuleCat.ofHom_zero, CategoryTheory.Limits.zero_comp,
      CategoryTheory.Limits.comp_zero]

variable (X : Scheme.{t}) (B : Type t) [CommRing B]
  (r : ℕ) (b : Fin r → B)
  (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ)

private noncomputable def gradedRetraction (m : ℕ) (p : ℤ) :
    (koszulTensor X B r b C m).X p ⟶ C.X p := by
  let := SheafOfModules.monoidalCategory (adicConstantRing X B)
  let := koszulSheafUnitZero_isIso X B r b m
  exact HomologicalComplex.mapBifunctorDesc (fun i j hij ↦
    if hj : j = 0 then by
      subst j
      have hi : i = p := by simpa using hij
      subst i
      exact (C.X p ◁ inv (koszulSheafUnitZero X B r b m)) ≫ (ρ_ (C.X p)).hom
    else 0)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem gradedRetraction_unit (m : ℕ) (p : ℤ) :
    (koszulTensorUnit X B r b C m).f p ≫ gradedRetraction X B r b C m p = 𝟙 _ := by
  let := SheafOfModules.monoidalCategory (adicConstantRing X B)
  let := koszulSheafUnitZero_isIso X B r b m
  dsimp only [koszulTensorUnit, koszulTensorUnitComponent, gradedRetraction]
  rw [Category.assoc, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
  rw [dif_pos rfl]
  rw [← whiskerLeft_comp_assoc, IsIso.hom_inv_id, whiskerLeft_id,
    Category.id_comp, Iso.inv_hom_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem gradedRetraction_step (m : ℕ) (p : ℤ) :
    (koszulTensorTransition X B r b C m).f p ≫ gradedRetraction X B r b C m p =
      gradedRetraction X B r b C (m + 1) p := by
  let := SheafOfModules.monoidalCategory (adicConstantRing X B)
  let := koszulSheafUnitZero_isIso X B r b m
  let := koszulSheafUnitZero_isIso X B r b (m + 1)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  dsimp only [koszulTensorTransition, gradedRetraction]
  rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
  split_ifs with hj
  · subst j
    have hi : i = p := by simpa using hij
    subst i
    dsimp only [HomologicalComplex.id_f, curriedTensor_map_app,
      curriedTensor_obj_map]
    rw [id_whiskerRight]
    erw [Category.id_comp]
    rw [← whiskerLeft_comp_assoc]
    congr 2
    apply (cancel_epi (koszulSheafUnitZero X B r b (m + 1))).1
    rw [← Category.assoc, koszulSheafUnitZero_transition, IsIso.hom_inv_id,
      IsIso.hom_inv_id]
  · exact comp_zero

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_jump (n k : ℕ) :
    letI := SheafOfModules.monoidalCategory (adicConstantRing X B)
    let S := Functor.ofOpSequence (koszulPowerTransition B r b)
    let T := Functor.ofOpSequence (koszulTensorTransition X B r b C)
    T.map (homOfLE (Nat.le_add_right n k)).op =
      HomologicalComplex.mapBifunctorMap (𝟙 C)
        (((koszulConstantFunctor X B).mapHomologicalComplex (.up ℤ)).map
          (S.map (homOfLE (Nat.le_add_right n k)).op)) (curriedTensor _) (.up ℤ) := by
  let := SheafOfModules.monoidalCategory (adicConstantRing X B)
  let S := Functor.ofOpSequence (koszulPowerTransition B r b)
  let T := Functor.ofOpSequence (koszulTensorTransition X B r b C)
  let F := (koszulConstantFunctor X B).mapHomologicalComplex (.up ℤ)
  let T' : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ :=
    { obj := fun n ↦ koszulTensor X B r b C n.unop
      map := fun f ↦ HomologicalComplex.mapBifunctorMap (𝟙 C)
        (F.map (S.map f)) (curriedTensor _) (.up ℤ)
      map_id := fun n ↦ by
        dsimp only [S]
        simp only [CategoryTheory.Functor.map_id]
        dsimp only [HomologicalComplex.mapBifunctorMap]
        simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
          HomologicalComplex₂.total.map_id]
        rfl
      map_comp := fun f g ↦ by
        rw [S.map_comp, F.map_comp]
        dsimp only [HomologicalComplex.mapBifunctorMap]
        simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
          Functor.map_comp, HomologicalComplex₂.total.map_comp] }
  let e : T ⟶ T' := NatTrans.ofOpSequence (fun n ↦ 𝟙 _) (fun n ↦ by
    change T.map _ ≫ 𝟙 _ = 𝟙 _ ≫ T'.map _
    rw [Category.comp_id, Category.id_comp]
    dsimp only [T, T', F]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    dsimp only [S]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    rfl)
  have h := e.naturality (homOfLE (Nat.le_add_right n k)).op
  change T.map _ ≫ 𝟙 _ = 𝟙 _ ≫ T'.map _ at h
  simpa only [Category.comp_id, Category.id_comp] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sheafUnitZero_jump (n k : ℕ) :
    koszulSheafUnitZero X B r b (n + k) ≫
      (((koszulConstantFunctor X B).mapHomologicalComplex (.up ℤ)).map
        ((Functor.ofOpSequence (koszulPowerTransition B r b)).map
          (homOfLE (Nat.le_add_right n k)).op)).f 0 =
      koszulSheafUnitZero X B r b n := by
  let S := Functor.ofOpSequence (koszulPowerTransition B r b)
  let F := (koszulConstantFunctor X B).mapHomologicalComplex (.up ℤ)
  let D := S ⋙ F ⋙ HomologicalComplex.eval _ (.up ℤ) 0
  let u : (Functor.const ℕᵒᵖ).obj (SheafOfModules.unit (adicModuleRing X B)) ⟶ D :=
    NatTrans.ofOpSequence (koszulSheafUnitZero X B r b) (fun n ↦ by
      dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
      rw [Category.id_comp]
      change _ = _ ≫ (F.map (S.map _)).f 0
      dsimp only [S]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact (koszulSheafUnitZero_transition X B r b n).symm)
  have hu := u.naturality (homOfLE (Nat.le_add_right n k)).op
  change 𝟙 _ ≫ koszulSheafUnitZero X B r b n =
    koszulSheafUnitZero X B r b (n + k) ≫ _ at hu
  rw [Category.id_comp] at hu
  exact hu.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The tensor Koszul tower is split proconstant in each graded degree.
The retractions asserted here are graded maps; they need not commute with differentials.

Source: literature/blueprint/main-20261015/blueprint/sec-proper-base-change/
sk-thm-properbasechange/lemma-weil-pbc-adic-completion-reduction.proof.md,
proof sentences three through five.
(blueprint: lem-weil-pbc-nilpotent-koszul-graded-tower).

Proof: project the total tensor in degree p onto its summand with Koszul degree zero,
and identify that summand with C^p using the coefficient unit and its right unitor.
The coefficient unit is an isomorphism: constant sheafification of the free rank-one
module is the unit module, and exterior power zero is the coefficient ring. The tensor
unit followed by this projection is the identity. Koszul transitions preserve exterior
degree, act identically in degree zero, and are exterior powers of the diagonal map
sending e_j to b_j e_j. This proves naturality of the retractions. The composite of a
successive diagonal maps is zero because b_j^a=0 for every j. Every positive exterior
power of this zero map is zero; the zeroth exterior power is the identity. Consequently
the a-step tensor transition is exactly projection onto exterior degree zero followed
by its inclusion. This computation is independent of the Koszul differential, so it
holds before the tail where that differential vanishes as well. It also covers r=0:
only exterior degree zero survives. Totalization uses the coproduct universal property,
so no boundedness of C is required. -/
theorem nilpotentKoszulGradedTower (X : Scheme.{t}) (B : Type t) [CommRing B]
    (r : ℕ) (b : Fin r → B) (a : ℕ) (_ha : 0 < a) (hb : ∀ j, b j ^ a = 0)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ) :
    let T := Functor.ofOpSequence (koszulTensorTransition X B r b C)
    ∃ β : ∀ p : ℤ,
        (T ⋙ HomologicalComplex.eval _ (.up ℤ) p) ⟶
          (Functor.const ℕᵒᵖ).obj (C.X p),
      (∀ n p, (koszulTensorUnit X B r b C n).f p ≫ (β p).app (op n) = 𝟙 (C.X p)) ∧
      (∀ n p, (T.map (homOfLE (Nat.le_add_right n a)).op).f p =
        (β p).app (op (n + a)) ≫ (koszulTensorUnit X B r b C n).f p) := by
  let := SheafOfModules.monoidalCategory (adicConstantRing X B)
  let T := Functor.ofOpSequence (koszulTensorTransition X B r b C)
  let β : ∀ p : ℤ, (T ⋙ HomologicalComplex.eval _ (.up ℤ) p) ⟶
      (Functor.const ℕᵒᵖ).obj (C.X p) := fun p ↦
    NatTrans.ofOpSequence (fun n ↦ gradedRetraction X B r b C n p) (fun n ↦ by
      dsimp only [Functor.comp_map, Functor.const_obj_obj, Functor.const_obj_map,
        HomologicalComplex.eval_map]
      rw [Category.comp_id]
      dsimp only [T]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact gradedRetraction_step X B r b C n p)
  refine ⟨β, fun n p ↦ gradedRetraction_unit X B r b C n p, ?_⟩
  intro n p
  change (T.map _).f p = gradedRetraction X B r b C (n + a) p ≫
    (koszulTensorUnit X B r b C n).f p
  rw [tensor_jump]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [gradedRetraction,
    HomologicalComplex.ι_mapBifunctorDesc_assoc]
  split_ifs with hj
  · subst j
    have hi : i = p := by simpa using hij
    subst i
    let := koszulSheafUnitZero_isIso X B r b (n + a)
    have hzero : (((koszulConstantFunctor X B).mapHomologicalComplex (.up ℤ)).map
        ((Functor.ofOpSequence (koszulPowerTransition B r b)).map
          (homOfLE (Nat.le_add_right n a)).op)).f 0 =
        inv (koszulSheafUnitZero X B r b (n + a)) ≫ koszulSheafUnitZero X B r b n := by
      apply (cancel_epi (koszulSheafUnitZero X B r b (n + a))).1
      rw [sheafUnitZero_jump, IsIso.hom_inv_id_assoc]
    simp only [HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
      id_whiskerRight, koszulTensorUnit, koszulTensorUnitComponent]
    erw [Category.id_comp]
    rw [hzero]
    simp only [Category.assoc, ← whiskerLeft_comp_assoc, Iso.hom_inv_id_assoc]
    rfl
  · have hz : (((koszulConstantFunctor X B).mapHomologicalComplex (.up ℤ)).map
        ((Functor.ofOpSequence (koszulPowerTransition B r b)).map
          (homOfLE (Nat.le_add_right n a)).op)).f j = 0 := by
      change (koszulConstantFunctor X B).map _ = 0
      rw [coefficient_jump_zero B r b n a hb j hj, Functor.map_zero]
    simp only [HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
      hz]
    have ht : C.X i ◁
        (0 : (koszulPowerSheaf X B r b (n + a)).X j ⟶
          (koszulPowerSheaf X B r b n).X j) = 0 :=
      (tensorLeft (C.X i)).map_zero _ _
    dsimp only [koszulPowerSheaf, Functor.ofOpSequence_obj] at ht ⊢
    erw [ht, zero_comp, comp_zero, zero_comp]

end AlgebraicGeometry.Scheme
