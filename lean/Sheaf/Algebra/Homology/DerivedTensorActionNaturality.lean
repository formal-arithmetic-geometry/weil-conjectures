/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups C1, G2
-/
module

public import Sheaf.Algebra.Homology.BalancedDerivedTensorModel
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Scalar actions and the balanced derived tensor comparison

Source: Stacks Project, Section 06Y5, Lemma 06Y6 and the comparison-map construction
(blueprint: lem-pc-derived-tensor-action-naturality).

The target of `c` is the K-flat model `P ⊗_A (A ⊗_R R')` of the second derived tensor.
The mixed tensor definition already incorporates the associativity identification.
Module structures are passed explicitly, so the signature has no local notation or instances.
-/

@[expose] public section

set_option autoImplicit false

universe u wA wR

open CategoryTheory
open scoped TensorProduct

namespace DerivedCategory

private def additiveMapEnd {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (L : C ⥤ D) [L.Additive] (X : C) :
    End X →+* End (L.obj X) :=
  { L.mapEnd X with
    map_zero' := L.map_zero X X
    map_add' := fun _ _ ↦ L.map_add }

set_option backward.isDefEq.respectTransparency false in
private theorem extendScalars_add
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {F G : ModuleCat.{u} R} (f g : F ⟶ G) :
    (ModuleCat.extendScalars (algebraMap R A)).map (f + g) =
      (ModuleCat.extendScalars (algebraMap R A)).map f +
      (ModuleCat.extendScalars (algebraMap R A)).map g := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  simp [ModuleCat.ExtendScalars.map_tmul, TensorProduct.tmul_add]

set_option backward.isDefEq.respectTransparency false in
open scoped ChangeOfRings in
private theorem extendScalars_scalar
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (F : ModuleCat.{u} R) (r : R) :
    (ModuleCat.extendScalars (algebraMap R A)).map (r • 𝟙 F) =
      algebraMap R A r • 𝟙 ((ModuleCat.extendScalars (algebraMap R A)).obj F) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  simp only [ModuleCat.ExtendScalars.map_tmul]
  change (1 : A) ⊗ₜ[R,algebraMap R A] (r • x) =
    (algebraMap R A r) • ((1 : A) ⊗ₜ[R,algebraMap R A] x)
  let : Module R A := Module.compHom A (algebraMap R A)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem mixedTotalTensor_additive
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (P : CochainComplex (ModuleCat A) ℤ) :
    ((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).Additive := by
  constructor
  intro F G f g
  dsimp only [ModuleCat.mixedTotalTensor]
  apply HomologicalComplex.Hom.ext
  funext j
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ hij
  change _ ≫ (HomologicalComplex.mapBifunctorMap (𝟙 P) (f + g)
    (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ)).f j = _
  simp [HomologicalComplex.ι_mapBifunctorMap, ModuleCat.mixedTensor, extendScalars_add,
    CategoryTheory.MonoidalPreadditive.whiskerLeft_add, CategoryTheory.Preadditive.add_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem mixedTotalTensor_baseScalar
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (P : CochainComplex (ModuleCat A) ℤ) (F : CochainComplex (ModuleCat R) ℤ) (r : R) :
    ((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).map (r • 𝟙 F) =
      algebraMap R A r • 𝟙 (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).obj F) := by
  change HomologicalComplex.mapBifunctorMap (𝟙 P) (r • 𝟙 F)
    (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) =
      algebraMap R A r • 𝟙 (HomologicalComplex.mapBifunctor P F
        (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ))
  apply HomologicalComplex.Hom.ext
  funext j
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ hij
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp [ModuleCat.mixedTensor, extendScalars_scalar, CategoryTheory.Linear.comp_smul,
    CategoryTheory.Linear.smul_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem homology_Q_scalar
    (A : Type u) [CommRing A] [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    (K : CochainComplex (ModuleCat A) ℤ) (i : ℤ) (a : A) :
    (homologyFunctor (ModuleCat A) i).map (Q.map (a • 𝟙 K)) =
      a • 𝟙 ((homologyFunctor (ModuleCat A) i).obj (Q.obj K)) := by
  apply (cancel_mono ((homologyFunctorFactors (ModuleCat A) i).hom.app K)).1
  rw [homologyFunctorFactors_hom_naturality]
  have hsc : (HomologicalComplex.shortComplexFunctor (ModuleCat A) (.up ℤ) i).map
      (a • 𝟙 K) = a • 𝟙 (K.sc i) := by
    ext <;> rfl
  rw [HomologicalComplex.homologyMap, hsc, ShortComplex.homologyMap_smul,
    ShortComplex.homologyMap_id]
  change _ ≫ (a • 𝟙 (K.homology i)) = _
  simp [CategoryTheory.Linear.comp_smul, CategoryTheory.Linear.smul_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem tensorModule_of_ringHom
    (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] (H : ModuleCat.{u} A)
    (φ : R' →+* Module.End A H)
    (hφ : ∀ r : R, φ (algebraMap R R' r) =
      algebraMap A (Module.End A H) (algebraMap R A r)) :
    ∃ p : Module (A ⊗[R] R') H,
      ∀ (a : A) (b : R') (x : H),
        p.toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (a ⊗ₜ[R] b) x =
          a • φ b x := by
  let : Algebra R (Module.End A H) :=
    Algebra.compHom (Module.End A H) (algebraMap R A)
  let : IsScalarTower R A (Module.End A H) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let g : R' →ₐ[R] Module.End A H := { φ with commutes' := hφ }
  let f : A →ₐ[R] Module.End A H := IsScalarTower.toAlgHom R A (Module.End A H)
  let ψ := Algebra.TensorProduct.lift f g (fun a b ↦ Algebra.commutes a (g b))
  refine ⟨Module.compHom H ψ.toRingHom, ?_⟩
  intro a b x
  change (ψ (a ⊗ₜ[R] b)) x = _
  simp [ψ, Algebra.TensorProduct.lift_tmul, f, g]

set_option backward.isDefEq.respectTransparency false in
/-- Scalar compatibility, naturality and the comparison map for balanced tensor models.
Source: Stacks Project, Section 06Y5 and Lemma 06Y6
(blueprint: lem-pc-derived-tensor-action-naturality).

Proof:
1. Obtain the derived bifunctor, its counit, canonical model isomorphisms, coefficient
   ring actions, and their cohomology module structures from
   `lem-pc-balanced-derived-tensor-model`.
2. Naturality of `T.map (Q.map g)` intertwines the second-ring actions. Its cohomology
   map is A-linear, so the pure-tensor formula proves tensor-ring linearity on pure
   tensors; tensor induction extends this to all scalars.
3. For the canonical model isomorphism, cancel the invertible K-flat counit. Naturality
   of the counit and of `T.map (Q.map q)`, together with A-linearity of q, proves the
   first-factor scalar equation. Transport the cohomology module structure along this
   specified isomorphism using its additive equivalence.
4. Define the comparison as the inverse of `T.map (Q.map q)` at `R'[0]`, followed by
   the counit at `R'[0]`. The defining equation of the model isomorphism and naturality
   of the counit prove its representative formula and second-ring equivariance.
5. The additive underived total tensor induces a ring map from R' to endomorphisms of
   the target. Summandwise extension of scalars identifies its restriction to R with
   the A-scalar map. The homology comparison with ordinary complex homology preserves
   scalar multiplication. The algebra tensor universal property therefore constructs
   the target cohomology module structure with the required pure-tensor formula.
   Finally, the comparison is A-linear and intertwines the R' actions, so tensor
   induction proves its tensor-ring linearity. -/
theorem exists_derivedTensor_action_naturality
    (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)] :
    ∃ T : DerivedCategory (ModuleCat.{u} A) ⥤
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A),
    ∃ α : ∀ M : CochainComplex (ModuleCat.{u} A) ℤ,
    Q ⋙ T.obj (Q.obj M) ⟶ (ModuleCat.mixedTotalTensor (algebraMap R A)).obj M ⋙ Q,
    (∀ M, (T.obj (Q.obj M)).IsLeftDerivedFunctor (α M)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))) ∧
    (∀ M F, (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F →
    IsIso ((α M).app F)) ∧
    (∀ (M N : CochainComplex (ModuleCat.{u} A) ℤ) (g : M ⟶ N)
    (F : CochainComplex (ModuleCat.{u} R) ℤ),
    (T.map (Q.map g)).app (Q.obj F) ≫ (α N).app F =
    (α M).app F ≫ Q.map (((ModuleCat.mixedTotalTensor (algebraMap R A)).map g).app F)) ∧
    (∀ (M P : CochainComplex (ModuleCat.{u} A) ℤ) (q : P ⟶ M),
    QuasiIso q → (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P →
    ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (f : F ⟶ ((CochainComplex.singleFunctor
      (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))),
    QuasiIso f → (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F →
    ∃! e : Q.obj (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).obj F) ≅ (T.obj (Q.obj
      M)).obj (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of
      R R'))),
    (α P).app F ≫ e.hom =
    (T.map (Q.map q)).app (Q.obj F) ≫ (T.obj (Q.obj M)).map (Q.map f)) ∧
    (∃ ρ : ∀ M : CochainComplex (ModuleCat.{u} A) ℤ, R' →+* End ((T.obj (Q.obj M)).obj (Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R')))),
    (∀ M b, ρ M b = (T.obj (Q.obj M)).map (Q.map ((CochainComplex.singleFunctor (ModuleCat.{u}
      R) (0 : ℤ)).map (ModuleCat.ofHom (LinearMap.mulLeft R b))))) ∧
    (∀ M (a : A) (b : R'), Commute (ρ M b) ((T.map (Q.map (a • 𝟙 M))).app (Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))))) ∧
    ∃ m : ∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ), Module (A ⊗[R] R')
      ((homologyFunctor (ModuleCat.{u} A) i).obj ((T.obj (Q.obj M)).obj (Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))))),
    (∀ M i (a : A) (b : R') (x : (homologyFunctor (ModuleCat.{u} A) i).obj ((T.obj (Q.obj
      M)).obj (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of
      R R'))))),
    (m M i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (a ⊗ₜ[R] b) (x) = a •
      ((homologyFunctor (ModuleCat.{u} A) i).map (ρ M b)).hom x) ∧
    (∀ (M N : CochainComplex (ModuleCat.{u} A) ℤ) (g : M ⟶ N) (i : ℤ)
    (t : A ⊗[R] R') (x : (homologyFunctor (ModuleCat.{u} A) i).obj ((T.obj (Q.obj M)).obj (Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))))),
    ((homologyFunctor (ModuleCat.{u} A) i).map ((T.map (Q.map g)).app (Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))))).hom
      ((m M i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (t) (x)) =
    (m N i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (t) (((homologyFunctor
      (ModuleCat.{u} A) i).map ((T.map (Q.map g)).app (Q.obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))))).hom x)) ∧
    ∀ (M P : CochainComplex (ModuleCat.{u} A) ℤ) (q : P ⟶ M),
    QuasiIso q → (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P →
    ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ) (f : F ⟶ ((CochainComplex.singleFunctor
      (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))),
    QuasiIso f → (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F →
    ∃ e : Q.obj (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).obj F) ≅ (T.obj (Q.obj
      M)).obj (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of
      R R'))),
    ((α P).app F ≫ e.hom = (T.map (Q.map q)).app (Q.obj F) ≫ (T.obj (Q.obj M)).map (Q.map f)) ∧
    (∀ a : A, Q.map (((ModuleCat.mixedTotalTensor (algebraMap R A)).map (a • 𝟙 P)).app F) ≫
      e.hom =
    e.hom ≫ (T.map (Q.map (a • 𝟙 M))).app (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u}
      R) (0 : ℤ)).obj (ModuleCat.of R R')))) ∧
    ∃ n : ∀ i : ℤ, Module (A ⊗[R] R') ((homologyFunctor (ModuleCat.{u} A) i).obj (Q.obj
      (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).obj F))),
    (∀ i (t : A ⊗[R] R') (x : (homologyFunctor (ModuleCat.{u} A) i).obj (Q.obj
      (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).obj F))),
    ((homologyFunctor (ModuleCat.{u} A) i).map (e.hom)).hom ((n
      i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (t) (x)) = (m M
      i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (t) (((homologyFunctor
      (ModuleCat.{u} A) i).map (e.hom)).hom x)) ∧
    ∃ c : (T.obj (Q.obj M)).obj (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 :
      ℤ)).obj (ModuleCat.of R R'))) ⟶ Q.obj (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj
      P).obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R
      R'))),
    (e.hom ≫ c = Q.map (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).map f)) ∧
    (∀ b : R', ρ M b ≫ c = c ≫ Q.map (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).map
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).map (ModuleCat.ofHom
      (LinearMap.mulLeft R b))))) ∧
    ∃ p : ∀ i : ℤ, Module (A ⊗[R] R') ((homologyFunctor (ModuleCat.{u} A) i).obj (Q.obj
      (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))))),
    (∀ i (a : A) (b : R') (x : (homologyFunctor (ModuleCat.{u} A) i).obj (Q.obj
      (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj P).obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R R'))))),
    (p i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (a ⊗ₜ[R] b) (x) = a •
      ((homologyFunctor (ModuleCat.{u} A) i).map (Q.map (((ModuleCat.mixedTotalTensor
      (algebraMap R A)).obj P).map ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).map
      (ModuleCat.ofHom (LinearMap.mulLeft R b)))))).hom x) ∧
    ∀ i (t : A ⊗[R] R') (x : (homologyFunctor (ModuleCat.{u} A) i).obj ((T.obj (Q.obj M)).obj
      (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R
      R'))))),
    ((homologyFunctor (ModuleCat.{u} A) i).map (c)).hom ((m M
      i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (t) (x)) = (p
      i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (t) (((homologyFunctor
      (ModuleCat.{u} A) i).map (c)).hom x)) := by
  classical
  obtain ⟨T, α, hderived, hcompute, hnat, hmodel, hactions⟩ :=
    exists_balancedDerivedTensorModel.{u, wA, wR} R A R'
  choose ρ hρ hcomm hm using hactions
  choose m hm using hm
  refine ⟨T, α, hderived, hcompute, hnat, hmodel, ρ, hρ, hcomm, m, hm, ?_, ?_⟩
  · intro M N g i t x
    let := m M i
    let := m N i
    change ((homologyFunctor (ModuleCat A) i).map
      ((T.map (Q.map g)).app (Q.obj
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
          (ModuleCat.of R R'))))).hom (t • x) = t • _
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hm, hm]
      rw [map_smul]
      congr 1
      have h := (T.map (Q.map g)).naturality (Q.map
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).map
          (ModuleCat.ofHom (LinearMap.mulLeft R b))))
      rw [← hρ M b, ← hρ N b] at h
      have h' := congrArg (fun k =>
        ((homologyFunctor (ModuleCat A) i).map k).hom x) h
      simpa using h'
    | add t t' ht ht' => simp only [add_smul, map_add, ht, ht']
  · intro M P q hq hP F f hf hF
    let S := CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)
    let E := S.obj (ModuleCat.of R R')
    let B := ModuleCat.mixedTotalTensor (algebraMap R A)
    obtain ⟨e, he, _⟩ := hmodel M P q hq hP F f hf hF
    have hα := hcompute P F hF
    have hscalar (a : A) :
        Q.map ((B.map (a • 𝟙 P)).app F) ≫ e.hom =
          e.hom ≫ (T.map (Q.map (a • 𝟙 M))).app (Q.obj E) := by
      apply (cancel_epi ((α P).app F)).1
      rw [← Category.assoc, ← hnat P P (a • 𝟙 P) F, Category.assoc, he]
      have hqscalar : (a • 𝟙 P) ≫ q = q ≫ (a • 𝟙 M) := by
        simp [CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul]
      have htscalar := congrArg (fun k => (T.map (Q.map k)).app (Q.obj F)) hqscalar
      simp only [Functor.map_comp, NatTrans.comp_app] at htscalar
      rw [← Category.assoc, htscalar, Category.assoc]
      rw [← (T.map (Q.map (a • 𝟙 M))).naturality (Q.map f)]
      rw [← Category.assoc, ← he, Category.assoc]
    let n (i : ℤ) : Module (A ⊗[R] R')
        ((homologyFunctor (ModuleCat A) i).obj (Q.obj ((B.obj P).obj F))) :=
      letI := m M i
      (((homologyFunctor (ModuleCat A) i).mapIso e).toLinearEquiv.toAddEquiv).module _
    have hn (i : ℤ) (t : A ⊗[R] R')
        (x : (homologyFunctor (ModuleCat A) i).obj (Q.obj ((B.obj P).obj F))) :
        ((homologyFunctor (ModuleCat A) i).map e.hom).hom
          ((n i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul t x) =
        (m M i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul t
          (((homologyFunctor (ModuleCat A) i).map e.hom).hom x) := by
      let := m M i
      let l := ((homologyFunctor (ModuleCat A) i).mapIso e).toLinearEquiv
      change l (l.symm (t • l x)) = t • l x
      exact l.apply_symm_apply _
    have hqiso : IsIso (Q.map q) :=
      (isIso_Q_map_iff_quasiIso (ModuleCat A) q).2 hq
    let v := (T.map (Q.map q)).app (Q.obj E)
    have : IsIso v := inferInstance
    let c := inv v ≫ (α P).app E
    have hc : e.hom ≫ c = Q.map ((B.obj P).map f) := by
      apply (cancel_epi ((α P).app F)).1
      simp only [← Category.assoc]
      rw [he]
      have h := (T.map (Q.map q)).naturality (Q.map f)
      dsimp only [c]
      simp only [← Category.assoc]
      rw [← h]
      dsimp only [v, E, S]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      exact (α P).naturality f
    have hcb (b : R') : ρ M b ≫ c = c ≫ Q.map ((B.obj P).map
        (S.map (ModuleCat.ofHom (LinearMap.mulLeft R b)))) := by
      rw [hρ]
      dsimp only [c]
      have h := (T.map (Q.map q)).naturality
        (Q.map (S.map (ModuleCat.ofHom (LinearMap.mulLeft R b))))
      apply (cancel_epi v).1
      dsimp only [v]
      simp only [← Category.assoc]
      rw [← h]
      dsimp only [v, E, S]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      exact (α P).naturality (S.map (ModuleCat.ofHom (LinearMap.mulLeft R b)))
    refine ⟨e, he, hscalar, n, hn, c, hc, hcb, ?_⟩
    have hadd := mixedTotalTensor_additive R A P
    let K := (B.obj P) ⋙ Q
    let σ : R' →+* End (ModuleCat.of R R') :=
      (ModuleCat.endRingEquiv (ModuleCat.of R R')).symm.toRingHom.comp
        (Algebra.lmul R R')
    let τ : R' →+* End (K.obj E) :=
      (additiveMapEnd K E).comp ((additiveMapEnd S (ModuleCat.of R R')).comp σ)
    have hτ (b : R') : τ b =
        Q.map ((B.obj P).map (S.map (ModuleCat.ofHom (LinearMap.mulLeft R b)))) := by
      rfl
    have hτR (r : R) : τ (algebraMap R R' r) =
        Q.map (algebraMap R A r • 𝟙 ((B.obj P).obj E)) := by
      rw [hτ]
      have hs : S.map (ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R R' r))) =
          r • 𝟙 E := by
        have hmul : ModuleCat.ofHom (LinearMap.mulLeft R (algebraMap R R' r)) =
            r • 𝟙 (ModuleCat.of R R') := by
          ext x
          simp [Algebra.smul_def]
        rw [hmul]
        simp [E, S, Functor.map_smul]
      rw [hs, mixedTotalTensor_baseScalar R A P E r]
    have hp (i : ℤ) : ∃ p : Module (A ⊗[R] R')
        ((homologyFunctor (ModuleCat A) i).obj (Q.obj ((B.obj P).obj E))),
        ∀ (a : A) (b : R')
          (x : (homologyFunctor (ModuleCat A) i).obj (Q.obj ((B.obj P).obj E))),
          p.toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul (a ⊗ₜ[R] b) x =
            a • ((homologyFunctor (ModuleCat A) i).map (τ b)).hom x := by
      let H := homologyFunctor (ModuleCat A) i
      let φ : R' →+* Module.End A (H.obj (K.obj E)) :=
        (ModuleCat.endRingEquiv _).toRingHom.comp ((additiveMapEnd H _).comp τ)
      apply tensorModule_of_ringHom R A R' (H.obj (K.obj E)) φ
      intro r
      change (H.map (τ (algebraMap R R' r))).hom = _
      rw [hτR, homology_Q_scalar]
      rfl
    dsimp only [B, E, S, K, Functor.comp_obj] at hp c
    choose p hp using hp
    refine ⟨p, ?_, ?_⟩
    · intro i a b x
      rw [← hτ b]
      exact hp i a b x
    · intro i t x
      let := m M i
      let := p i
      change ((homologyFunctor (ModuleCat A) i).map c).hom (t • x) = t • _
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        rw [hm M i a b x]
        change _ = (p i).toDistribMulAction.toMulAction.toSemigroupAction.toSMul.smul
          (a ⊗ₜ[R] b) (((homologyFunctor (ModuleCat A) i).map c).hom x)
        rw [hp i a b _]
        rw [map_smul]
        congr 1
        have h := congrArg (fun k => ((homologyFunctor (ModuleCat A) i).map k).hom x)
          (hcb b)
        change ((homologyFunctor (ModuleCat A) i).map c).hom
          (((homologyFunctor (ModuleCat A) i).map (ρ M b)).hom x) =
          ((homologyFunctor (ModuleCat A) i).map (Q.map ((B.obj P).map
            (S.map (ModuleCat.ofHom (LinearMap.mulLeft R b)))))).hom
              (((homologyFunctor (ModuleCat A) i).map c).hom x)
        simp only [Functor.map_comp] at h
        exact h
      | add t t' ht ht' => simp only [add_smul, map_add, ht, ht']

end DerivedCategory
