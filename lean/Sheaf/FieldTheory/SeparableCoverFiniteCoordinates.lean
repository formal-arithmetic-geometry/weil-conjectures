/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Sheaf.RingTheory.IndEtaleUniverseTransport
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ULift

/-!
# Separable-closure cover and finite-stage incremental coordinates

Source: Bhatt–Scholze, Definition 4.1.1 and Example 4.1.4; Stacks Project,
Tags 0BU2 and 03SF (blueprint: lem-sfb-separable-cover-finite-coordinates).

The colimit is expressed by its universal property for compatible algebra maps.
Tensor powers are Mathlib's finite indexed tensor products. The coordinate formula
uses the ordered prefix products of a tuple of automorphisms, so it also applies
to noncommutative Galois groups. The last clause uses Mathlib's restriction map.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct

namespace IsSepClosure

private theorem galois_colimit (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω]
    (A : Type (max u v)) [CommRing A] [Algebra k A]
    (f : (E : FiniteGaloisIntermediateField k Ω) → E →ₐ[k] A)
    (hf : ∀ E E' (h : E ≤ E'), (f E').comp (IntermediateField.inclusion h) = f E) :
    ∃! F : Ω →ₐ[k] A, ∀ E : FiniteGaloisIntermediateField k Ω,
      F.comp E.toIntermediateField.val = f E := by
  classical
  let S (E : FiniteGaloisIntermediateField k Ω) := E.toIntermediateField.toSubalgebra
  have hdir : Directed (· ≤ ·) S := fun E E' ↦
    ⟨E ⊔ E', show E ≤ E ⊔ E' from le_sup_left,
      show E' ≤ E ⊔ E' from le_sup_right⟩
  have htop : ⨆ E, S E = ⊤ := by
    apply top_unique
    intro x _
    exact le_iSup S (FiniteGaloisIntermediateField.adjoin k {x})
      (FiniteGaloisIntermediateField.subset_adjoin k {x} (by simp))
  have hcompat : ∀ E E' (h : S E ≤ S E'),
      f E = (f E').comp (Subalgebra.inclusion h) := fun E E' h ↦ (hf E E' h).symm
  let F := (Subalgebra.iSupLift S hdir f hcompat ⊤ htop.ge).comp
    Subalgebra.topEquiv.symm.toAlgHom
  have hF (E : FiniteGaloisIntermediateField k Ω) :
      F.comp E.toIntermediateField.val = f E := by
    ext x
    change Subalgebra.iSupLift S hdir f hcompat ⊤ htop.ge ⟨(x : Ω), trivial⟩ = _
    exact Subalgebra.iSupLift_mk S x (by trivial)
  refine ⟨F, hF, ?_⟩
  intro G hG
  ext x
  let E := FiniteGaloisIntermediateField.adjoin k {x}
  let y : E := ⟨x, FiniteGaloisIntermediateField.subset_adjoin k {x} (by simp)⟩
  exact (DFunLike.congr_fun (hG E) y).trans (DFunLike.congr_fun (hF E) y).symm

private theorem separable_indEtale (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [Algebra.IsSeparable k Ω] : Algebra.IndEtale k Ω := by
  apply Algebra.IndEtale.of_forall_fg_etale
  intro A hA
  let : Field A := A.isField_of_algebraic.toField
  have : Algebra.FiniteType k A := A.fg_iff_finiteType.mp hA
  have : Algebra.IsSeparable k A := Algebra.IsSeparable.of_algHom k Ω A.val
  have : Algebra.IsIntegral k A := ⟨Algebra.IsSeparable.isIntegral k⟩
  have : Module.Finite k A := Algebra.IsIntegral.finite
  exact Algebra.Etale.of_finite_of_isSeparable

private theorem separable_indEtale_across (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [Algebra.IsSeparable k Ω] :
    (algebraMap k Ω).IndEtaleAcrossUniverses := by
  let : Algebra (ULift.{u} k) (ULift.{u} Ω) := ULift.algebra' k (ULift.{u} Ω)
  have : Algebra.IsSeparable (ULift.{u} k) (ULift.{u} Ω) :=
    Algebra.IsSeparable.of_equiv_equiv (A₁ := k) (B₁ := Ω)
      (A₂ := ULift.{u} k) (B₂ := ULift.{u} Ω) (ULift.ringEquiv : ULift.{u} k ≃+* k).symm
      (ULift.ringEquiv : ULift.{u} Ω ≃+* Ω).symm
      (by ext x; rfl)
  exact (RingHom.IndEtale.algebraMap_iff _ _).mpr (separable_indEtale _ _)

private noncomputable def productEval {k E Ω : Type u} [Field k] [Field E] [Field Ω]
    [Algebra k E] [Algebra k Ω] {q : ℕ} (h : Fin q → E →ₐ[k] Ω) :
    (⨂[k] _ : Fin q, E) →ₐ[k] Ω :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra k (Fin q) Ω).compLinearMap fun j ↦ (h j).toLinearMap)
    (by change (∏ j, h j 1) = 1; simp)
    (by intro x y; change (∏ j, h j (x j * y j)) = (∏ j, h j (x j)) * ∏ j, h j (y j)
        simp only [map_mul, Finset.prod_mul_distrib])

private theorem productEval_tprod {k E Ω : Type u} [Field k] [Field E] [Field Ω]
    [Algebra k E] [Algebra k Ω] {q : ℕ} (h : Fin q → E →ₐ[k] Ω) (a : Fin q → E) :
    productEval h (PiTensorProduct.tprod k a) = ∏ j, h j (a j) := by
  simp [productEval, MultilinearMap.mkPiAlgebra_apply]

private noncomputable def ordinaryEval {k E Ω : Type u} [Field k] [Field E] [Field Ω]
    [Algebra k E] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω] (q : ℕ) :
    (Ω ⊗[k] (⨂[k] _ : Fin q, E)) →ₐ[Ω] ((Fin q → (E ≃ₐ[k] E)) → Ω) :=
  AlgHom.pi fun g ↦ Algebra.TensorProduct.lift (AlgHom.id Ω Ω)
    (productEval fun j ↦ (IsScalarTower.toAlgHom k E Ω).comp (g j).toAlgHom)
    (fun _ _ ↦ Commute.all _ _)

private theorem ordinaryEval_tprod {k E Ω : Type u} [Field k] [Field E] [Field Ω]
    [Algebra k E] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
    (q : ℕ) (a₀ : Ω) (a : Fin q → E) (g : Fin q → (E ≃ₐ[k] E)) :
    ordinaryEval (k := k) (E := E) (Ω := Ω) q (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) g =
      a₀ * ∏ j, algebraMap E Ω (g j (a j)) := by
  simp [ordinaryEval, productEval_tprod]

private theorem ordinaryEval_surjective {k E Ω : Type u} [Field k] [Field E] [Field Ω]
    [Algebra k E] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
    [FiniteDimensional k E] (q : ℕ) : Function.Surjective (ordinaryEval (k := k) (E := E)
      (Ω := Ω) q) := by
  classical
  let Q := E ≃ₐ[k] E
  let f := ordinaryEval (k := k) (E := E) (Ω := Ω) q
  have hli : LinearIndependent Ω (fun g : Q ↦ fun a : E ↦ algebraMap E Ω (g a)) := by
    apply (linearIndependent_monoidHom E Ω).comp
      (fun g : Q ↦ (algebraMap E Ω).toMonoidHom.comp g.toRingEquiv.toMonoidHom)
    intro g h heq
    apply AlgEquiv.ext
    intro a
    exact (algebraMap E Ω).injective (DFunLike.congr_fun heq a)
  have hspan : Submodule.span Ω (Set.range (fun a : E ↦
      fun g : Q ↦ algebraMap E Ω (g a))) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hli
  have hcoord (j : Fin q) (x : Q → Ω) : (fun g : Fin q → Q ↦ x (g j)) ∈ f.range := by
    have hx : x ∈ Submodule.span Ω (Set.range (fun a : E ↦
        fun g : Q ↦ algebraMap E Ω (g a))) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨1 ⊗ₜ[k] PiTensorProduct.singleAlgHom j a, ?_⟩
      ext g
      change ordinaryEval (k := k) (E := E) (Ω := Ω) q
        (1 ⊗ₜ[k] PiTensorProduct.tprod k (MonoidHom.mulSingle _ j a)) g = _
      rw [ordinaryEval_tprod]
      simp [MonoidHom.mulSingle_apply, Pi.mulSingle, Function.update_apply,
        apply_ite, map_one, Finset.prod_ite_eq']
    | zero => exact f.range.zero_mem
    | add x y hx hy hx' hy' => exact f.range.add_mem hx' hy'
    | smul c x hx hx' => exact f.range.smul_mem hx' c
  have hsingle (g : Fin q → Q) : Pi.single g (1 : Ω) ∈ f.range := by
    let z : Fin q → ((Fin q → Q) → Ω) :=
      fun j h ↦ (Pi.single (g j) (1 : Ω) : Q → Ω) (h j)
    have hp : (∏ j, z j) ∈ f.range := (f.range.prod_mem (t := Finset.univ)
          (f := fun j ↦ (fun h : Fin q → Q ↦ (Pi.single (g j) (1 : Ω) : Q → Ω) (h j)))
          (fun j _ ↦ hcoord j (Pi.single (g j) 1)))
    convert hp using 1
    ext h
    by_cases hh : h = g
    · subst h; simp [z]
    · obtain ⟨j, hj⟩ := Function.ne_iff.mp hh
      dsimp only [z] at *
      simp only [Finset.prod_apply, Pi.single_eq_of_ne hh]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact Pi.single_eq_of_ne hj 1
  intro x
  have hx : x ∈ f.range := by
    rw [← Finset.univ_sum_single x]
    apply f.range.sum_mem
    intro g _
    have := f.range.smul_mem (hsingle g) (x g)
    convert this using 1
    ext h
    by_cases hh : h = g
    · subst h; simp
    · simp [Pi.single_eq_of_ne hh]
  exact hx

private theorem ordinaryEval_bijective {k E Ω : Type u} [Field k] [Field E] [Field Ω]
    [Algebra k E] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
    [FiniteDimensional k E] [IsGalois k E] (q : ℕ) :
    Function.Bijective (ordinaryEval (k := k) (E := E) (Ω := Ω) q) := by
  classical
  let b := Basis.piTensorProduct (fun _ : Fin q ↦ Module.finBasis k E)
  have hdim : Module.finrank Ω (Ω ⊗[k] (⨂[k] _ : Fin q, E)) =
      Module.finrank Ω ((Fin q → (E ≃ₐ[k] E)) → Ω) := by
    rw [Module.finrank_eq_card_basis (b.baseChange Ω), Module.finrank_pi]
    simp only [Fintype.card_fun, Fintype.card_fin]
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (ordinaryEval (k := k) (E := E) (Ω := Ω) q).toLinearMap) hdim).mpr
      (ordinaryEval_surjective q),
    ordinaryEval_surjective q⟩

private theorem cumulative_bijective {G : Type*} [Group G] [Finite G] (q : ℕ) :
    Function.Bijective (fun g : Fin q → G ↦ fun j : Fin q ↦ Fin.partialProd g j.succ) := by
  classical
  suffices hi : Function.Injective
      (fun g : Fin q → G ↦ fun j : Fin q ↦ Fin.partialProd g j.succ) from
    ⟨hi, Finite.injective_iff_surjective.mp hi⟩
  intro g h heq
  funext j
  have hall : Fin.partialProd g = Fin.partialProd h := by
    funext i
    exact Fin.cases (by simp) (fun i ↦ congrFun heq i) i
  have hp := congrFun hall j.castSucc
  have hs : Fin.partialProd g j.succ = Fin.partialProd h j.succ := congrFun heq j
  rw [Fin.partialProd_succ, Fin.partialProd_succ, hp] at hs
  exact mul_left_cancel hs

private noncomputable def incrementalEquiv {k E Ω : Type u} [Field k] [Field E] [Field Ω]
    [Algebra k E] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
    [FiniteDimensional k E] [IsGalois k E] (q : ℕ) :
    (Ω ⊗[k] (⨂[k] _ : Fin q, E)) ≃ₐ[Ω] ((Fin q → (E ≃ₐ[k] E)) → Ω) :=
  (AlgEquiv.ofBijective (ordinaryEval (k := k) (E := E) (Ω := Ω) q)
    (ordinaryEval_bijective q)).trans
    { toFun := fun x g ↦ x (fun j : Fin q ↦ Fin.partialProd g j.succ)
      invFun := fun x g ↦ x ((Equiv.ofBijective _ (cumulative_bijective q)).symm g)
      left_inv := by
        intro x; funext g
        exact congrArg x ((Equiv.ofBijective _ (cumulative_bijective q)).apply_symm_apply g)
      right_inv := by
        intro x; funext g
        exact congrArg x ((Equiv.ofBijective _ (cumulative_bijective q)).symm_apply_apply g)
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }

private theorem incrementalEquiv_tprod {k E Ω : Type u} [Field k] [Field E] [Field Ω]
    [Algebra k E] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
    [FiniteDimensional k E] [IsGalois k E]
    (q : ℕ) (a₀ : Ω) (a : Fin q → E) (g : Fin q → (E ≃ₐ[k] E)) :
    incrementalEquiv (k := k) (E := E) (Ω := Ω) q (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) g =
      a₀ * ∏ j, algebraMap E Ω ((((List.ofFn g).take (j.val + 1)).prod) (a j)) :=
  ordinaryEval_tprod q a₀ a _

set_option backward.isDefEq.respectTransparency false in
private theorem incrementalEquiv_zero {k E Ω : Type u} [Field k] [Field E] [Field Ω]
    [Algebra k E] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
    [FiniteDimensional k E] [IsGalois k E]
    (x : Ω ⊗[k] (⨂[k] _ : Fin 0, E)) (g : Fin 0 → (E ≃ₐ[k] E)) :
    incrementalEquiv (k := k) (E := E) (Ω := Ω) 0 x g = TensorProduct.rid k Ω
      (TensorProduct.map (LinearMap.id : Ω →ₗ[k] Ω)
        (PiTensorProduct.isEmptyEquiv (Fin 0)).toLinearMap x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul a b =>
    induction b using PiTensorProduct.induction_on with
    | add x y hx hy => simp only [tmul_add, map_add, Pi.add_apply, hx, hy]
    | smul_tprod r a' =>
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rw [incrementalEquiv_tprod]
      simp [PiTensorProduct.isEmptyEquiv_apply_tprod]

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_apply (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (E E' : FiniteGaloisIntermediateField k Ω) (h : E ≤ E')
    (g : E' ≃ₐ[k] E') (a : E) :
    algebraMap E' Ω (g (IntermediateField.inclusion h a)) =
      algebraMap E Ω (AlgEquiv.toAlgHom
        (finGaloisGroupMap (homOfLE h).op g : E ≃ₐ[k] E) a) := by
  let : Algebra E E' := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower k E E' := IsScalarTower.of_algebraMap_eq' rfl
  change algebraMap E' Ω (g (algebraMap E E' a)) =
    algebraMap E Ω (g.restrictNormal E a)
  exact (congrArg (algebraMap E' Ω) (g.restrictNormal_commutes E a)).symm

private theorem restriction_prefix (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (E E' : FiniteGaloisIntermediateField k Ω) (h : E ≤ E') (q : ℕ)
    (g : Fin q → (E' ≃ₐ[k] E')) (j : Fin q) :
    finGaloisGroupMap (homOfLE h).op (((List.ofFn g).take (j.val + 1)).prod) =
      ((List.ofFn (fun i ↦ finGaloisGroupMap (homOfLE h).op (g i))).take
        (j.val + 1)).prod := by
  let f : (E' ≃ₐ[k] E') →* (E ≃ₐ[k] E) :=
    (finGaloisGroupMap (homOfLE h).op).hom.hom
  change f _ = _
  rw [map_list_prod, List.map_take, List.map_ofFn]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem incrementalEquiv_natural (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    (E E' : FiniteGaloisIntermediateField k Ω) (h : E ≤ E') (q : ℕ)
    (x : Ω ⊗[k] (⨂[k] _ : Fin q, E)) (g : Fin q → (E' ≃ₐ[k] E')) :
    incrementalEquiv (k := k) (E := E') (Ω := Ω) q (TensorProduct.map (LinearMap.id : Ω →ₗ[k] Ω)
      (PiTensorProduct.map fun _ : Fin q ↦ (IntermediateField.inclusion h).toLinearMap) x) g =
      incrementalEquiv (k := k) (E := E) (Ω := Ω) q x
        (fun j ↦ finGaloisGroupMap (homOfLE h).op (g j)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul a b =>
    induction b using PiTensorProduct.induction_on with
    | add x y hx hy => simp only [tmul_add, map_add, Pi.add_apply, hx, hy]
    | smul_tprod r a' =>
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rw [TensorProduct.map_tmul, PiTensorProduct.map_tprod]
      change incrementalEquiv (k := k) (E := E') (Ω := Ω) q
        ((r • a) ⊗ₜ[k] PiTensorProduct.tprod k
          (fun j ↦ IntermediateField.inclusion h (a' j))) g = _
      rw [incrementalEquiv_tprod, incrementalEquiv_tprod]
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      rw [restriction_apply k Ω E E' h, restriction_prefix k Ω E E' h]
      rfl

/-- A separable closure is the faithfully flat ind-etale union of its finite Galois
subfields; its spectrum is a singleton pro-etale cover. Every finite-stage tensor
power has the displayed incremental coordinates, compatible with field inclusion.
The degree-zero coordinate is the identity after the tensor-unit identifications.

Source: Bhatt–Scholze, Definition 4.1.1 and Example 4.1.4; Stacks Project,
Tags 0BU2 and 03SF (blueprint: lem-sfb-separable-cover-finite-coordinates).

Proof:
1. The finite Galois intermediate fields form a nonempty lattice. Their supremum
   as subalgebras is top because every singleton lies in its finite Galois
   adjunction. The directed-supremum lift extends compatible maps uniquely.
2. Every finitely generated subalgebra of a separable algebraic field extension
   is a finite separable field extension, hence etale. The ind-etale criterion
   applies both directly and after the canonical ULift transport. The extension
   is faithfully flat, its affine map is weakly etale, and the singleton affine
   surjection is a quasi-compact pro-etale cover.
3. Define ordinary tensor evaluation by the product of the chosen automorphisms.
   Dedekind independence implies that one-coordinate evaluations span every
   function on the automorphism group. Products yield the tuple delta functions,
   so the evaluation map is surjective. A base-changed indexed tensor basis and
   the Galois automorphism cardinality show equal dimensions, hence bijectivity.
4. Reindex ordinary coordinates by the ordered prefix products of a tuple of
   automorphisms. Prefix products determine the tuple by cancellation, giving
   a permutation of the finite tuple set and thus the incremental equivalence.
5. Tensor induction proves the degree-zero identification. Normal restriction
   commutes with inclusion and products, so tensor induction also proves the
   compatibility under inclusions of finite Galois fields.
-/
theorem separableCover_finiteCoordinates (k Ω : Type u) [Field k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] :
    Nonempty (FiniteGaloisIntermediateField k Ω) ∧
    IsDirected (FiniteGaloisIntermediateField k Ω) (· ≤ ·) ∧
    (∀ (A : Type (max u v)) [CommRing A] [Algebra k A]
      (f : (E : FiniteGaloisIntermediateField k Ω) → E →ₐ[k] A),
      (∀ (E E' : FiniteGaloisIntermediateField k Ω) (h : E ≤ E'),
        (f E').comp (IntermediateField.inclusion h) = f E) →
      ∃! F : Ω →ₐ[k] A, ∀ E : FiniteGaloisIntermediateField k Ω,
        F.comp E.toIntermediateField.val = f E) ∧
    Module.FaithfullyFlat k Ω ∧
    (algebraMap k Ω).IndEtaleAcrossUniverses ∧
    (∃ h : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap k Ω))),
      Presieve.singleton
        (MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
          @Scheme.ProEt.mk _ _ (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) h ⟶
            Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of k)))) ∈
        Scheme.ProEt.precoverage (Spec (CommRingCat.of k))
          (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of k))))) ∧
    ∃ θ : (E : FiniteGaloisIntermediateField k Ω) → (q : ℕ) →
        (Ω ⊗[k] (⨂[k] _ : Fin q, E)) ≃ₐ[Ω] ((Fin q → (E ≃ₐ[k] E)) → Ω),
      (∀ (E : FiniteGaloisIntermediateField k Ω) (q : ℕ) (a₀ : Ω)
        (a : Fin q → E) (g : Fin q → (E ≃ₐ[k] E)),
        θ E q (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) g =
          a₀ * ∏ j : Fin q,
            algebraMap E Ω ((((List.ofFn g).take (j.val + 1)).prod) (a j))) ∧
      (∀ (E : FiniteGaloisIntermediateField k Ω)
        (x : Ω ⊗[k] (⨂[k] _ : Fin 0, E)) (g : Fin 0 → (E ≃ₐ[k] E)),
        θ E 0 x g = TensorProduct.rid k Ω
          (TensorProduct.map (LinearMap.id : Ω →ₗ[k] Ω)
            (PiTensorProduct.isEmptyEquiv (Fin 0)).toLinearMap x)) ∧
      (∀ (E E' : FiniteGaloisIntermediateField k Ω) (h : E ≤ E') (q : ℕ)
        (x : Ω ⊗[k] (⨂[k] _ : Fin q, E)) (g : Fin q → (E' ≃ₐ[k] E')),
        θ E' q (TensorProduct.map (LinearMap.id : Ω →ₗ[k] Ω)
          (PiTensorProduct.map fun _ : Fin q ↦
            (IntermediateField.inclusion h).toLinearMap) x) g =
          θ E q x (fun j ↦ finGaloisGroupMap (homOfLE h).op (g j))) := by
  classical
  have hind : Algebra.IndEtale k Ω := separable_indEtale k Ω
  have hweak : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    weaklyEtale_SpecMap_algebraMap_iff.mpr inferInstance
  refine ⟨inferInstance, inferInstance, galois_colimit k Ω, inferInstance,
    separable_indEtale_across k Ω, ⟨hweak, ?_⟩, ?_⟩
  · let : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := hweak
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
      ⟨fun x ↦ ⟨Classical.arbitrary (PrimeSpectrum Ω), Subsingleton.elim _ _⟩⟩
    change Presieve.singleton _ ∈ Scheme.proetalePrecoverage.comap _ _
    rw [CategoryTheory.Precoverage.mem_comap_iff, Presieve.map_singleton]
    change Presieve.singleton (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ∈
      Scheme.proetalePrecoverage _
    exact Scheme.Hom.singleton_mem_propQCPrecoverage hweak
  · refine ⟨fun E q ↦ incrementalEquiv (k := k) (E := E) (Ω := Ω) q, ?_, ?_, ?_⟩
    · intro E q a₀ a g
      exact incrementalEquiv_tprod q a₀ a g
    · intro E x g
      exact incrementalEquiv_zero x g
    · intro E E' h q x g
      exact incrementalEquiv_natural k Ω E E' h q x g

end IsSepClosure
