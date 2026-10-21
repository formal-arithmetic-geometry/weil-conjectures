/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Category.Ring.Limits

/-! # Regular constant scalars on flat module sheaves

Source: Stacks Project, Modules on Sites, Tags 03ER(3), 08FC and 03DA
(blueprint: lem-sfb-flat-constant-module-scalar-mono).
-/

@[expose] public section

set_option autoImplicit false

universe uC vC r m

open CategoryTheory Opposite

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem constantScalar_ring_injective
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{r}]
    (A : Type r) [CommRing A] (a : A)
    (ha : Function.Injective (fun x : A ↦ a * x)) (U : C) :
    Function.Injective (fun s :
        (sheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).obj (op U) ↦
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op U)) a * s) := by
  let B := Localization.Away a
  let f : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  have hreg : IsRegular a := (Commute.isRegular_iff (fun b ↦ mul_comm a b)).2 ha
  have hf : Function.Injective f := by
    apply (IsLocalization.injective_iff_isRegular (S := B) (Submonoid.powers a)).2
    rintro ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := hx
    exact hreg.pow n
  have : Mono f := ConcreteCategory.mono_of_injective f hf
  let g := (constantSheaf J CommRingCat).map f
  have : Mono ((Functor.const Cᵒᵖ).map f) := by
    apply NatTrans.mono_of_mono_app
  have : Mono g := by
    change Mono ((presheafToSheaf J CommRingCat).map ((Functor.const Cᵒᵖ).map f))
    infer_instance
  have : Mono (g.hom.app (op U)) := inferInstance
  have hg : Function.Injective (g.hom.app (op U)) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback _
  let ηA := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  let ηB := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B))
  have hga : g.hom.app (op U) (ηA.app (op U) a) =
      ηB.app (op U) (algebraMap A B a) := by
    exact congrArg (fun k ↦ k.app (op U) a)
      (toSheafify_naturality J ((Functor.const Cᵒᵖ).map f)).symm
  have hu : IsUnit (g.hom.app (op U) (ηA.app (op U) a)) := by
    rw [hga]
    exact (IsLocalization.Away.algebraMap_isUnit (S := B) a).map (ηB.app (op U)).hom
  intro s t h
  apply hg
  apply hu.mul_right_injective
  simpa only [map_mul] using congrArg (g.hom.app (op U)) h

/-- A regular scalar of a commutative ring acts injectively on sections of its constant
ring sheaf and of every flat module sheaf over that ring sheaf. Sectionwise injectivity
is the monomorphism condition, since kernels of module sheaves are computed sectionwise.
Source: Stacks Project, Tags 03ER(3), 08FC and 03DA
(blueprint: lem-sfb-flat-constant-module-scalar-mono).

Proof:
1. Since every power of a is regular, A → A[1/a] is injective
[lem-pc-affine-localization-injective]. The constant presheaf map is monic, and the
assumed left exact ring sheafification preserves this monomorphism. Evaluation is
injective. Naturality of the sheafification unit identifies the image of η(a) with
the image of the unit a/1. Multiplication by this unit is injective, so multiplication
by η(a) is injective on the constant ring sheaf.
2. Apply the existing local relation criterion for flat module sheaves
[lem-weil-pbc-flat-local-relations-universes] to η(a) • (s - t) = 0. On a covering
sieve it writes s - t as a finite sum of b_j • z_j, with η(a) * b_j = 0.
Naturality of η and Step 1 give b_j = 0, so s - t restricts to zero on that sieve.
3. The separatedness of M gives s - t = 0, hence s = t. No sectionwise flatness,
domain hypothesis or enough-points assumption is used. -/
theorem constantScalar_injective_of_flat
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max r m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
    (A : Type r) [CommRing A]
    (M : ringedSiteModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of A))))
    (hM : IsFlatOnSite M) (a : A) (ha : Function.Injective (fun x : A ↦ a * x)) :
    ∀ U : C,
      Function.Injective (fun s :
          (sheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).obj (op U) ↦
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op U)) a * s) ∧
      Function.Injective (fun s : M.val.obj (op U) ↦
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op U)) a • s) := by
  classical
  let R := (constantSheaf J CommRingCat.{r}).obj (CommRingCat.of A)
  let η := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
  have hR := constantScalar_ring_injective J A a ha
  intro U
  refine ⟨hR U, ?_⟩
  intro s t h
  change η.app (op U) a • s = η.app (op U) a • t at h
  have hz : η.app (op U) a • (s - t) = 0 := by
    exact (smul_sub _ s t).trans (sub_eq_zero.mpr h)
  obtain ⟨S, hS, hloc⟩ := local_equationalCriterion_of_isFlatOnSite.{uC, vC, r, m} R M hM
    U 1 (fun _ ↦ η.app (op U) a) (fun _ ↦ s - t) (by simpa using hz)
  have hlocal : ∀ (V : C) (f : V ⟶ U), S f → M.val.map f.op (s - t) = 0 := by
    intro V f hf
    obtain ⟨l, b, z, hs, hb⟩ := hloc V f hf
    have hη : R.obj.map f.op (η.app (op U) a) = η.app (op V) a := by
      exact (η.naturality_apply f.op a).symm
    have hzero (j : Fin l) : b 0 j = 0 := by
      apply hR V
      have hj := hb j
      simpa only [Fin.sum_univ_one, hη, mul_zero] using hj
    simpa only [hzero, zero_smul, Finset.sum_const_zero] using hs 0
  have heq : s - t = 0 := by
    apply M.isSheaf.isSeparated _ S hS
    intro V f hf
    change M.val.map f.op (s - t) = M.val.map f.op 0
    rw [map_zero]
    exact hlocal V f hf
  exact sub_eq_zero.mp heq

end SheafOfModules
