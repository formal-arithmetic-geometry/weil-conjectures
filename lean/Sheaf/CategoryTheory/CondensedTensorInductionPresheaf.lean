/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.CategoryTheory.CondensedTensorInductionData
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # The balanced tensor presheaf

Source: the induction argument, steps 2--3, below direct-image stability paragraph (3).
(blueprint: lem-sfb-condensed-tensor-presheaf).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace Profinite.CondensedAction
variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
  (P : ProfiniteGrp.{u}) (H : ClosedSubgroup P)

variable {R P H}

private theorem tensor_add (M : ActionModule R H.toSubgroup) (S : Profinite.{u})
    (p : C(S, P)) (m n : sectionModule R M.module S) :
    inductionTensor R P H M S p (m + n) =
      inductionTensor R P H M S p m + inductionTensor R P H M S p n := by
  apply sub_eq_zero.mp
  rw [sub_add_eq_sub_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.subset_span (Or.inl ⟨p, m, n, rfl⟩)

private theorem tensor_smul (M : ActionModule R H.toSubgroup) (S : Profinite.{u})
    (p : C(S, P)) (a : inductionSectionRing R S) (m : sectionModule R M.module S) :
    inductionTensor R P H M S p (a • m) = a • inductionTensor R P H M S p m := by
  apply sub_eq_zero.mp
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.subset_span (Or.inr (Or.inl ⟨p, a, m, rfl⟩))

private theorem tensor_balance (M : ActionModule R H.toSubgroup) (S : Profinite.{u})
    (p : C(S, P)) (h : C(S, H.toSubgroup)) (m : sectionModule R M.module S) :
    inductionTensor R P H M S
        (p * (inductionSubgroupInclusion P H).toContinuousMap.comp h) m =
      inductionTensor R P H M S p (M.act S h m) := by
  apply (Submodule.Quotient.eq _).mpr
  exact Submodule.subset_span (Or.inr (Or.inr ⟨p, h, m, rfl⟩))

private def tensorSum {A : Type (u + 1)} [Ring A] {V : Type (u + 1)}
    [AddCommGroup V] [Module A V] {M : ActionModule R H.toSubgroup} {S : Profinite.{u}}
    (σ : inductionSectionRing R S →+* A)
    (v : C(S, P) → sectionModule R M.module S → V) :
    ((C(S, P) × sectionModule R M.module S) →₀ inductionSectionRing R S) →ₛₗ[σ] V :=
  Finsupp.lsum ℕ fun x ↦
    { toFun := fun a ↦ σ a • v x.1 x.2
      map_add' := fun a b ↦ by rw [map_add, add_smul]
      map_smul' := fun a b ↦ by simp only [smul_eq_mul, map_mul, mul_smul] }

private theorem tensorSum_single {A : Type (u + 1)} [Ring A] {V : Type (u + 1)}
    [AddCommGroup V] [Module A V] {M : ActionModule R H.toSubgroup} {S : Profinite.{u}}
    (σ : inductionSectionRing R S →+* A)
    (v : C(S, P) → sectionModule R M.module S → V)
    (p : C(S, P)) (m : sectionModule R M.module S) (a : inductionSectionRing R S) :
    tensorSum σ v (Finsupp.single (p, m) a) = σ a • v p m := by
  simp [tensorSum, Finsupp.lsum_single]

private def tensorLift {A : Type (u + 1)} [Ring A] {V : Type (u + 1)}
    [AddCommGroup V] [Module A V] (M : ActionModule R H.toSubgroup) (S : Profinite.{u})
    (σ : inductionSectionRing R S →+* A)
    (v : C(S, P) → sectionModule R M.module S → V)
    (hadd : ∀ p m n, v p (m + n) = v p m + v p n)
    (hsmul : ∀ p a m, v p (a • m) = σ a • v p m)
    (hbal : ∀ p h m, v (p * (inductionSubgroupInclusion P H).toContinuousMap.comp h) m =
      v p (M.act S h m)) : InductionSection R P H M S →ₛₗ[σ] V :=
  (inductionRelations R P H M S).liftQ (tensorSum σ v) (by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨p, m, n, rfl⟩ | ⟨p, a, m, rfl⟩ | ⟨p, h, m, rfl⟩
    · change tensorSum σ v _ = 0
      rw [map_sub, map_sub, tensorSum_single, tensorSum_single, tensorSum_single]
      simp [hadd]
    · change tensorSum σ v _ = 0
      rw [map_sub, map_smulₛₗ, tensorSum_single, tensorSum_single]
      simp [hsmul]
    · change tensorSum σ v _ = 0
      rw [map_sub, tensorSum_single, tensorSum_single]
      simp only [map_one, one_smul]
      exact sub_eq_zero.mpr (hbal p h m))

private theorem tensorLift_tensor {A : Type (u + 1)} [Ring A] {V : Type (u + 1)}
    [AddCommGroup V] [Module A V] (M : ActionModule R H.toSubgroup) (S : Profinite.{u})
    (σ : inductionSectionRing R S →+* A)
    (v : C(S, P) → sectionModule R M.module S → V) (hadd hsmul hbal)
    (p : C(S, P)) (m : sectionModule R M.module S) :
    tensorLift M S σ v hadd hsmul hbal (inductionTensor R P H M S p m) = v p m := by
  change tensorSum σ v (Finsupp.single (p, m) 1) = _
  rw [tensorSum_single, map_one, one_smul]

private theorem tensor_ext {A : Type (u + 1)} [Ring A] {V : Type (u + 1)}
    [AddCommGroup V] [Module A V] {S : Profinite.{u}}
    {σ : inductionSectionRing R S →+* A} (M : ActionModule R H.toSubgroup)
    (f g : InductionSection R P H M S →ₛₗ[σ] V)
    (h : ∀ p m, f (inductionTensor R P H M S p m) =
      g (inductionTensor R P H M S p m)) : f = g := by
  have e : f.comp (inductionRelations R P H M S).mkQ =
      g.comp (inductionRelations R P H M S).mkQ := by
    apply Finsupp.lhom_ext
    rintro ⟨p, m⟩ a
    have ha := congrArg (fun x ↦ σ a • x) (h p m)
    simpa only [inductionTensor, ← map_smulₛₗ, ← map_smul, Finsupp.smul_single,
      smul_eq_mul, mul_one, LinearMap.comp_apply] using ha
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (inductionRelations R P H M S).mkQ_surjective x
  exact LinearMap.congr_fun e x

/-- The concrete quotient has its semilinear balanced universal property.
Source: induction steps 2--3 (blueprint: lem-sfb-condensed-tensor-presheaf).
Proof: sum sigma(a)v(p,m) on finite formal sums. The three relation families map
to zero, so the map descends; pure generators span the quotient and give uniqueness. -/
theorem inductionTensorLift_unique {A : Type (u + 1)} [Ring A] {V : Type (u + 1)}
    [AddCommGroup V] [Module A V] (M : ActionModule R H.toSubgroup) (S : Profinite.{u})
    (σ : inductionSectionRing R S →+* A)
    (v : C(S, P) → sectionModule R M.module S → V)
    (hadd : ∀ p m n, v p (m + n) = v p m + v p n)
    (hsmul : ∀ p a m, v p (a • m) = σ a • v p m)
    (hbal : ∀ p h m, v (p * (inductionSubgroupInclusion P H).toContinuousMap.comp h) m =
      v p (M.act S h m)) :
    ∃! F : InductionSection R P H M S →ₛₗ[σ] V,
      ∀ p m, F (inductionTensor R P H M S p m) = v p m := by
  refine ⟨tensorLift M S σ v hadd hsmul hbal,
    tensorLift_tensor M S σ v hadd hsmul hbal, ?_⟩
  intro F hF
  apply tensor_ext M
  intro p m
  rw [hF, tensorLift_tensor]

/-- Pure tensors determine a semilinear map out of the concrete quotient.
Source: the finite-sum presentation, induction steps 2--3
(blueprint: lem-sfb-condensed-tensor-presheaf).
Proof: precompose with the quotient map and use finite-support linear
extensionality; scalar multiples of the coefficient-one generators suffice. -/
theorem inductionTensor_hom_ext {A : Type (u + 1)} [Ring A] {V : Type (u + 1)}
    [AddCommGroup V] [Module A V] {S : Profinite.{u}}
    {σ : inductionSectionRing R S →+* A} (M : ActionModule R H.toSubgroup)
    (f g : InductionSection R P H M S →ₛₗ[σ] V)
    (h : ∀ p m, f (inductionTensor R P H M S p m) =
      g (inductionTensor R P H M S p m)) : f = g :=
  tensor_ext M f g h

private abbrev moduleSections (M : ActionModule R H.toSubgroup) :=
  ((InternalAbelianSheafModule.sectionModuleFunctor
    (coherentTopology Profinite.{u}) R.X).obj M.module).val

private def tensorRestrict (M : ActionModule R H.toSubgroup) {S T : Profinite.{u}}
    (t : T ⟶ S) : InductionSection R P H M S →ₛₗ[
      ((inductionRingSheaf R).obj.map t.op).hom] InductionSection R P H M T :=
  tensorLift M S ((inductionRingSheaf R).obj.map t.op).hom
    (fun p m ↦ inductionTensor R P H M T (p.comp t.hom.hom)
      ((moduleSections M).restrictₛₗ t.op m))
    (by intros; rw [map_add, tensor_add])
    (by intros; rw [map_smulₛₗ, tensor_smul]; rfl)
    (by
      intro p h m
      rw [show (p * (inductionSubgroupInclusion P H).toContinuousMap.comp h).comp
          t.hom.hom = p.comp t.hom.hom *
            (inductionSubgroupInclusion P H).toContinuousMap.comp (h.comp t.hom.hom) by rfl,
        tensor_balance]
      congr 1
      exact (M.naturality S T t h m).symm)

private theorem tensorRestrict_tensor (M : ActionModule R H.toSubgroup)
    {S T : Profinite.{u}} (t : T ⟶ S) (p : C(S, P)) (m : sectionModule R M.module S) :
    tensorRestrict M t (inductionTensor R P H M S p m) =
      inductionTensor R P H M T (p.comp t.hom.hom)
        ((M.module.X.obj.map t.op).hom m) :=
  tensorLift_tensor M S _ _ _ _ _ p m

private def tensorPresheaf (M : ActionModule R H.toSubgroup) :
    PresheafOfModules.{u + 1} (inductionRingSheaf R).obj where
  obj S := ModuleCat.of _ (InductionSection R P H M S.unop)
  map {X Y} t := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((inductionRingSheaf R).obj.map t).hom).obj
      (ModuleCat.of _ (InductionSection R P H M Y.unop)))
    { toFun := tensorRestrict M t.unop
      map_add' := map_add _
      map_smul' := fun a m ↦ (tensorRestrict M t.unop).map_smulₛₗ a m }
  map_id X := by
    apply ModuleCat.hom_ext
    apply tensor_ext M
    intro p m
    change tensorRestrict M (𝟙 X.unop) (inductionTensor R P H M X.unop p m) =
      inductionTensor R P H M X.unop p m
    rw [tensorRestrict_tensor]
    exact congrArg (inductionTensor R P H M X.unop p)
      (ConcreteCategory.congr_hom (M.module.X.obj.map_id X) m)
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply tensor_ext M
    intro p m
    change tensorRestrict M (f ≫ g).unop (inductionTensor R P H M _ p m) =
      tensorRestrict M g.unop (tensorRestrict M f.unop (inductionTensor R P H M _ p m))
    rw [tensorRestrict_tensor, tensorRestrict_tensor, tensorRestrict_tensor]
    congr 1
    exact ConcreteCategory.congr_hom (M.module.X.obj.map_comp f g) m

private def tensorMap {M N : ActionModule R H.toSubgroup} (f : M ⟶ N)
    (S : Profinite.{u}) : InductionSection R P H M S →ₗ[inductionSectionRing R S]
      InductionSection R P H N S :=
  tensorLift M S (RingHom.id _) (fun p m ↦
    inductionTensor R P H N S p ((f.val.hom.hom.app (op S)).hom m))
    (by intros; rw [map_add, tensor_add])
    (by
      intro p a m
      change inductionTensor R P H N S p
        (((InternalAbelianSheafModule.sectionModuleFunctor
          (coherentTopology Profinite.{u}) R.X).map f.val).val.app (op S) (a • m)) = _
      rw [map_smul, tensor_smul]
      rfl)
    (by intro p h m; rw [tensor_balance, f.property])

private theorem tensorMap_tensor {M N : ActionModule R H.toSubgroup} (f : M ⟶ N)
    (S : Profinite.{u}) (p : C(S, P)) (m : sectionModule R M.module S) :
    tensorMap f S (inductionTensor R P H M S p m) =
      inductionTensor R P H N S p ((f.val.hom.hom.app (op S)).hom m) :=
  tensorLift_tensor M S _ _ _ _ _ p m

private def tensorPresheafMap {M N : ActionModule R H.toSubgroup} (f : M ⟶ N) :
    tensorPresheaf M ⟶ tensorPresheaf N where
  app S := ModuleCat.ofHom (tensorMap f S.unop)
  naturality {S T} t := by
    apply ModuleCat.hom_ext
    apply tensor_ext M
    intro p m
    change tensorMap f T.unop (tensorRestrict M t.unop
        (inductionTensor R P H M S.unop p m)) =
      tensorRestrict N t.unop (tensorMap f S.unop
        (inductionTensor R P H M S.unop p m))
    rw [tensorRestrict_tensor, tensorMap_tensor, tensorMap_tensor, tensorRestrict_tensor]
    congr 1
    exact ConcreteCategory.congr_hom (f.val.hom.hom.naturality t) m

private def tensorFunctor : ActionModule R H.toSubgroup ⥤
    PresheafOfModules.{u + 1} (inductionRingSheaf R).obj where
  obj := tensorPresheaf
  map := tensorPresheafMap
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro S
    apply ModuleCat.hom_ext
    apply tensor_ext M
    intro p m
    change tensorMap (𝟙 M) S.unop (inductionTensor R P H M S.unop p m) = _
    rw [tensorMap_tensor]
    rfl
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro S
    apply ModuleCat.hom_ext
    apply tensor_ext _
    intro p m
    change tensorMap (f ≫ g) S.unop (inductionTensor R P H _ _ p m) =
      tensorMap g S.unop (tensorMap f S.unop (inductionTensor R P H _ _ p m))
    rw [tensorMap_tensor, tensorMap_tensor, tensorMap_tensor]
    rfl

private def tensorActionMap (M : ActionModule R H.toSubgroup) (S : Profinite.{u})
    (g : C(S, P)) : Module.End (inductionSectionRing R S) (InductionSection R P H M S) :=
  tensorLift M S (RingHom.id _) (fun p m ↦ inductionTensor R P H M S (g * p) m)
    (by intros; rw [tensor_add])
    (by intros; rw [tensor_smul]; rfl)
    (by intro p h m; rw [← mul_assoc, tensor_balance])

private theorem tensorActionMap_tensor (M : ActionModule R H.toSubgroup)
    (S : Profinite.{u}) (g p : C(S, P)) (m : sectionModule R M.module S) :
    tensorActionMap M S g (inductionTensor R P H M S p m) =
      inductionTensor R P H M S (g * p) m :=
  tensorLift_tensor M S _ _ _ _ _ p m

private def tensorAction (M : ActionModule R H.toSubgroup) (S : Profinite.{u}) :
    C(S, P) →* Module.End (inductionSectionRing R S) (InductionSection R P H M S) where
  toFun := tensorActionMap M S
  map_one' := by
    apply tensor_ext M
    intro p m
    rw [tensorActionMap_tensor, one_mul]
    rfl
  map_mul' g h := by
    apply tensor_ext M
    intro p m
    change tensorActionMap M S (g * h) (inductionTensor R P H M S p m) =
      tensorActionMap M S g (tensorActionMap M S h (inductionTensor R P H M S p m))
    simp only [tensorActionMap_tensor, mul_assoc]

variable (R P H)

/-- The quotient modules assemble into the tensor presheaf, with their specified maps
and left action. Source: induction argument, steps 2--3
(blueprint: lem-sfb-condensed-tensor-presheaf).

Proof: restrict coefficients and send (p,m) to (p composed with t,t*m). Each of the
three families of relations is preserved; for balancing use naturality of M's
action. The resulting semilinear quotient maps have identity and composition laws
on generators, hence on all finite sums. Left multiplication preserves the same
relations by associativity. It gives a monoid homomorphism into linear
endomorphisms and commutes with restrictions. An equivariant morphism acts on m;
its equivariance preserves balancing. Identity and composition hold on generators.
This constructs the functor, section isomorphisms, and every displayed formula.
-/
theorem tensorInductionPresheaf_exists : Nonempty (TensorInductionPresheaf R P H) := by
  refine ⟨{
    functor := tensorFunctor
    sectionIso := fun _ _ ↦ LinearEquiv.refl _ _
    restriction := fun M S T t p m ↦ tensorRestrict_tensor M t p m
    map_tensor := fun M N f S p m ↦ tensorMap_tensor f S p m
    action := tensorAction
    action_tensor := tensorActionMap_tensor
    action_naturality := ?_ }⟩
  intro M S T t g x
  have he : (tensorRestrict M t).comp (tensorActionMap M S g) =
      (tensorActionMap M T (g.comp t.hom.hom)).comp (tensorRestrict M t) := by
    apply tensor_ext M
    intro p m
    change tensorRestrict M t
        (tensorActionMap M S g (inductionTensor R P H M S p m)) =
      tensorActionMap M T (g.comp t.hom.hom)
        (tensorRestrict M t (inductionTensor R P H M S p m))
    rw [tensorActionMap_tensor, tensorRestrict_tensor,
      tensorRestrict_tensor, tensorActionMap_tensor]
    rfl
  exact LinearMap.congr_fun he x

end Profinite.CondensedAction
