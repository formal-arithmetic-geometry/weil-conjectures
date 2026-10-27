/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68, SHEAF group E2
-/
module

public import Sheaf.CategoryTheory.CondensedTensorInductionData
import Sheaf.CategoryTheory.CondensedTensorInductionPresheaf
import Sheaf.CategoryTheory.CondensedTensorInductionSheafification
import Sheaf.CategoryTheory.CondensedTensorInductionExtension

/-! # Sheafified tensor induction for internal condensed modules

Source: direct-image stability, paragraph (3), induction proof steps 2--8.
(blueprint: lem-sfb-condensed-tensor-induction-adjunction).

Reciprocity is assembled from the balanced presheaf, its sheafification, and the
extension formula. Uniqueness, additivity, inverse identities and naturality are
proved here, without an assumed adjunction.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace Profinite.CondensedAction
variable {R : Profinite.CondensedRing.{u}} [IsCommMonObj R.X]
  {P : ProfiniteGrp.{u}} {H : ClosedSubgroup P}

private theorem actionHom_ext {M N : ActionModule R H.toSubgroup} (f g : M ⟶ N)
    (h : ∀ (S : Profinite.{u}) (m : sectionModule R M.module S),
      ((f.val.hom.hom.app (op S)).hom m) =
        ((g.val.hom.hom.app (op S)).hom m)) : f = g := by
  apply Subtype.ext
  apply Mod.hom_ext
  apply Sheaf.hom_ext
  ext S m
  exact h S.unop m

private theorem sheafTensor_ext (B : TensorInductionPresheaf R P H)
    (D : TensorInductionSheafData B) (M : ActionModule R H.toSubgroup)
    (N : ActionModule R P) (f g : D.functor.obj M ⟶ N)
    (h : ∀ (S : Profinite.{u}) (p : C(S, P)) (m : sectionModule R M.module S),
      ((f.val.hom.hom.app (op S)).hom)
          (B.sheafTensor D.functor D.comparison M S p m) =
        ((g.val.hom.hom.app (op S)).hom)
          (B.sheafTensor D.functor D.comparison M S p m)) : f = g := by
  apply Subtype.ext
  apply (InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful
    (coherentTopology Profinite.{u}) R.X).map_injective
  apply (cancel_epi (D.comparison.inv.app M)).mp
  apply (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (inductionRingSheaf R).obj)).injective
  apply PresheafOfModules.hom_ext
  intro X
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (inductionRingSheaf R).obj)).unit.app (B.functor.obj M)
  let ff := (InternalAbelianSheafModule.sectionModuleFunctor
    (coherentTopology Profinite.{u}) R.X).map f.val
  let gg := (InternalAbelianSheafModule.sectionModuleFunctor
    (coherentTopology Profinite.{u}) R.X).map g.val
  let q := (D.comparison.inv.app M).val.app X
  have he := inductionTensor_hom_ext M
    ((ff.val.app X).hom.comp (q.hom.comp
      ((η.app X).hom.comp (B.sectionIso M X.unop).toLinearMap)))
    ((gg.val.app X).hom.comp (q.hom.comp
      ((η.app X).hom.comp (B.sectionIso M X.unop).toLinearMap)))
    (h X.unop)
  ext x
  have hx := LinearMap.congr_fun he ((B.sectionIso M X.unop).symm x)
  change ff.val.app X (q (η.app X
      ((B.sectionIso M X.unop) ((B.sectionIso M X.unop).symm x)))) =
    gg.val.app X (q (η.app X
      ((B.sectionIso M X.unop) ((B.sectionIso M X.unop).symm x)))) at hx
  rw [LinearEquiv.apply_symm_apply] at hx
  exact hx

private theorem sheafTensor_action (B : TensorInductionPresheaf R P H)
    (D : TensorInductionSheafData B) (M : ActionModule R H.toSubgroup)
    (S : Profinite.{u}) (g p : C(S, P)) (m : sectionModule R M.module S) :
    (D.functor.obj M).act S g (B.sheafTensor D.functor D.comparison M S p m) =
      B.sheafTensor D.functor D.comparison M S (g * p) m := by
  unfold TensorInductionPresheaf.sheafTensor TensorInductionPresheaf.tensor
  rw [D.induced_action, B.action_tensor]

private theorem sheafTensor_add (B : TensorInductionPresheaf R P H)
    (D : TensorInductionSheafData B) (M : ActionModule R H.toSubgroup)
    (S : Profinite.{u}) (p : C(S, P)) (m n : sectionModule R M.module S) :
    B.sheafTensor D.functor D.comparison M S p (m + n) =
      B.sheafTensor D.functor D.comparison M S p m +
        B.sheafTensor D.functor D.comparison M S p n := by
  have hr : Finsupp.single (p, m + n) (1 : inductionSectionRing R S) -
      Finsupp.single (p, m) 1 - Finsupp.single (p, n) 1 ∈
        inductionRelations R P H M S :=
    Submodule.subset_span (Or.inl ⟨p, m, n, rfl⟩)
  have ht : inductionTensor R P H M S p (m + n) =
      inductionTensor R P H M S p m + inductionTensor R P H M S p n := by
    apply sub_eq_zero.mp
    rw [sub_add_eq_sub_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hr
  unfold TensorInductionPresheaf.sheafTensor TensorInductionPresheaf.tensor
  rw [ht, map_add, map_add, map_add]

private theorem tensorInduction_additive (B : TensorInductionPresheaf R P H)
    (D : TensorInductionSheafData B) : D.functor.Additive where
  map_add {M N} {f g} := by
    apply sheafTensor_ext B D M (D.functor.obj N)
    intro S p m
    change _ = ((D.functor.map f).val.hom.hom.app (op S)).hom
        (B.sheafTensor D.functor D.comparison M S p m) +
      ((D.functor.map g).val.hom.hom.app (op S)).hom
        (B.sheafTensor D.functor D.comparison M S p m)
    rw [D.map_tensor, D.map_tensor, D.map_tensor]
    exact sheafTensor_add B D N S p _ _

private def tensorHomEquiv (B : TensorInductionPresheaf R P H)
    (D : TensorInductionSheafData B) (M : ActionModule R H.toSubgroup)
    (N : ActionModule R P) :
    (D.functor.obj M ⟶ N) ≃ (M ⟶ (inflate (inductionSubgroupInclusion P H)).obj N) where
  toFun F := D.identityTensor M ≫ (inflate (inductionSubgroupInclusion P H)).map F
  invFun f := (tensorInductionExtension_exists B D M N f).choose
  left_inv F := by
    apply sheafTensor_ext B D M N
    intro S p m
    rw [(tensorInductionExtension_exists B D M N _).choose_spec]
    change N.act S p ((F.val.hom.hom.app (op S)).hom
      (((D.identityTensor M).val.hom.hom.app (op S)).hom m)) = _
    rw [D.identityTensor_apply, ← F.property, sheafTensor_action]
    simp only [mul_one]
  right_inv f := by
    apply actionHom_ext
    intro S m
    change (((tensorInductionExtension_exists B D M N f).choose.val.hom.hom.app
      (op S)).hom) (((D.identityTensor M).val.hom.hom.app (op S)).hom m) = _
    rw [D.identityTensor_apply, (tensorInductionExtension_exists B D M N f).choose_spec]
    simp only [map_one, Module.End.one_apply]

private def tensorAdjunctionCore (B : TensorInductionPresheaf R P H)
    (D : TensorInductionSheafData B) :
    Adjunction.CoreHomEquiv D.functor (inflate (inductionSubgroupInclusion P H)) where
  homEquiv := tensorHomEquiv B D
  homEquiv_naturality_left_symm {M' M N} u f := by
    apply sheafTensor_ext B D M' N
    intro S p m
    change _ = ((tensorHomEquiv B D M N).symm f).val.hom.hom.app (op S)
      (((D.functor.map u).val.hom.hom.app (op S)).hom
        (B.sheafTensor D.functor D.comparison M' S p m))
    rw [D.map_tensor]
    exact ((tensorInductionExtension_exists B D M' N (u ≫ f)).choose_spec S p m).trans
      ((tensorInductionExtension_exists B D M N f).choose_spec S p
        ((u.val.hom.hom.app (op S)).hom m)).symm
  homEquiv_naturality_right F w := by
    apply actionHom_ext
    intro S m
    rfl

/-- Sheafified balanced-tensor induction exists and has the normalized natural
Frobenius adjunction, with no coset section or finite-index hypothesis.

Source: main-20261015, direct-image stability paragraph (3), returned induction
proof steps 2--5, agent-formulated input; external reference WANTED
(blueprint: lem-sfb-condensed-tensor-induction-adjunction).

Proof:
1. Products and equalizers make the small profinite site finitely complete.
   Continuous maps to P form a group sheaf: descend compatible maps along the
   finite coproduct covering surjection, using
   lem-sfb-compact-hausdorff-surjection-quotient, also for the empty cover.
2. Use the displayed finite-sum quotient presentation. Restriction of coefficients,
   precomposition of p and restriction of m preserve additivity, scalar relations
   and balancing because M's action is natural. Identity and composition hold on
   generators. This gives the tensor presheaf of the statement.
3. Left multiplication preserves balancing by associativity. The action laws and
   naturality hold on generators. An equivariant f induces `[p] tensor f(m)`;
   balancing uses f(hm)=hf(m). Identity, composition, sums and zero are checked
   on generators, using def-sfb-condensed-action-module.
4. Apply lem-sfb-equivariant-module-sheafification-reflector to the group sheaf
   of step 1 and R. Use def-weil-pbc-internal-abelian-sheaf-module-equivalence to
   realize the resulting sheaf and action as an internal action module, without
   changing sections. Uniqueness of extensions proves functoriality and additivity.
5. The forward transpose is evaluation on the identity tensor. It is H-equivariant
   because `[h] tensor m = [1] tensor hm`, using balancing and equivariance of F.
6. For f in the other Hom set, `[p] tensor m` maps to p f(m). This is balanced:
   (ph)f(m)=p f(hm), is natural, and is P-equivariant. The reflector of step 4
   supplies its unique equivariant linear sheaf extension, interpreted in the
   internal-module category by the equivalence of step 4.
7. The first composite is f since 1 acts identically. For the other composite,
   equality on every generator gives equality on the presheaf and uniqueness of
   extension gives F. Thus the transposes are inverse.
8. For u in the source and w in the target, evaluating w F L(u) on the identity
   tensor gives Res(w) Phi(F) u. This proves naturality in both variables; the
   inverse maps are natural by bijectivity. No coset representatives were used. -/
theorem exists_tensorInductionAdjunction (R : Profinite.CondensedRing.{u})
    [IsCommMonObj R.X] (P : ProfiniteGrp.{u}) (H : ClosedSubgroup P) :
    ∃ B : TensorInductionPresheaf R P H, Nonempty (TensorInductionSheafAdjunction B) := by
  obtain ⟨B⟩ := tensorInductionPresheaf_exists R P H
  obtain ⟨D⟩ := tensorInductionSheafData_exists R P H B
  let adj := Adjunction.mkOfHomEquiv (tensorAdjunctionCore B D)
  refine ⟨B, ⟨{
    functor := D.functor
    additive := tensorInduction_additive B D
    comparison := D.comparison
    induced_action := D.induced_action
    map_tensor := D.map_tensor
    adjunction := adj
    transpose := ?_
    untranspose := ?_ }⟩⟩
  · intro M N F S m
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    change (F.val.hom.hom.app (op S)).hom
      (((D.identityTensor M).val.hom.hom.app (op S)).hom m) = _
    rw [D.identityTensor_apply]
  · intro M N f F
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    constructor
    · intro h
      apply sheafTensor_ext B D M N
      intro S p m
      exact (h S p m).trans
        ((tensorInductionExtension_exists B D M N f).choose_spec S p m).symm
    · rintro rfl
      exact (tensorInductionExtension_exists B D M N f).choose_spec

end Profinite.CondensedAction
