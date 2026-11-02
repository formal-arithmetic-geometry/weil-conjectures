/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ClosedUnitIso
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PullbackZero
import WeilConjectures.SmoothPurity.PurityFiniteSetting.TensorPullback
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSingleTensorLax

/-!
# Vanishing of the closed-support cup action

Source: Stacks Project, Cohomology, Tags 0G75 to 0G77, and the finite-coefficient
pro-etale tensor-morphism construction (blueprint: lem-pur-closed-supported-cup-vanishing).
The three helper definitions only specialize the published supported cup to full support
and transport its intersection support along the canonical identity-pullback isomorphism.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Regard an ordinary class as a class with full support using the direct-image
identity isomorphism. Source: the full-support case of the supported-Hom construction,
Stacks 0G76 (blueprint: lem-pur-closed-supported-cup-vanishing). -/
def closedCupFullSupport (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (a t : ℤ)
    (α : P.FunctorialCupOrdinaryH true X a t) : P.FunctorialCupH true (𝟙 X) a t :=
  (P.functorialCupSingle true X).map
    ((ProEtale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).hom.app (P.constant X)) ≫ α

/-- The existing supported cup with first support all of X, transported from
X times_X Z to Z along the canonical second-projection isomorphism.
Source: the tensor-morphism definition of def-pur-supported-cup, and Stacks 0G76
(blueprint: lem-pur-closed-supported-cup-vanishing). -/
def closedSupportedCup (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (i : Z ⟶ X) [IsClosedImmersion i] (a b t s : ℤ)
    (α : P.FunctorialCupOrdinaryH true X a t) (β : P.FunctorialCupH true i b s) :
    P.FunctorialCupH true i (a + b) (t + s) :=
  P.functorialCupChangeSupport true i (ProEtale.cupIntersection (𝟙 X) i)
    (pullback.snd (𝟙 X) i)
    (pullback.condition.symm) (a + b) (t + s)
    (P.functorialCup true (X ↘ Spec (.of P.field.k)) (𝟙 X) i a b t s
      (P.closedCupFullSupport X a t α) β)

/-- The ordinary cup is the full-support specialization of the same supported cup,
followed by the canonical map forgetting full support. Source: Stacks 0G77,
its lower horizontal arrow (blueprint: lem-pur-closed-supported-cup-vanishing). -/
def closedOrdinaryCup (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))] (a b t s : ℤ)
    (α : P.FunctorialCupOrdinaryH true X a t)
    (β : P.FunctorialCupOrdinaryH true X b s) :
    P.FunctorialCupOrdinaryH true X (a + b) (t + s) :=
  P.functorialCupForget true (𝟙 X) (a + b) (t + s)
    (P.closedSupportedCup (𝟙 X) a b t s α (P.closedCupFullSupport X b s β))

private theorem closed_support_map_normalized (P : PurityFiniteSetting.{u})
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (hg : g ≫ i = j) :
    ProEtale.cupCoefficientRestriction P i ≫
      P.functorialCupSupportMap true i j g hg =
      ProEtale.cupCoefficientRestriction P j :=
  (P.functorialCupSupportMap_existsUnique true i j g hg).choose_spec.1

private theorem closed_coefficient_support_naturality_right
    (P : PurityFiniteSetting.{u})
    {Z W W' X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X) (j' : W' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion j']
    (g : W' ⟶ W) (hg : g ≫ j = j')
    (q : pullback i j' ⟶ pullback i j)
    (hq : q ≫ ProEtale.cupIntersection i j =
      ProEtale.cupIntersection i j') :
    ProEtale.cupCoefficientMap P i j ≫
        P.functorialCupSupportMap true (ProEtale.cupIntersection i j)
          (ProEtale.cupIntersection i j') q hq =
      (𝟙 _ ⊗ₘ P.functorialCupSupportMap true j j' g hg) ≫
        ProEtale.cupCoefficientMap P i j' := by
  have : Epi (ProEtale.cupCoefficientRestriction P i) :=
    ProEtale.cupRestriction_epi P i
  have : Epi (ProEtale.cupCoefficientRestriction P j) :=
    ProEtale.cupRestriction_epi P j
  have : Epi (ProEtale.cupCoefficientRestriction P i ▷ P.constant X) :=
    (tensorRight _).map_epi _
  have : Epi ((ProEtale.lowerStar
      (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z) ◁
      ProEtale.cupCoefficientRestriction P j) := (tensorLeft _).map_epi _
  have : Epi (ProEtale.cupCoefficientRestriction P i ⊗ₘ
      ProEtale.cupCoefficientRestriction P j) := by
    rw [MonoidalCategory.tensorHom_def]
    infer_instance
  have hj := closed_support_map_normalized P j j' g hg
  have hq' := closed_support_map_normalized P
    (ProEtale.cupIntersection i j) (ProEtale.cupIntersection i j') q hq
  have hμ := (ProEtale.cupCoefficientMap_existsUnique P i j).exists.choose_spec
  have hμ' := (ProEtale.cupCoefficientMap_existsUnique P i j').exists.choose_spec
  change ProEtale.cupCoefficientRestriction P j ≫
      P.functorialCupSupportMap true j j' g hg =
    ProEtale.cupCoefficientRestriction P j' at hj
  change ProEtale.cupCoefficientRestriction P (ProEtale.cupIntersection i j) ≫
      P.functorialCupSupportMap true (ProEtale.cupIntersection i j)
        (ProEtale.cupIntersection i j') q hq =
    ProEtale.cupCoefficientRestriction P (ProEtale.cupIntersection i j') at hq'
  change (ProEtale.cupCoefficientRestriction P i ⊗ₘ
      ProEtale.cupCoefficientRestriction P j) ≫
      ProEtale.cupCoefficientMap P i j = _ at hμ
  change (ProEtale.cupCoefficientRestriction P i ⊗ₘ
      ProEtale.cupCoefficientRestriction P j') ≫
      ProEtale.cupCoefficientMap P i j' = _ at hμ'
  apply (cancel_epi (ProEtale.cupCoefficientRestriction P i ⊗ₘ
    ProEtale.cupCoefficientRestriction P j)).mp
  rw [← Category.assoc, hμ, Category.assoc, hq']
  rw [← Category.assoc _ (_ ⊗ₘ _), tensorHom_comp_tensorHom]
  simp only [hj]
  exact hμ'.symm

private theorem closed_single_tensor_natural
    {C : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [HasDerivedCategory.{u + 1} C]
    [Abelian.HasFunctorialFlatResolution C]
    {L M M' : C} (t : M ⟶ M') :
    ProEtale.cupSingleTensorMap L M ≫
        (DerivedCategory.singleFunctor C 0).map (𝟙 L ⊗ₘ t) =
      (𝟙 _ ⊗ₘ (DerivedCategory.singleFunctor C 0).map t) ≫
        ProEtale.cupSingleTensorMap L M' := by
  obtain ⟨m, hm⟩ := ProEtale.AffineZeroPurity.coordinate_single_tensor_lax (C := C)
  let := m
  simpa only [id_tensorHom, hm] using
    (Functor.LaxMonoidal.μ_natural_right
      (DerivedCategory.singleFunctor C 0) L t).symm

private theorem closed_derived_coefficient_square
    {C : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [HasDerivedCategory.{u + 1} C]
    [Abelian.HasFunctorialFlatResolution C]
    {L M M' N N' : C} (μ : L ⊗ M ⟶ N) (μ' : L ⊗ M' ⟶ N')
    (t : M ⟶ M') (s : N ⟶ N')
    (h : μ ≫ s = (𝟙 L ⊗ₘ t) ≫ μ') :
    ProEtale.cupDerivedCoefficientMap μ ≫
        (DerivedCategory.singleFunctor C 0).map s =
      (𝟙 _ ⊗ₘ (DerivedCategory.singleFunctor C 0).map t) ≫
        ProEtale.cupDerivedCoefficientMap μ' := by
  unfold ProEtale.cupDerivedCoefficientMap
  rw [Category.assoc, ← Functor.map_comp, h, Functor.map_comp, ← Category.assoc]
  rw [closed_single_tensor_natural]
  simp only [Category.assoc]

private theorem closed_derived_support_square (P : PurityFiniteSetting.{u})
    {Z W W' X : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X) (j' : W' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion j']
    (g : W' ⟶ W) (hg : g ≫ j = j')
    (q : pullback i j' ⟶ pullback i j)
    (hq : q ≫ ProEtale.cupIntersection i j =
      ProEtale.cupIntersection i j') :
    ProEtale.cupDerivedCoefficientMap
        (hD := P.functorialCupHasDerived true X)
        (hDM := P.functorialCupDerivedMonoidal true X)
        (ProEtale.cupCoefficientMap P i j) ≫
      (P.functorialCupSingle true X).map
        (P.functorialCupSupportMap true (ProEtale.cupIntersection i j)
          (ProEtale.cupIntersection i j') q hq) =
      (𝟙 _ ⊗ₘ (P.functorialCupSingle true X).map
        (P.functorialCupSupportMap true j j' g hg)) ≫
        ProEtale.cupDerivedCoefficientMap
          (hD := P.functorialCupHasDerived true X)
          (hDM := P.functorialCupDerivedMonoidal true X)
          (ProEtale.cupCoefficientMap P i j') := by
  have h := closed_coefficient_support_naturality_right P i j j' g hg q hq
  exact closed_derived_coefficient_square
    (ProEtale.cupCoefficientMap P i j)
    (ProEtale.cupCoefficientMap P i j')
    (P.functorialCupSupportMap true j j' g hg)
    (P.functorialCupSupportMap true (ProEtale.cupIntersection i j)
      (ProEtale.cupIntersection i j') q hq) h

private theorem closed_inverse_tensor_square
    {C : Type*} [Category C] [MonoidalCategory C]
    {L M M' N N' F G H : C}
    (θ : L ⊗ M ⟶ N) (θ' : L ⊗ M' ⟶ N') [IsIso θ] [IsIso θ']
    (t : M ⟶ M') (s : N ⟶ N')
    (hs : θ ≫ s = (𝟙 L ⊗ₘ t) ≫ θ')
    (α : L ⟶ F) (β' : M' ⟶ G) (β : M ⟶ G)
    (hβ : t ≫ β' = β) (r : F ⊗ G ⟶ H) :
    s ≫ (inv θ' ≫ (α ⊗ₘ β') ≫ r) = inv θ ≫ (α ⊗ₘ β) ≫ r := by
  have hi : s ≫ inv θ' = inv θ ≫ (𝟙 L ⊗ₘ t) := by
    apply (cancel_epi θ).mp
    rw [← Category.assoc, hs]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc,
      IsIso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc s, hi]
  simp only [Category.assoc]
  rw [← Category.assoc (𝟙 L ⊗ₘ t), tensorHom_comp_tensorHom]
  simp only [Category.id_comp, hβ]

private theorem closed_raw_support_transport (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (i : Z ⟶ X) [IsClosedImmersion i] (a b t s : ℤ)
    (α : P.FunctorialCupH true (𝟙 X) a t)
    (β : P.FunctorialCupH true i b s)
    (q : pullback (𝟙 X) i ⟶ pullback (𝟙 X) (𝟙 X))
    (hq : q ≫ ProEtale.cupIntersection (𝟙 X) (𝟙 X) =
      ProEtale.cupIntersection (𝟙 X) i) :
    (P.functorialCupSingle true X).map
      (P.functorialCupSupportMap true
        (ProEtale.cupIntersection (𝟙 X) (𝟙 X))
        (ProEtale.cupIntersection (𝟙 X) i) q hq) ≫
      P.functorialCup true (X ↘ Spec (.of P.field.k))
        (𝟙 X) i a b t s α β =
    P.functorialCup true (X ↘ Spec (.of P.field.k))
      (𝟙 X) (𝟙 X) a b t s α
        (P.closedCupFullSupport X b s (P.functorialCupForget true i b s β)) := by
  have hr := closed_support_map_normalized P (𝟙 X) i i (by simp)
  have hf := P.restriction_full true X
  have ht : P.functorialCupSupportMap true (𝟙 X) i i (by simp) =
      (ProEtale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).hom.app
        (P.constant X) ≫ P.functorialCupRestriction true i := by
    change P.functorialCupRestriction true (𝟙 X) ≫
      P.functorialCupSupportMap true (𝟙 X) i i (by simp) =
        P.functorialCupRestriction true i at hr
    rw [hf] at hr
    exact (P.functorialCupFullSupportIso true X).inv_comp_eq.mp hr
  have hβ : (P.functorialCupSingle true X).map
      (P.functorialCupSupportMap true (𝟙 X) i i (by simp)) ≫ β =
      P.closedCupFullSupport X b s (P.functorialCupForget true i b s β) := by
    rw [ht, Functor.map_comp]
    simp only [closedCupFullSupport, functorialCupForget, Category.assoc]
  have hs := closed_derived_support_square P (𝟙 X) (𝟙 X) i i (by simp) q hq
  let : IsIso (ProEtale.cupDerivedCoefficientMap
      (hD := P.functorialCupHasDerived true X)
      (hDM := P.functorialCupDerivedMonoidal true X)
      (ProEtale.cupCoefficientMap P (𝟙 X) (𝟙 X))) :=
    P.functorialCupCoefficient_isIso true (𝟙 X) (𝟙 X)
  let : IsIso (ProEtale.cupDerivedCoefficientMap
      (hD := P.functorialCupHasDerived true X)
      (hDM := P.functorialCupDerivedMonoidal true X)
      (ProEtale.cupCoefficientMap P (𝟙 X) i)) :=
    P.functorialCupCoefficient_isIso true (𝟙 X) i
  unfold functorialCup ProEtale.cupComposite
  simp only [Category.assoc]
  exact closed_inverse_tensor_square _ _ _ _ hs α β _ hβ _

/-- The forgetting-support square identifies the ordinary cup with the
forgetful image of the supported cup. Source: Stacks 0G77
(blueprint: lem-pur-closed-ordinary-cup-zero). The proof is the forgetting-support
coefficient restriction square of Tag 0G77, followed by naturality of the
single-tensor comparison and bifunctoriality of tensor. The full-support unitor
and the second-projection support map identify the resulting two composites.
The checked FunctorialCupAlgebraLaws has no cup-forgetting field; its pullback
field and the localization forget_support field do not directly prove this square. -/
theorem closedOrdinaryCupForget_eq (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (i : Z ⟶ X) [IsClosedImmersion i] (a b : ℕ) (t s : ℤ)
    (α : P.FunctorialCupOrdinaryH true X (a : ℤ) t)
    (β : P.FunctorialCupH true i (b : ℤ) s) :
    P.closedOrdinaryCup X a b t s α (P.functorialCupForget true i b s β) =
      P.functorialCupForget true i (a + b) (t + s)
        (P.closedSupportedCup i a b t s α β) := by
  let q : pullback (𝟙 X) i ⟶ pullback (𝟙 X) (𝟙 X) :=
    pullback.lift (pullback.fst (𝟙 X) i)
      (pullback.fst (𝟙 X) i) (by simp only [Category.comp_id])
  have hq : q ≫ ProEtale.cupIntersection (𝟙 X) (𝟙 X) =
      ProEtale.cupIntersection (𝟙 X) i := by
    dsimp only [q, ProEtale.cupIntersection]
    rw [← Category.assoc, pullback.lift_fst]
  have hfull := closed_support_map_normalized P (𝟙 X)
    (ProEtale.cupIntersection (𝟙 X) (𝟙 X))
    (pullback.snd (𝟙 X) (𝟙 X)) pullback.condition.symm
  have hi := closed_support_map_normalized P i
    (ProEtale.cupIntersection (𝟙 X) i)
    (pullback.snd (𝟙 X) i) pullback.condition.symm
  have hq' := closed_support_map_normalized P
    (ProEtale.cupIntersection (𝟙 X) (𝟙 X))
    (ProEtale.cupIntersection (𝟙 X) i) q hq
  have hc := closed_raw_support_transport P i a b t s
    (P.closedCupFullSupport X a t α) β q hq
  unfold closedOrdinaryCup closedSupportedCup functorialCupForget
    functorialCupChangeSupport
  simp only [← Functor.map_comp_assoc]
  rw [show P.functorialCupRestriction true (𝟙 X) ≫
      P.functorialCupSupportMap true (𝟙 X)
        (ProEtale.cupIntersection (𝟙 X) (𝟙 X))
        (pullback.snd (𝟙 X) (𝟙 X)) pullback.condition.symm = _ from hfull]
  rw [show P.functorialCupRestriction true i ≫
      P.functorialCupSupportMap true i (ProEtale.cupIntersection (𝟙 X) i)
        (pullback.snd (𝟙 X) i) pullback.condition.symm = _ from hi]
  rw [← hq', Functor.map_comp, Category.assoc, hc]
  rfl

end WeilConjectures.PurityFiniteSetting
