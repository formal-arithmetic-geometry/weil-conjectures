/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-! # Profinite scheme products and finite label constructions

Source: Stacks 097D and Bhatt--Scholze §7.4.
The explicit product, evaluation sections, and functorial maps are separated from
pointed-cover existence so their comparison theorems can be used in that proof.
(blueprint: def-sfb-profinite-product-maps)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.UniversalCover

/-- The actual scheme `T × P`, using the existing profinite test object, not a product
of underlying sets. Source: Stacks 097D
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable abbrev profiniteProduct (T : Scheme.{u}) (P : Profinite.{u}) : Scheme.{u} :=
  ((ProEtale.profiniteToProEtOf T).obj P).left

/-- The first projection of the profinite product. Source: Stacks 097D
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable abbrev profiniteProductBase (T : Scheme.{u}) (P : Profinite.{u}) :
    profiniteProduct T P ⟶ T :=
  ((ProEtale.profiniteToProEtOf T).obj P).hom

/-- The constant-label section as a scheme morphism, by evaluation of locally constant
integer functions. Source: Stacks 097D
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def profiniteProductSection (T : Scheme.{u}) (P : Profinite.{u}) (p : P) :
    T ⟶ profiniteProduct T P :=
  pullback.lift
    (ProEtale.toSpecZ T ≫ Spec.map (CommRingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp (LocallyConstant.evalRingHom p))))
    (𝟙 T) (by exact (ProEtale.comp_toSpecZ _).trans (Category.id_comp _).symm)

/-- The q-th power of a finite label set. Source: the consecutive-label construction in
§7.4 (blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
def labelPower (q : ℕ) : Type u ⥤ Type u where
  obj A := Fin q → A
  map f := ↾fun a ↦ f ∘ a

/-- The prescribed inverse system `N ↦ ∐_(G/N)^q T`, with quotient transition maps.
Source: Stacks 097D (blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def finiteLabelDiagram (T : Scheme.{u}) (G : ProfiniteGrp.{u}) (q : ℕ) :
    OpenNormalSubgroup G ⥤ Scheme.{u} :=
  ProfiniteGrp.toFiniteQuotientFunctor G ⋙ CategoryTheory.forget FiniteGrp ⋙ labelPower q ⋙
    (sigmaConst.obj T)

/-- Consecutive labels up to the i-th vertex, in their stated order.
Source: the cumulative-label formula in §7.4
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
def cumulativeLabel {G : Type u} [Group G] {q : ℕ} (g : Fin q → G) (i : ℕ) : G :=
  ((List.ofFn g).take i).prod

/-- Restrict a consecutive-label list along an arbitrary simplex map.
Source: the group-nerve construction in §7.4
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
def restrictedLabels {G : Type u} [Group G] {m n : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (g : Fin m → G) : Fin n → G :=
  fun i ↦ (cumulativeLabel g (φ.toOrderHom i.castSucc).val)⁻¹ *
    cumulativeLabel g (φ.toOrderHom i.succ).val

/-- The continuous map of q labels induced by a pointed scheme morphism.
Source: Stacks 0BND (3) (blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def labelMap (G H : ProfiniteGrp.{u}) (ρ : H →* G)
    (hρ : Continuous ρ) (q : ℕ) :
    Profinite.of (Fin q → H) ⟶ Profinite.of (Fin q → G) :=
  ConcreteCategory.ofHom (ContinuousMap.piMap (fun _ : Fin q ↦ ⟨ρ, hρ⟩))

/-- Map of profinite products over a scheme morphism, using the existing test functor.
Source: Stacks 097D and 0BND (3)
(blueprint: lem-sfb-pointed-finite-etale-limit-cover). -/
noncomputable def profiniteProductMap {T T' : Scheme.{u}} (f : T' ⟶ T)
    {P P' : Profinite.{u}} (a : P' ⟶ P) :
    profiniteProduct T' P' ⟶ profiniteProduct T P :=
  pullback.map _ _ _ _ (ProEtale.profiniteToScheme.map a) f
    (𝟙 ProEtale.specZ) (by
      change ProEtale.toSpecZ _ ≫ 𝟙 _ = _ ≫ ProEtale.toSpecZ _
      rw [Category.comp_id]
      exact (ProEtale.comp_toSpecZ _).symm)
    (by
      change ProEtale.toSpecZ T' ≫ 𝟙 _ = f ≫ ProEtale.toSpecZ T
      exact (Category.comp_id _).trans (ProEtale.comp_toSpecZ f).symm)

end AlgebraicGeometry.Scheme.UniversalCover
