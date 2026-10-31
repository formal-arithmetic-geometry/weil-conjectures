/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CondensedActionModule
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-! # Sheafified tensor induction for internal condensed modules

Source: main-20261015, direct-image stability, paragraph (3), agent-formulated
induction input, returned proof steps 2--5; external reference WANTED
(blueprint: lem-sfb-condensed-tensor-induction-adjunction).

The balanced section module is a concrete quotient of finite formal sums. The
presheaf and adjunction specifications retain every generator formula. Existence
is asserted without choosing an unspecified functor or a section of a coset map.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.CondensedAction

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- The existing commutative section ring, without a new ring structure.
Source: paragraph (3) (blueprint: lem-sfb-condensed-tensor-induction-adjunction). -/
abbrev inductionSectionRing (S : Profinite.{u}) :=
  (InternalAbelianSheafModule.sectionRings (coherentTopology Profinite.{u}) R.X).obj (op S)

/-- The existing ring sheaf for ordinary module sheafification.
Source: paragraph (3) (blueprint: lem-sfb-condensed-tensor-induction-adjunction). -/
abbrev inductionRingSheaf :=
  (sheafCompose (coherentTopology Profinite.{u}) (forget₂ CommRingCat RingCat)).obj
    (InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) R.X)

variable (P : ProfiniteGrp.{u}) (H : ClosedSubgroup P)

/-- The continuous subgroup inclusion used by restriction of the action.
Source: paragraph (3) (blueprint: lem-sfb-condensed-tensor-induction-adjunction). -/
def inductionSubgroupInclusion : H.toSubgroup →ₜ* P :=
  { H.toSubgroup.subtype with continuous_toFun := continuous_subtype_val }

/-- Relations on the free section module: additivity and scalar linearity in the
second variable, and `[p h] tensor m = [p] tensor h m`. Their span also imposes
balancing by every finite sum in the subgroup algebra. This is the standard
presentation of `R(S)[C(S,P)] tensor_{R(S)[C(S,H)]} M(S)`.
Source: paragraph (3) (blueprint: lem-sfb-condensed-tensor-induction-adjunction). -/
def inductionRelations (M : ActionModule R H.toSubgroup) (S : Profinite.{u}) :
    Submodule (inductionSectionRing R S)
      ((C(S, P) × sectionModule R M.module S) →₀ inductionSectionRing R S) :=
  Submodule.span (inductionSectionRing R S)
    {x | (∃ (p : C(S, P)) (m n : sectionModule R M.module S),
        x = Finsupp.single (p, m + n) 1 - Finsupp.single (p, m) 1 -
          Finsupp.single (p, n) 1) ∨
      (∃ (p : C(S, P)) (a : inductionSectionRing R S) (m : sectionModule R M.module S),
        x = Finsupp.single (p, a • m) 1 - a • Finsupp.single (p, m) 1) ∨
      (∃ (p : C(S, P)) (h : C(S, H.toSubgroup)) (m : sectionModule R M.module S),
        x = Finsupp.single
          (p * ((inductionSubgroupInclusion P H).toContinuousMap.comp h), m) 1 -
          Finsupp.single (p, M.act S h m) 1)}

/-- The balanced tensor section module, constructed as a quotient of finite sums.
Source: paragraph (3) (blueprint: lem-sfb-condensed-tensor-induction-adjunction). -/
abbrev InductionSection (M : ActionModule R H.toSubgroup) (S : Profinite.{u}) :=
  ((C(S, P) × sectionModule R M.module S) →₀ inductionSectionRing R S) ⧸
    inductionRelations R P H M S

/-- The class of the pure tensor `[p] tensor m` in the balanced quotient.
Source: paragraph (3) (blueprint: lem-sfb-condensed-tensor-induction-adjunction). -/
def inductionTensor (M : ActionModule R H.toSubgroup) (S : Profinite.{u})
    (p : C(S, P)) (m : sectionModule R M.module S) : InductionSection R P H M S :=
  (inductionRelations R P H M S).mkQ (Finsupp.single (p, m) 1)

/-- Specification of the tensor presheaf and its natural linear action. The section
isomorphisms identify the prescribed concrete balanced quotient, rather than an
arbitrary module. Restrictions, action and maps are specified on its generators.
Source: paragraph (3) (blueprint: lem-sfb-condensed-tensor-induction-adjunction). -/
structure TensorInductionPresheaf where
  /-- The presheaf functor. -/
  functor : ActionModule R H.toSubgroup ⥤ PresheafOfModules.{u + 1} (inductionRingSheaf R).obj
  /-- Identification with the concrete sectionwise balanced tensor. -/
  sectionIso : ∀ (M : ActionModule R H.toSubgroup) (S : Profinite.{u}),
    InductionSection R P H M S ≃ₗ[inductionSectionRing R S] (functor.obj M).obj (op S)
  /-- Restriction is precomposition on the group section and restriction on the module. -/
  restriction : ∀ (M : ActionModule R H.toSubgroup) (S T : Profinite.{u}) (t : T ⟶ S)
      (p : C(S, P)) (m : sectionModule R M.module S),
    (functor.obj M).map t.op (sectionIso M S (inductionTensor R P H M S p m)) =
      sectionIso M T (inductionTensor R P H M T (p.comp t.hom.hom)
        ((M.module.X.obj.map t.op).hom m))
  /-- The functor map acts on the second tensor factor. -/
  map_tensor : ∀ (M N : ActionModule R H.toSubgroup) (f : M ⟶ N) (S : Profinite.{u})
      (p : C(S, P)) (m : sectionModule R M.module S),
    (functor.map f).app (op S) (sectionIso M S (inductionTensor R P H M S p m)) =
      sectionIso N S (inductionTensor R P H N S p ((f.val.hom.hom.app (op S)).hom m))
  /-- Sectionwise linear action of the continuous-map group. -/
  action : ∀ (M : ActionModule R H.toSubgroup) (S : Profinite.{u}), C(S, P) →*
    Module.End (inductionSectionRing R S) ((functor.obj M).obj (op S))
  /-- The action multiplies the first tensor factor on the left. -/
  action_tensor : ∀ (M : ActionModule R H.toSubgroup) (S : Profinite.{u}) (g p : C(S, P))
      (m : sectionModule R M.module S),
    action M S g (sectionIso M S (inductionTensor R P H M S p m)) =
      sectionIso M S (inductionTensor R P H M S (g * p) m)
  /-- The action commutes with all restrictions. -/
  action_naturality : ∀ (M : ActionModule R H.toSubgroup) (S T : Profinite.{u}) (t : T ⟶ S)
      (g : C(S, P)) (x : (functor.obj M).obj (op S)),
    (functor.obj M).map t.op (action M S g x) =
      action M T (g.comp t.hom.hom) ((functor.obj M).map t.op x)

variable {R P H}

/-- The balanced generator viewed in the tensor presheaf.
Source: paragraph (3) (blueprint: lem-sfb-condensed-tensor-induction-adjunction). -/
def TensorInductionPresheaf.tensor (B : TensorInductionPresheaf R P H)
    (M : ActionModule R H.toSubgroup) (S : Profinite.{u}) (p : C(S, P))
    (m : sectionModule R M.module S) : (B.functor.obj M).obj (op S) :=
  B.sectionIso M S (inductionTensor R P H M S p m)

/-- The sheafification unit transported through a specified comparison to the
internal-module realization. It sends `[p] tensor m` to its sheafified section.
Source: paragraph (3) (blueprint: lem-sfb-condensed-tensor-induction-adjunction). -/
def TensorInductionPresheaf.sheafTensor (B : TensorInductionPresheaf R P H)
    (L : ActionModule R H.toSubgroup ⥤ ActionModule R P)
    (comparison : (L ⋙ forgetAction) ⋙
        InternalAbelianSheafModule.sectionModuleFunctor (coherentTopology Profinite.{u}) R.X ≅
      B.functor ⋙ PresheafOfModules.sheafification (𝟙 (inductionRingSheaf R).obj))
    (M : ActionModule R H.toSubgroup) (S : Profinite.{u}) (p : C(S, P))
    (m : sectionModule R M.module S) : sectionModule R (L.obj M).module S :=
  (comparison.inv.app M).val.app (op S)
    ((toSheafify (coherentTopology Profinite.{u}) (B.functor.obj M).presheaf).app (op S)
      (B.tensor M S p m))

/-- Ordinary module sheafification of the balanced presheaf, with its induced
linear action, additive functor, and the normalized Frobenius adjunction.
An adjunction includes inverse bijections and their naturality in both variables;
the two displayed transpose formulas fix these particular bijections.
Source: paragraph (3) (blueprint: lem-sfb-condensed-tensor-induction-adjunction). -/
structure TensorInductionSheafAdjunction (B : TensorInductionPresheaf R P H) where
  /-- The sheafified induction functor. -/
  functor : ActionModule R H.toSubgroup ⥤ ActionModule R P
  /-- Induction is additive. -/
  additive : functor.Additive
  /-- Its underlying module sheaf is ordinary module sheafification, naturally in M. -/
  comparison : (functor ⋙ forgetAction) ⋙
      InternalAbelianSheafModule.sectionModuleFunctor (coherentTopology Profinite.{u}) R.X ≅
    B.functor ⋙ PresheafOfModules.sheafification (𝟙 (inductionRingSheaf R).obj)
  /-- Sheafification carries the action through the ordinary unit. -/
  induced_action : ∀ (M : ActionModule R H.toSubgroup) (S : Profinite.{u}) (g : C(S, P))
      (x : (B.functor.obj M).obj (op S)),
    (functor.obj M).act S g ((comparison.inv.app M).val.app (op S)
      ((toSheafify (coherentTopology Profinite.{u}) (B.functor.obj M).presheaf).app (op S) x)) =
    (comparison.inv.app M).val.app (op S)
      ((toSheafify (coherentTopology Profinite.{u}) (B.functor.obj M).presheaf).app (op S)
        (B.action M S g x))
  /-- The map of sheafified induction is the specified extension on pure tensors. -/
  map_tensor : ∀ (M N : ActionModule R H.toSubgroup) (f : M ⟶ N) (S : Profinite.{u})
      (p : C(S, P)) (m : sectionModule R M.module S),
    (((functor.map f).val.hom.hom.app (op S)).hom)
        (B.sheafTensor functor comparison M S p m) =
      B.sheafTensor functor comparison N S p ((f.val.hom.hom.app (op S)).hom m)
  /-- Induction is left adjoint to restriction along the subgroup inclusion. -/
  adjunction : functor ⊣ inflate (inductionSubgroupInclusion P H)
  /-- The forward bijection evaluates on the sheafified identity tensor. -/
  transpose : ∀ (M : ActionModule R H.toSubgroup) (N : ActionModule R P) (F : functor.obj M ⟶ N)
      (S : Profinite.{u}) (m : sectionModule R M.module S),
    (((adjunction.homEquiv M N F).val.hom.hom.app (op S)).hom m) =
      ((F.val.hom.hom.app (op S)).hom) (B.sheafTensor functor comparison M S 1 m)
  /-- The inverse is the unique sheafified extension of `[p] tensor m` to `p f(m)`. -/
  untranspose : ∀ (M : ActionModule R H.toSubgroup) (N : ActionModule R P)
      (f : M ⟶ (inflate (inductionSubgroupInclusion P H)).obj N),
    ∀ F : functor.obj M ⟶ N,
      (∀ (S : Profinite.{u}) (p : C(S, P)) (m : sectionModule R M.module S),
        ((F.val.hom.hom.app (op S)).hom) (B.sheafTensor functor comparison M S p m) =
          N.act S p ((f.val.hom.hom.app (op S)).hom m)) ↔
      F = (adjunction.homEquiv M N).symm f

/-- Sheafification data before Frobenius reciprocity. The identity tensor is a
morphism of internal H-modules; no adjunction or extension property is included.
Source: steps 4--5 of the induction argument
(blueprint: def-sfb-condensed-tensor-induction-data). -/
structure TensorInductionSheafData (B : TensorInductionPresheaf R P H) where
  /-- The sheafified functor. -/
  functor : ActionModule R H.toSubgroup ⥤ ActionModule R P
  /-- Its ordinary module sheafification comparison. -/
  comparison : (functor ⋙ forgetAction) ⋙
      InternalAbelianSheafModule.sectionModuleFunctor (coherentTopology Profinite.{u}) R.X ≅
    B.functor ⋙ PresheafOfModules.sheafification (𝟙 (inductionRingSheaf R).obj)
  /-- Equivariance of the sheafification unit. -/
  induced_action : ∀ (M : ActionModule R H.toSubgroup) (S : Profinite.{u}) (g : C(S, P))
      (x : (B.functor.obj M).obj (op S)),
    (functor.obj M).act S g ((comparison.inv.app M).val.app (op S)
      ((toSheafify (coherentTopology Profinite.{u}) (B.functor.obj M).presheaf).app (op S) x)) =
    (comparison.inv.app M).val.app (op S)
      ((toSheafify (coherentTopology Profinite.{u}) (B.functor.obj M).presheaf).app (op S)
        (B.action M S g x))
  /-- Maps on tensor generators. -/
  map_tensor : ∀ (M N : ActionModule R H.toSubgroup) (f : M ⟶ N) (S : Profinite.{u})
      (p : C(S, P)) (m : sectionModule R M.module S),
    (((functor.map f).val.hom.hom.app (op S)).hom)
        (B.sheafTensor functor comparison M S p m) =
      B.sheafTensor functor comparison N S p ((f.val.hom.hom.app (op S)).hom m)
  /-- The identity tensor, including its H-equivariance. -/
  identityTensor (M : ActionModule R H.toSubgroup) :
    M ⟶ (inflate (inductionSubgroupInclusion P H)).obj (functor.obj M)
  /-- Normalization of the identity tensor morphism. -/
  identityTensor_apply (M : ActionModule R H.toSubgroup) (S : Profinite.{u})
      (m : sectionModule R M.module S) :
    ((identityTensor M).val.hom.hom.app (op S)).hom m =
      B.sheafTensor functor comparison M S 1 m

end Profinite.CondensedAction
