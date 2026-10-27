/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation
public import Sheaf.CategoryTheory.ProfiniteActionParameters
public import Sheaf.CategoryTheory.ActionToposGeometricRestriction
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Yoneda

/-! # Equivariant Yoneda and free profinite-action evaluation

Source: current blueprint, direct-image stability proof, paragraph (3), auxiliary
profinite-action infrastructure, Yoneda, descent and free evaluation
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation).

The existing small models are reused. The represented-action functor in the statement
is specified by its sections, maps and actual pointwise action, without assuming the
stronger equivalence of topoi in the coherent-presentation theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open Profinite.CondensedAction.CoherentPresentation

namespace Profinite.CondensedAction.YonedaFreeEvaluation

variable (J : Type u) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
  [CompactSpace J] [T2Space J] [TotallyDisconnectedSpace J]

/-- The parameter underlying an action space.
Source: paragraph (3), h_T and X(T)
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation). -/
abbrev base (T : Space J) : Base.{u} := AsSmall.up.obj ((underlying J).obj T)

/-- The whole profinite test parameter J times T.
Source: paragraph (3), the universal equivariance equation
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation). -/
abbrev productParameter (T : Space J) : Base.{u} :=
  AsSmall.up.obj (Profinite.of (J × (underlying J).obj T))

/-- The given jointly continuous action, as a map of profinite parameters.
Source: paragraph (3), alpha_T
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation). -/
def actionMap (T : Space J) : productParameter J T ⟶ base J T :=
  AsSmall.up.map (CompHausLike.ofHom _
    ⟨fun p ↦ ((AsSmall.down.obj T).obj.ρ p.1).hom.hom p.2,
      (AsSmall.down.obj T).property.continuous_smul⟩)

/-- The projection to T in the universal equivariance test.
Source: paragraph (3), pi_T
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation). -/
def secondProjection (T : Space J) : productParameter J T ⟶ base J T :=
  AsSmall.up.map (CompHausLike.ofHom _ ⟨Prod.snd, continuous_snd⟩)

/-- The group-valued section gamma on the whole product parameter.
Source: paragraph (3), gamma
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation). -/
def groupProjection (T : Space J) : (groupPresheaf J).obj (op (productParameter J T)) :=
  ULift.up ⟨Prod.fst, continuous_fst⟩

/-- The specified universal-parameter equation, as an equality of sections.
Source: paragraph (3), Q_X(T)
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation). -/
def IsEquivariantSection (X : Actions J) (T : Space J)
    (x : X.X.obj.obj (op (base J T))) : Prop :=
  X.X.obj.map (actionMap J T).op x =
    InternalActionSite.setAction _ _ _ X (op (productParameter J T))
      (groupProjection J T) (X.X.obj.map (secondProjection J T).op x)

/-- Restricted Yoneda, with precomposition on action spaces and postcomposition on actions.
Source: paragraph (3), Phi
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation). -/
def phiPresheaves (h : Space J ⥤ Actions J) : Actions J ⥤ (Space J)ᵒᵖ ⥤ Type (u + 1) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ (Type (u + 1))).obj h.op

/-- The sheaf-valued restricted Yoneda functor, once the asserted descent is supplied.
Source: paragraph (3), the functor Phi to sheaves on P_J
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation). -/
def phi (h : Space J ⥤ Actions J)
    (hh : ∀ X : Actions J, Presheaf.IsSheaf (coverage J).toGrothendieck
      ((phiPresheaves J h).obj X)) :
    Actions J ⥤ Sheaf (coverage J).toGrothendieck (Type (u + 1)) :=
  ObjectProperty.lift _ (phiPresheaves J h) hh

variable {J}

/-- A component of an equivariant sheaf map, read on an ordinary continuous parameter map.
Source: paragraph (3), b_V(f), using the section identification of h_T
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation). -/
def component (h : Space J ⥤ Actions J)
    (hs : ∀ T : Space J, (h.obj T).X.obj ≅ yoneda.obj (base J T))
    (T : Space J) (X : Actions J) (b : h.obj T ⟶ X) (V : Base.{u})
    (f : parameter V ⟶ (underlying J).obj T) : X.X.obj.obj (op V) :=
  b.hom.hom.app (op V) ((hs T).inv.app (op V) (AsSmall.up.map f))

/-- Evaluation at the identity of the underlying action space.
Source: paragraph (3), the first Yoneda bijection
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation). -/
def identityEvaluation (h : Space J ⥤ Actions J)
    (hs : ∀ T : Space J, (h.obj T).X.obj ≅ yoneda.obj (base J T))
    (X : Actions J) (T : Space J) (b : h.obj T ⟶ X) :
    X.X.obj.obj (op (base J T)) :=
  component h hs T X b (base J T) (𝟙 _)

/-- The map s mapped to (1,s) in the free parameter.
Source: paragraph (3), evaluation on (1,id_S)
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation). -/
def unitParameter (S : Base.{u}) :
    parameter S ⟶ (underlying J).obj ((freeParameter J).obj S) :=
  CompHausLike.ofHom _ ⟨fun s ↦ (1, s), continuous_const.prodMk continuous_id⟩

/-- The canonical free evaluation, with no arbitrary choice of bijection.
Source: paragraph (3), e_(X,S)
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation). -/
def freeEvaluation (h : Space J ⥤ Actions J)
    (hs : ∀ T : Space J, (h.obj T).X.obj ≅ yoneda.obj (base J T))
    (X : Actions J) (S : Base.{u}) (b : h.obj ((freeParameter J).obj S) ⟶ X) :
    X.X.obj.obj (op S) :=
  component h hs ((freeParameter J).obj S) X b S (unitParameter S)

/-- A pair (a,b) as a continuous map into the free action space.
Source: paragraph (3), the inverse free-evaluation formula
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation). -/
def pairedParameter (S V : Base.{u}) (a : (groupPresheaf J).obj (op V))
    (b : V ⟶ S) : parameter V ⟶ (underlying J).obj ((freeParameter J).obj S) :=
  CompHausLike.ofHom _ ⟨fun v ↦ (a.down v, b.down v),
    a.down.continuous.prodMk b.down.hom.hom.continuous⟩

variable (J)

/-- Equivariant Yoneda is descent for the universal action equation, and free evaluation
is naturally bijective with the prescribed inverse on every profinite parameter.
Source: current blueprint, direct-image stability, paragraph (3), auxiliary argument
(blueprint: lem-sfb-profinite-action-yoneda-free-evaluation).
Proof:
1. Represented continuous-map presheaves are sheaves by finite-cover descent
   (lem-sfb-profinite-action-finite-cover-site). Their pointwise actions give h.
   Ordinary Yoneda (lem-galois-yoneda-hom-bijection) identifies maps with X(T).
2. Equivariance implies the equation by testing on J times T with gamma and pi.
   Pull the equation back along (a,f) to recover equivariance on every parameter.
3. Equivariant maps T to T' pull this equation back, and equivariant sheaf maps
   preserve it. Yoneda naturality gives the two displayed naturality formulas.
4. Glue matching sections in X over a finite cover. Pull the equation back over
   J times each covering space. The identities alpha r_i=p_i alpha_i,
   pi r_i=p_i pi_i and gamma r_i=gamma_i make the restrictions equal. Separatedness
   on that cover gives the equation globally, proving the sheaf condition for Phi.
   The empty cover works since sections over the empty space are a singleton.
5. For x in X(S), the formula (a,b) mapped to a acting on b-star x is natural
   and equivariant by the action axioms. At (1,id) it is x.
6. Conversely equivariance and naturality force B(a,b)=a acting on b-star B(1,id).
   Thus free evaluation is bijective. Postcomposition acts by v_S, while
   precomposition along H(f) acts by X(f); these are the two free naturalities.
-/
theorem profiniteAction_yoneda_free_evaluation :
    ∃ (h : Space J ⥤ Actions J)
      (hs : ∀ T : Space J, (h.obj T).X.obj ≅ yoneda.obj (base J T)),
      (∀ (T V : Space J) (f : T ⟶ V),
        (h.map f).hom.hom ≫ (hs V).hom =
          (hs T).hom ≫ yoneda.map (AsSmall.up.map ((underlying J).map f))) ∧
      (∀ (T : Space J) (S : Base.{u}ᵒᵖ) (a : (groupPresheaf J).obj S)
        (x : (h.obj T).X.obj.obj S) (s : parameter S.unop),
        ((hs T).hom.app S (InternalActionSite.setAction _ _ _ (h.obj T) S a x)).down s =
          ((AsSmall.down.obj T).obj.ρ (a.down s)).hom.hom (((hs T).hom.app S x).down s)) ∧
      (∀ X : Actions J, Presheaf.IsSheaf (coverage J).toGrothendieck
        ((phiPresheaves J h).obj X)) ∧
      (∃ q : ∀ (X : Actions J) (T : Space J),
        (h.obj T ⟶ X) ≃ {x : X.X.obj.obj (op (base J T)) // IsEquivariantSection J X T x},
        (∀ (X : Actions J) (T : Space J) (b : h.obj T ⟶ X),
          (q X T b).val = identityEvaluation h hs X T b) ∧
        (∀ (X : Actions J) (T V : Space J) (f : T ⟶ V) (b : h.obj V ⟶ X),
          (q X T (h.map f ≫ b)).val =
            X.X.obj.map (AsSmall.up.map ((underlying J).map f)).op (q X V b).val) ∧
        (∀ (X Y : Actions J) (v : X ⟶ Y) (T : Space J) (b : h.obj T ⟶ X),
          (q Y T (b ≫ v)).val = v.hom.hom.app (op (base J T)) (q X T b).val)) ∧
      (∃ e : ∀ (X : Actions J) (S : Base.{u}),
        (h.obj ((freeParameter J).obj S) ⟶ X) ≃ X.X.obj.obj (op S),
        (∀ (X : Actions J) (S : Base.{u}) (b : h.obj ((freeParameter J).obj S) ⟶ X),
          e X S b = freeEvaluation h hs X S b) ∧
        (∀ (X : Actions J) (S V : Base.{u}) (x : X.X.obj.obj (op S))
          (a : (groupPresheaf J).obj (op V)) (b : V ⟶ S),
          component h hs ((freeParameter J).obj S) X ((e X S).symm x) V
              (pairedParameter S V a b) =
            InternalActionSite.setAction _ _ _ X (op V) a (X.X.obj.map b.op x)) ∧
        (∀ (X Y : Actions J) (v : X ⟶ Y) (S : Base.{u})
          (b : h.obj ((freeParameter J).obj S) ⟶ X),
          e Y S (b ≫ v) = v.hom.hom.app (op S) (e X S b)) ∧
        (∀ (X : Actions J) (S V : Base.{u}) (f : S ⟶ V)
          (b : h.obj ((freeParameter J).obj V) ⟶ X),
          e X S (h.map ((freeParameter J).map f) ≫ b) = X.X.obj.map f.op (e X V b))) := by
  sorry

end Profinite.CondensedAction.YonedaFreeEvaluation
