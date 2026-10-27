/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Sheaf.CategoryTheory.ProfiniteActionYonedaFreeEvaluation
public import Sheaf.CategoryTheory.ProfiniteActionFreeRestriction
public import Sheaf.CategoryTheory.ProfiniteActionParameters
public import Sheaf.CategoryTheory.ActionToposGeometricRestriction
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Topology.ProfiniteCondensedRing

/-! # Action-cover Cech equalizers and natural recovery

Source: current blueprint, direct-image stability, paragraph (3), agent-formulated
auxiliary action-space infrastructure, extracted presentation steps 9 and 10;
Stacks Project, Sites, Tag 00VM for singleton-cover descent
(blueprint: lem-sfb-profinite-action-cech-recovery).

The functors and section identifications are the recorded dependency interfaces.
No equivalence from the downstream coherent-presentation theorem is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open Profinite.CondensedAction.CoherentPresentation
open Profinite.CondensedAction.YonedaFreeEvaluation

namespace Profinite.CondensedAction.CechRecovery

variable (J : Type u) [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
  [CompactSpace J] [T2Space J] [TotallyDisconnectedSpace J]

/-- Equivariance needed to bundle the action map as an action-space morphism.
Source: paragraph (3), extracted step 9, action-cover construction
(blueprint: lem-sfb-profinite-action-cech-recovery).
Proof: the multiplication law of the given action says (gj)t=g(jt). Continuity
is already supplied by the recorded actionMap, using the continuous action. -/
theorem actionCover_wellDefined (T : Space J) (g j : J) (t : (underlying J).obj T) :
    ((AsSmall.down.obj T).obj.ρ (g * j)).hom.hom t =
      ((AsSmall.down.obj T).obj.ρ g).hom.hom
        (((AsSmall.down.obj T).obj.ρ j).hom.hom t) := by
  sorry

/-- The actual continuous equivariant action map a_T(j,t)=jt.
Source: paragraph (3), extracted step 9
(blueprint: lem-sfb-profinite-action-cech-recovery). -/
def actionCover (T : Space J) : (freeParameter J).obj (base J T) ⟶ T :=
  AsSmall.up.map (ObjectProperty.homMk
    { hom := (actionMap J T).down
      comm := fun g ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        exact actionCover_wellDefined J T g x.1 x.2 })

/-- The categorical action-cover fibre square, with its continuous diagonal action.
Source: paragraph (3), extracted step 9
(blueprint: lem-sfb-profinite-action-cech-recovery). -/
abbrev cechSpace (T : Space J) : Space J := pullback (actionCover J T) (actionCover J T)

/-- First projection of the action-cover fibre square.
Source: paragraph (3), extracted step 9
(blueprint: lem-sfb-profinite-action-cech-recovery). -/
abbrev cechFirst (T : Space J) : cechSpace J T ⟶ (freeParameter J).obj (base J T) :=
  pullback.fst (actionCover J T) (actionCover J T)

/-- Second projection of the action-cover fibre square.
Source: paragraph (3), extracted step 9
(blueprint: lem-sfb-profinite-action-cech-recovery). -/
abbrev cechSecond (T : Space J) : cechSpace J T ⟶ (freeParameter J).obj (base J T) :=
  pullback.snd (actionCover J T) (actionCover J T)

/-- The action cover and its coordinate-specified equivariant homeomorphism.
The two projection equations give c(j,k,t)=((j,kt),(jk,t)); the last equation
specifies its inverse on every point of the fibre square. An isomorphism in Space
is precisely an equivariant homeomorphism of the original profinite spaces.
Source: paragraph (3), extracted step 9, proof steps 1 and 2
(blueprint: lem-sfb-profinite-action-cech-recovery).
Proof: a_T is continuous and equivariant, and a_T(1,t)=t, so it is a singleton
cover. For c use ((j,kt),(jk,t)); associativity puts it in the fibre square.
For a fibre-square point ((j,u),(j',v)), ju=j'v implies u=(j^-1*j')v.
Thus d sends it to (j,j^-1*j',v), and cd=dc=1. Multiplication, inversion and
the action are continuous, so both maps are continuous. Left translation in j
proves equivariance. The two projections are H(alpha) and r_gamma followed by H(pi),
using freeRightTranslation from lem-sfb-profinite-action-free-restriction. -/
theorem actionCover_cech (T : Space J) :
    Presieve.singleton (actionCover J T) ∈ coverage J T ∧
    ∃ c : (freeParameter J).obj (productParameter J T) ≅ cechSpace J T,
      c.hom ≫ cechFirst J T = (freeParameter J).map (actionMap J T) ∧
      c.hom ≫ cechSecond J T =
        freeRightTranslation J (productParameter J T) (groupProjection J T).down ≫
          (freeParameter J).map (secondProjection J T) ∧
      (∀ z : (underlying J).obj (cechSpace J T),
        (underlying J).map c.inv z =
          (((underlying J).map (cechFirst J T) z).1,
            ((((underlying J).map (cechFirst J T) z).1)⁻¹ *
              ((underlying J).map (cechSecond J T) z).1,
              ((underlying J).map (cechSecond J T) z).2))) := by
  sorry

/-- Naturality of the action-cover arrow for every equivariant map.
Source: paragraph (3), extracted step 10, proof step 4
(blueprint: lem-sfb-profinite-action-cech-recovery).
Proof: evaluate both sides on (j,t). Equivariance of f gives f(jt)=j f(t),
so the actual continuous maps agree; the small model changes no maps. -/
theorem actionCover_naturality (T V : Space J) (f : T ⟶ V) :
    actionCover J T ≫ f =
      (freeParameter J).map (AsSmall.up.map ((underlying J).map f)) ≫ actionCover J V := by
  sorry

/-- Descent identifies F(T), by the actual pullback F(a_T), with Q_(G(F))(T).
The inverse section identification only transports between the recorded realization
of G and its prescribed sections F(H(T)); it is not an arbitrary comparison map.
Source: paragraph (3), extracted step 9; Stacks Sites, Tag 00VM
(blueprint: lem-sfb-profinite-action-cech-recovery).
Proof: apply the defining sheaf equalizer to the singleton cover actionCover_cech.
Pullback along c is bijective, its inverse being pullback along c.inv. Therefore
it preserves and reflects equality of the two restrictions. The projection equations
identify these restrictions with F(H(alpha)) and F(r_gamma) F(H(pi)), in that order
by contravariance. The sections and action fields of FreeRestriction identify these
with G(F)(alpha) and gamma acting on G(F)(pi). This is precisely IsEquivariantSection
on the whole parameter J times T, not just its ordinary points. -/
theorem actionCover_descent (G : FreeRestriction J)
    (F : Sheaf (coverage J).toGrothendieck (Type (u + 1))) (T : Space J) :
    Set.BijOn
      (fun y ↦ (G.sections F).inv.app (op (base J T))
        (F.obj.map (actionCover J T).op y))
      Set.univ {x | IsEquivariantSection J (G.functor.obj F) T x} := by
  sorry

/-- The two natural recovery isomorphisms with their prescribed evaluations.
The assumptions on h and hs are exactly its represented-section, map and action
normalizations from lem-sfb-profinite-action-yoneda-free-evaluation; hh is that
lemma's sheaf condition, used by its existing phi construction. G is exactly the
normalized free-restriction interface, not an assumed equivalence.
Source: paragraph (3), extracted step 10, proof steps 4--7
(blueprint: lem-sfb-profinite-action-cech-recovery).
Proof:
1. By actionCover_descent, F(a_T) corestricted to Q is bijective. Compose with
   the inverse identity-evaluation bijection from the recorded Yoneda lemma.
   This defines eta with the displayed normalization, and each component is bijective.
2. For equivariant f:T to V, actionCover_naturality gives f a_T=a_V H(f).
   Apply F and the Yoneda restriction formula to obtain eta's object naturality.
   Its inverse is natural by composing with the component inverses.
3. For v:F to F', naturality at a_T gives v_H(T) F(a_T)=F'(a_T) v_T.
   G.maps and Yoneda postcomposition give naturality of eta in F.
4. Use the recorded free-evaluation bijection for epsilon. Its inverse sends x to
   the map (a,b) mapped to a acting on b-star x. Naturality in S follows from
   b_V(1,f)=X(f)b_S(1,id). Postcomposition gives naturality in X.
5. For every continuous g:S to J, restriction by r_g sends b to b composed
   with h(r_g). Evaluation is b_S(g,id)=g acting on b_S(1,id), by equivariance
   of b and the actual pointwise action on h. This proves the displayed intertwining
   formula for arbitrary g, not only constant g. G.action identifies it with the
   internal action on G Phi(X). Bijectivity makes the inverse equivariant as well.
Thus both families are natural isomorphisms in the stated categories. -/
theorem profiniteAction_cech_recovery
    (G : FreeRestriction J) (h : Space J ⥤ Actions J)
    (hs : ∀ T : Space J, (h.obj T).X.obj ≅ yoneda.obj (base J T))
    (hh : ∀ X : Actions J, Presheaf.IsSheaf (coverage J).toGrothendieck
      ((phiPresheaves J h).obj X)) :
    (∀ (T V : Space J) (f : T ⟶ V),
      (h.map f).hom.hom ≫ (hs V).hom =
        (hs T).hom ≫ yoneda.map (AsSmall.up.map ((underlying J).map f))) →
    (∀ (T : Space J) (S : Base.{u}ᵒᵖ) (a : (groupPresheaf J).obj S)
      (x : (h.obj T).X.obj.obj S) (s : parameter S.unop),
      ((hs T).hom.app S (InternalActionSite.setAction _ _ _ (h.obj T) S a x)).down s =
        ((AsSmall.down.obj T).obj.ρ (a.down s)).hom.hom (((hs T).hom.app S x).down s)) →
    ∃ (η : 𝟭 (Sheaf (coverage J).toGrothendieck (Type (u + 1))) ≅
        G.functor ⋙ phi J h hh)
      (ε : phi J h hh ⋙ G.functor ≅ 𝟭 (Actions J)),
      (∀ (F : Sheaf (coverage J).toGrothendieck (Type (u + 1)))
        (T : Space J) (y : F.obj.obj (op T)),
        identityEvaluation h hs (G.functor.obj F) T ((η.hom.app F).hom.app (op T) y) =
          (G.sections F).inv.app (op (base J T)) (F.obj.map (actionCover J T).op y)) ∧
      (∀ (X : Actions J) (S : Base.{u})
        (b : (G.functor.obj ((phi J h hh).obj X)).X.obj.obj (op S)),
        (ε.hom.app X).hom.hom.app (op S) b =
          freeEvaluation h hs X S
            ((G.sections ((phi J h hh).obj X)).hom.app (op S) b)) ∧
      (∀ (X : Actions J) (S : Base.{u}) (g : (groupPresheaf J).obj (op S))
        (b : h.obj ((freeParameter J).obj S) ⟶ X),
        freeEvaluation h hs X S
            (((phi J h hh).obj X).obj.map (freeRightTranslation J S g.down).op b) =
          InternalActionSite.setAction _ _ _ X (op S) g (freeEvaluation h hs X S b)) := by
  sorry

end Profinite.CondensedAction.CechRecovery
