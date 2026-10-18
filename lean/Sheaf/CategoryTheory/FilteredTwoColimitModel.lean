/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # An explicit filtered two-colimit and its comparison functor

Source: blueprint, `sec-six-functors-basics/sk-def-sfb-filtered-two-colimit/`,
`det-def-sfb-filtered-two-colimit-model.md`
(blueprint: det-def-sfb-filtered-two-colimit-model).

## Main definitions

* `CoherentCategoryCocone`: normalized pseudofunctor and cocone coherence.
* `FilteredTwoColimit.HomSet`: Mathlib's colimit type of the common-stage Hom diagram.
* `FilteredTwoColimit.category`: the category on pairs `(i, x)`.
* `FilteredTwoColimit.comparison`: the comparison to the cocone vertex.
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

variable {I : Type w} [Preorder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : Type u'} [Category.{v'} D]

/-- Coherent transition data used by the explicit filtered two-colimit model.

Source: blueprint, det-def-sfb-filtered-two-colimit-model, coherence clauses.
(blueprint: det-def-sfb-filtered-two-colimit-model).

The equations are written componentwise.  The `HEq` fields express the identity
normalizations whose source and target functors are definitionally different until
the corresponding identity transition is identified with the identity functor. -/
structure CoherentCategoryCocone (C : I → Type u) (D : Type u')
    [∀ i, Category.{v} (C i)] [Category.{v'} D] extends
    CategoryCocone C D where
  /-- Pseudofunctorial comparison isomorphisms for composable transitions. -/
  tau : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
    T hij ⋙ T hjk ≅ T (hij.trans hjk)
  /-- The transition on an identity index is the identity functor. -/
  transition_identity : ∀ i, T (le_refl i) = 𝟭 (C i)
  /-- The cocone is normalized at an identity index. -/
  cocone_identity : ∀ i,
    HEq (iso (le_refl i)) (Iso.refl (Φ i))
  /-- The two unit cases of the pseudofunctorial comparison are identities. -/
  tau_identity_left : ∀ {i j : I} (hij : i ≤ j),
    HEq (tau (le_refl i) hij) (Iso.refl (T hij))
  tau_identity_right : ∀ {i j : I} (hij : i ≤ j),
    HEq (tau hij (le_refl j)) (Iso.refl (T hij))
  /-- The pseudofunctorial comparisons satisfy the cocycle equation. -/
  tau_cocycle : ∀ {i j k l : I} (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l)
      (x : C i),
    (T hkl).map ((tau hij hjk).hom.app x) ≫
        (tau (hij.trans hjk) hkl).hom.app x =
      (tau hjk hkl).hom.app ((T hij).obj x) ≫
        (tau hij (hjk.trans hkl)).hom.app x
  /-- The cocone is compatible with the pseudofunctorial comparisons. -/
  compatibility : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : C i),
    (iso (hij.trans hjk)).hom.app x =
      (Φ k).map ((tau hij hjk).inv.app x) ≫
        (iso hjk).hom.app ((T hij).obj x) ≫ (iso hij).hom.app x


namespace FilteredTwoColimit

variable (c : CoherentCategoryCocone C D)

/-- The common upper stages of two indices. Source: blueprint, model, Hom clause
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def CommonStage (i j : I) : Type w := {k : I // i ≤ k ∧ j ≤ k}

/-- The inherited preorder of common stages. Source: blueprint, model, Hom clause
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
instance commonStagePreorder (i j : I) : Preorder (CommonStage i j) :=
  inferInstanceAs (Preorder {k : I // i ≤ k ∧ j ≤ k})

/-- The Hom-set at a common stage. Source: blueprint, model, Hom clause
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def HomAt {i j : I} (x : C i) (y : C j) (k : CommonStage i j) : Type v :=
  (c.T k.2.1).obj x ⟶ (c.T k.2.2).obj y

/-- Transport of a Hom representative, with the specified tau conjugations.
Source: blueprint, model, formula for t (blueprint: det-def-sfb-filtered-two-colimit-model). -/
def homTransition {i j : I} (x : C i) (y : C j) {k l : CommonStage i j}
    (h : k ≤ l) (g : HomAt c x y k) : HomAt c x y l :=
  (c.tau k.2.1 h).inv.app x ≫ (c.T h).map g ≫ (c.tau k.2.2 h).hom.app y

/-- Hom transport on an identity stage is the identity. Source: blueprint, model, proof 1
(blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: Use T_kk = Id and both normalized tau unit identities in the conjugation formula. -/
theorem homTransition_id {i j : I} (x : C i) (y : C j) (k : CommonStage i j)
    (g : HomAt c x y k) : homTransition c x y (le_refl k) g = g := by
  sorry

/-- Hom transport is transitive. Source: blueprint, model, proof 1
(blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: Expand the two conjugations. Apply the tau cocycle at x and y and naturality
of tau to g. Cancel inverse comparisons to obtain the single conjugation. -/
theorem homTransition_comp {i j : I} (x : C i) (y : C j)
    {k l m : CommonStage i j} (h : k ≤ l) (h' : l ≤ m) (g : HomAt c x y k) :
    homTransition c x y (h.trans h') g =
      homTransition c x y h' (homTransition c x y h g) := by
  sorry

/-- The diagram of Hom-sets with its prescribed transitions. Source: blueprint, model,
Hom clause (blueprint: det-def-sfb-filtered-two-colimit-model). -/
def homDiagram {i j : I} (x : C i) (y : C j) : CommonStage i j ⥤ Type v where
  obj := HomAt c x y
  map h := TypeCat.ofHom (homTransition c x y (leOfHom h))
  map_id k := ConcreteCategory.hom_ext _ _ (homTransition_id c x y k)
  map_comp h h' :=
    ConcreteCategory.hom_ext _ _ (homTransition_comp c x y (leOfHom h) (leOfHom h'))

/-- The filtered colimit of the common-stage Hom-sets, using Mathlib's colimit type.
Source: blueprint, model, Hom clause (blueprint: det-def-sfb-filtered-two-colimit-model). -/
def HomSet {i j : I} (x : C i) (y : C j) : Type (max w v) :=
  (homDiagram c x y).ColimitType

/-- A Hom representative, as the sigma type used by Mathlib's colimit construction.
Source: blueprint, model, notation [k,g] (blueprint: det-def-sfb-filtered-two-colimit-model). -/
def HomRepresentative {i j : I} (x : C i) (y : C j) : Type (max w v) :=
  Σ k : CommonStage i j, HomAt c x y k

/-- The class [k,g] in the Hom colimit. Source: blueprint, model, Hom clause
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def homClass {i j : I} {x : C i} {y : C j} (k : CommonStage i j)
    (g : HomAt c x y k) : HomSet c x y :=
  (homDiagram c x y).ιColimitType k g

/-- The Hom-colimit coprojections respect transition maps.
Source: blueprint, model, proof step 2, the compatible coprojections
(blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: Apply Mathlib's ιColimitType_map to the arrow h of homDiagram. Its underlying
map is the stated homTransition, so the two displayed classes agree. -/
theorem homClass_transition {i j : I} (x : C i) (y : C j)
    {k l : CommonStage i j} (h : k ⟶ l) (g : HomAt c x y k) :
    homClass c l (homTransition c x y (leOfHom h) g) = homClass c k g := by
  sorry

/-- The actual Hom colimit cocone in a universe containing both the indices and Hom-sets.
ULift only places the stage sets in that universe; its elements are the same stage
morphisms. Source: blueprint, model, Hom clause and proof step 2
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def homCocone {i j : I} (x : C i) (y : C j) :
    Limits.Cocone (homDiagram c x y ⋙ uliftFunctor.{w, v}) where
  pt := HomSet c x y
  ι :=
    { app := fun k ↦ TypeCat.ofHom (fun g ↦ homClass c k g.down)
      naturality := fun _ _ h ↦
        ConcreteCategory.hom_ext _ _ (fun g ↦ homClass_transition c x y h g.down) }

/-- The constructed Hom-set and coprojections have the colimit universal property.
Source: blueprint, model, proof step 2, using def-weil-pbc-category-colimit
(blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: Given any cocone with vertex S, send [k,g] to the k-th cocone map applied to
ULift.up g. Cocone compatibility makes this assignment respect the generating relation
of Mathlib's ColimitType, so Quot.lift defines the induced map. Its value on every
coprojection is prescribed. Every colimit-type element is represented by some (k,g),
so any two maps with these values agree. This provides IsColimit for homCocone. -/
theorem homCocone_isColimit {i j : I} (x : C i) (y : C j) :
    Nonempty (Limits.IsColimit (homCocone c x y)) := by
  sorry

/-- Pair objects (i,x). Source: blueprint, model, object clause
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def Object : Type (max w u) := Σ i : I, C i

/-- The class of the identity at its original stage. The transported object is x by
normalization of T_ii. Source: blueprint, model, identity clause
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def identityHom (X : Object (I := I) (C := C)) : HomSet c X.2 X.2 :=
  homClass c ⟨X.1, le_refl X.1, le_refl X.1⟩ (𝟙 _)

-- Stacks' directedness convention includes a nonempty index category; Mathlib's
-- `IsDirected` class records only common upper bounds, so retain the nonemptiness
-- hypothesis explicitly for the filtered colimit model.
variable [IsDirected I (· ≤ ·)] [Nonempty I]

/-- Every common-stage indexing category is filtered. Source: blueprint, model, proof 1
(blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: Directedness gives an upper bound for i and j and hence a common-stage object.
An upper bound of two common stages is again a common stage. All parallel arrows in
this preorder agree, so the equalization condition is automatic. -/
theorem commonStage_isFiltered (i j : I) : IsFiltered (CommonStage i j) := by
  sorry

/-- Equality of Hom classes means equality at some common later stage.
Source: blueprint, model, proof 1 (blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: Install commonStage_isFiltered and take the IsColimit structure asserted by
homCocone_isColimit. Apply the recorded leaf's Types.FilteredColimit.isColimit_eq_iff
to this lifted cocone and ULift.up g, ULift.up g'. Its arrows are exactly inequalities
of common stages, and equality of lifted stage morphisms is equality of their down maps. -/
theorem homClass_eq_iff {i j : I} (x : C i) (y : C j)
    (k l : CommonStage i j) (g : HomAt c x y k) (g' : HomAt c x y l) :
    homClass c k g = homClass c l g' ↔
      ∃ (m : CommonStage i j) (h : k ≤ m) (h' : l ≤ m),
        homTransition c x y h g = homTransition c x y h' g' := by
  sorry

/-- Compose two representatives at any specified common upper stage.
Source: blueprint, model, composition formula
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def compAt {X Y Z : Object (I := I) (C := C)}
    (r : HomRepresentative c X.2 Y.2) (s : HomRepresentative c Y.2 Z.2)
    (m : I) (hr : r.1.1 ≤ m) (hs : s.1.1 ≤ m) : HomSet c X.2 Z.2 :=
  homClass c ⟨m, r.1.2.1.trans hr, s.1.2.2.trans hs⟩
    (homTransition c X.2 Y.2 (l := ⟨m, r.1.2.1.trans hr, r.1.2.2.trans hr⟩) hr r.2 ≫
      homTransition c Y.2 Z.2 (l := ⟨m, s.1.2.1.trans hs, s.1.2.2.trans hs⟩) hs s.2)

/-- Choose a common stage to compute a composite of representatives.
The choice is only from the actual directedness hypothesis, never a postponed theorem.
Source: blueprint, model, composition clause
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
noncomputable def compRepresentative {X Y Z : Object (I := I) (C := C)}
    (r : HomRepresentative c X.2 Y.2) (s : HomRepresentative c Y.2 Z.2) :
    HomSet c X.2 Z.2 :=
  compAt c r s (Classical.choose (directed_of (· ≤ ·) r.1.1 s.1.1))
    (Classical.choose_spec (directed_of (· ≤ ·) r.1.1 s.1.1)).1
    (Classical.choose_spec (directed_of (· ≤ ·) r.1.1 s.1.1)).2

/-- Representative composition is independent of the chosen upper stage.
Source: blueprint, model, proof 2 (blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: Choose a common refinement of m and the stage chosen by compRepresentative.
Hom transport preserves composites, because it is a functor map conjugated by the
endpoint tau isomorphisms. Use transitivity of transport and the colimit relations to
identify both composites with that common-stage composite. -/
theorem compRepresentative_eq_compAt {X Y Z : Object (I := I) (C := C)}
    (r : HomRepresentative c X.2 Y.2) (s : HomRepresentative c Y.2 Z.2)
    (m : I) (hr : r.1.1 ≤ m) (hs : s.1.1 ≤ m) :
    compRepresentative c r s = compAt c r s m hr hs := by
  sorry

/-- Composition respects one generating colimit relation in the second input.
Source: blueprint, model, proof 2 (blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: A generating relation replaces the second input by one transition. Move the
original and new representatives and the first input to a common stage. The two
second inputs then agree by homTransition_comp. Compose there and use
compRepresentative_eq_compAt to remove the two choices of stage. -/
theorem compRepresentative_rel_right {X Y Z : Object (I := I) (C := C)}
    (r : HomRepresentative c X.2 Y.2) (s s' : HomRepresentative c Y.2 Z.2)
    (h : (homDiagram c Y.2 Z.2).ColimitTypeRel s s') :
    compRepresentative c r s = compRepresentative c r s' := by
  sorry

/-- Composition respects one generating colimit relation in the first input.
Source: blueprint, model, proof 2 (blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: Replace the first input by its indicated transition. Move it, the original
input and the second input to a common stage; homTransition_comp identifies the first
inputs there. Compose and use compRepresentative_eq_compAt for both choices. -/
theorem compRepresentative_rel_left {X Y Z : Object (I := I) (C := C)}
    (r r' : HomRepresentative c X.2 Y.2) (s : HomRepresentative c Y.2 Z.2)
    (h : (homDiagram c X.2 Y.2).ColimitTypeRel r r') :
    compRepresentative c r s = compRepresentative c r' s := by
  sorry

/-- Composition on the Hom colimits, descended from actual common-stage composition.
Source: blueprint, model, composition clause
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
noncomputable def compHom {X Y Z : Object (I := I) (C := C)}
    (f : HomSet c X.2 Y.2) (g : HomSet c Y.2 Z.2) : HomSet c X.2 Z.2 :=
  Quot.liftOn₂ f g (compRepresentative c) (compRepresentative_rel_right c)
    (compRepresentative_rel_left c)

/-- The identity on the left acts as identity on the Hom colimit.
Source: blueprint, model, proof 2 (blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: Represent f at a stage. At a common refinement of that stage and X.index,
the identity representative transports to the identity. Composition there is f by
id_comp in that stage category. Apply the colimit transition relation. -/
theorem identity_comp {X Y : Object (I := I) (C := C)} (f : HomSet c X.2 Y.2) :
    compHom c (identityHom c X) f = f := by
  sorry

/-- The identity on the right acts as identity on the Hom colimit.
Source: blueprint, model, proof 2 (blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: Represent f and move it and the identity at Y to a common stage. Hom transport
sends the identity to the identity. Use comp_id in that category and the colimit relation. -/
theorem comp_identity {X Y : Object (I := I) (C := C)} (f : HomSet c X.2 Y.2) :
    compHom c f (identityHom c Y) = f := by
  sorry

/-- Composition on Hom colimits is associative.
Source: blueprint, model, proof 2 (blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: Choose representatives of the three arrows and move all three and all chosen
intermediate composition stages to a common upper stage. Transport preserves composition
and is transitive; compRepresentative_eq_compAt identifies both parenthesizations with
the common-stage composites. Associativity in that category gives their equality. -/
theorem comp_assoc {W X Y Z : Object (I := I) (C := C)}
    (f : HomSet c W.2 X.2) (g : HomSet c X.2 Y.2) (h : HomSet c Y.2 Z.2) :
    compHom c (compHom c f g) h = compHom c f (compHom c g h) := by
  sorry

/-- The category on pairs with the specified Hom colimits and common-stage composition.
Source: blueprint, model, category clause
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
@[instance_reducible]
noncomputable def category : Category (Object (I := I) (C := C)) where
  Hom X Y := HomSet c X.2 Y.2
  id := identityHom c
  comp := compHom c
  id_comp := identity_comp c
  comp_id := comp_identity c
  assoc := comp_assoc c

/-- The specified conjugated image of a Hom representative in the vertex.
Source: blueprint, model, comparison formula
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def mapHomRepresentative {i j : I} {x : C i} {y : C j}
    (r : HomRepresentative c x y) : (c.Φ i).obj x ⟶ (c.Φ j).obj y :=
  (c.iso r.1.2.1).inv.app x ≫ (c.Φ r.1.1).map r.2 ≫ (c.iso r.1.2.2).hom.app y

/-- The representative image respects the generating colimit relation.
Source: blueprint, model, proof 3 (blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: Expand the transported representative. The compatibility equation rewrites the
cocone comparisons at the later stage in terms of the original ones and tau. Cancel
tau and its inverse. Naturality of the cocone isomorphism identifies the remaining
expression with the original conjugated image. -/
theorem mapHomRepresentative_rel {i j : I} {x : C i} {y : C j}
    (r s : HomRepresentative c x y) (h : (homDiagram c x y).ColimitTypeRel r s) :
    mapHomRepresentative c r = mapHomRepresentative c s := by
  sorry

/-- The comparison on a Hom colimit, given by the actual representative formula.
Source: blueprint, model, comparison clause
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def mapHom {i j : I} {x : C i} {y : C j} (f : HomSet c x y) :
    (c.Φ i).obj x ⟶ (c.Φ j).obj y :=
  Quot.liftOn f (mapHomRepresentative c) (mapHomRepresentative_rel c)

/-- The comparison preserves identities.
Source: blueprint, model, proof 3 (blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: On the identity representative, functoriality sends the identity to an identity;
the inverse cocone comparison followed by the comparison cancels. Normalization identifies
T_ii x with x, giving the identity on Phi_i x. -/
theorem mapHom_identity (X : Object (I := I) (C := C)) :
    mapHom c (identityHom c X) = 𝟙 ((c.Φ X.1).obj X.2) := by
  sorry

/-- The comparison preserves composition.
Source: blueprint, model, proof 3 (blueprint: det-def-sfb-filtered-two-colimit-model).
Proof: Choose representatives and move them to one stage. The middle cocone comparison
and its inverse cancel in the composite of their images. Functoriality of Phi at that
stage identifies the remaining expression with the image of the common-stage composite.
Representative independence then gives the result on arbitrary Hom classes. -/
theorem mapHom_comp {X Y Z : Object (I := I) (C := C)}
    (f : HomSet c X.2 Y.2) (g : HomSet c Y.2 Z.2) :
    mapHom c (compHom c f g) = mapHom c f ≫ mapHom c g := by
  sorry

/-- The comparison functor with the specified object and representative maps.
Source: blueprint, model, comparison clause
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
noncomputable def comparison :
    @Functor (Object (I := I) (C := C)) (category c) D inferInstance := by
  letI : Category (Object (I := I) (C := C)) := category c
  exact
    { obj := fun X ↦ (c.Φ X.1).obj X.2
      map := mapHom c
      map_id := mapHom_identity c
      map_comp := mapHom_comp c }

end FilteredTwoColimit
end CategoryTheory
