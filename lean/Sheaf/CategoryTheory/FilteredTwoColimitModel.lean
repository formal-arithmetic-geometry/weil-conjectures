module

public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # The concrete directed category colimit and comparison

Source: blueprint main-20261015, filtered 2-colimit model
(blueprint: det-def-sfb-filtered-two-colimit-model).
-/

@[expose] public section

universe w u v u' v'

namespace CategoryTheory

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : Type u'} [Category.{v'} D]

/-- Normalized coherent cocone. Source: blueprint main-20261015, model, coherence bullets
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
structure CoherentCategoryCocone extends CategoryCocone C D where
  tau : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
    T hij ⋙ T hjk ≅ T (hij.trans hjk)
  transition_identity : ∀ i : I, T (le_refl i) = 𝟭 (C i)
  cocone_identity : ∀ i : I, HEq (iso (le_refl i)) (Iso.refl (Φ i))
  tau_identity_left : ∀ {i j : I} (h : i ≤ j),
    HEq (tau (le_refl i) h) (Iso.refl (T h))
  tau_identity_right : ∀ {i j : I} (h : i ≤ j),
    HEq (tau h (le_refl j)) (Iso.refl (T h))
  tau_cocycle : ∀ {i j k l : I} (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l)
    (x : C i),
    (T hkl).map ((tau hij hjk).hom.app x) ≫
        (tau (hij.trans hjk) hkl).hom.app x =
      (tau hjk hkl).hom.app ((T hij).obj x) ≫
        (tau hij (hjk.trans hkl)).hom.app x
  compatibility : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : C i),
    (iso (hij.trans hjk)).hom.app x =
      (Φ k).map ((tau hij hjk).inv.app x) ≫
        (iso hjk).hom.app ((T hij).obj x) ≫ (iso hij).hom.app x

namespace FilteredTwoColimit

variable (c : CoherentCategoryCocone (C := C) (D := D))

/-- Pair objects. Source: blueprint model, objects
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def Object (_c : CoherentCategoryCocone (C := C) (D := D)) : Type (max w u) :=
  Σ i : I, C i

/-- Common upper stages with the inherited preorder. Source: blueprint model, Hom sets
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def CommonStage (i j : I) := {k : I // i ≤ k ∧ j ≤ k}

/-- The inherited order. Source: blueprint model, Hom sets
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
instance commonStagePreorder (i j : I) : Preorder (CommonStage i j) :=
  inferInstanceAs (Preorder {k : I // i ≤ k ∧ j ≤ k})

/-- Hom at a common stage. Source: blueprint model, Hom sets
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def HomAt (a b : Object c) (k : CommonStage a.1 b.1) : Type v :=
  (c.T k.2.1).obj a.2 ⟶ (c.T k.2.2).obj b.2

/-- Transition by conjugating the transition functor by tau. Source: blueprint model, t_kk'
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def homTransition {a b : Object c} {k l : CommonStage a.1 b.1}
    (h : k ≤ l) (g : HomAt c a b k) : HomAt c a b l :=
  (c.tau k.2.1 h).inv.app a.2 ≫ (c.T h).map g ≫ (c.tau k.2.2 h).hom.app b.2

/-- Source: blueprint model proof, transition laws. Normalization of tau and T gives identity.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem homTransition_id (a b : Object c) (k : CommonStage a.1 b.1)
    (g : HomAt c a b k) : homTransition c (le_refl k) g = g := by
  sorry

/-- Source: blueprint model proof, transition laws. Expand both conjugations, use the cocycle
on their endpoints, and apply naturality of tau to the middle arrow.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem homTransition_comp (a b : Object c) {k l m : CommonStage a.1 b.1}
    (h : k ≤ l) (h' : l ≤ m) (g : HomAt c a b k) :
    homTransition c h' (homTransition c h g) = homTransition c (h.trans h') g := by
  sorry

/-- The Hom diagram. Source: blueprint model, H_k and t_kk'
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def homDiagram (a b : Object c) : CommonStage a.1 b.1 ⥤ Type v where
  obj k := HomAt c a b k
  map h := TypeCat.ofHom (homTransition c (leOfHom h))
  map_id k := ConcreteCategory.hom_ext _ _ (homTransition_id c a b k)
  map_comp h h' := ConcreteCategory.hom_ext _ _
    (fun g => (homTransition_comp c a b (leOfHom h) (leOfHom h') g).symm)

/-- The actual set colimit, with no smallness restriction on the index. Source: blueprint model
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def HomSet (a b : Object c) : Type (max w v) := (homDiagram c a b).ColimitType

/-- A representative consists of a common stage and an arrow there. Source: blueprint model
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def HomRepresentative (a b : Object c) := Σ k, HomAt c a b k

/-- The class of a representative. Source: blueprint model, [k,g]
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def homClass {a b : Object c} (k : CommonStage a.1 b.1) (g : HomAt c a b k) :
    HomSet c a b := (homDiagram c a b).ιColimitType k g

/-- Source: blueprint model proof, set colimit. The canonical colimit classes identify an arrow
with its transition image, by the generating relation of the colimit quotient.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem homClass_transition {a b : Object c} {k l : CommonStage a.1 b.1}
    (h : k ≤ l) (g : HomAt c a b k) :
    homClass c l (homTransition c h g) = homClass c k g := by
  sorry

/-- The colimit cocone, lifting stage Hom types into the colimit's universe. Source: blueprint
model, Hom colimit (blueprint: det-def-sfb-filtered-two-colimit-model). -/
def homCocone (a b : Object c) :
    Limits.Cocone (homDiagram c a b ⋙ uliftFunctor.{w, v}) where
  pt := HomSet c a b
  ι :=
    { app k := TypeCat.ofHom (fun g => homClass c k g.down)
      naturality {_ _} h := ConcreteCategory.hom_ext _ _
        (fun g => homClass_transition c (leOfHom h) g.down) }

/-- Source: blueprint model proof, set-colimit universal property. A compatible family on the
lifted Hom diagram factors by sending [k,g] to its value on ULift.up g. Compatibility respects
the quotient relation; uniqueness follows because every class has a representative. This is
exactly the universal property of the recorded category-colimit dependency.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem homCocone_isColimit (a b : Object c) :
    Nonempty (Limits.IsColimit (homCocone c a b)) := by
  sorry

/-- The normalized identity class. Source: blueprint model, identities
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def identityHom (a : Object c) : HomSet c a a :=
  homClass c ⟨a.1, le_refl a.1, le_refl a.1⟩ (𝟙 _)

/-- Source: blueprint model proof, filtered index. Directedness supplies upper bounds of two
common stages and nonemptiness; thinness of a preorder equalizes every parallel pair.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem commonStage_isFiltered [IsDirected I (· ≤ ·)] (i j : I) : IsFiltered (CommonStage i j) := by
  sorry

/-- Source: blueprint model proof, equality of classes; Stacks 04AX. Apply the filtered-set
colimit equality criterion to homCocone_isColimit, using commonStage_isFiltered and cancelling
the ULift on each stage. Thus equality means agreement at a common later stage.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem homClass_eq_iff [IsDirected I (· ≤ ·)] {a b : Object c} (k l : CommonStage a.1 b.1)
    (f : HomAt c a b k) (g : HomAt c a b l) :
    homClass c k f = homClass c l g ↔
      ∃ (m : CommonStage a.1 b.1) (hk : k ≤ m) (hl : l ≤ m),
        homTransition c hk f = homTransition c hl g := by
  sorry

variable [IsDirected I (· ≤ ·)] [Nonempty I]

/-- Composition at a specified common stage. Source: blueprint model, composition formula
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def compAt {a b d : Object c} (f : HomRepresentative c a b)
    (g : HomRepresentative c b d) (m : I) (hf : f.1.1 ≤ m) (hg : g.1.1 ≤ m) :
    HomSet c a d :=
  homClass c ⟨m, f.1.2.1.trans hf, g.1.2.2.trans hg⟩
    (homTransition c (a := a) (b := b)
        (l := ⟨m, f.1.2.1.trans hf, f.1.2.2.trans hf⟩) hf f.2 ≫
      homTransition c (a := b) (b := d)
        (l := ⟨m, g.1.2.1.trans hg, g.1.2.2.trans hg⟩) hg g.2)

/-- Choose an upper bound of two representative stages, then use the displayed composition.
Source: blueprint model, composition (blueprint: det-def-sfb-filtered-two-colimit-model). -/
noncomputable def compRepresentative {a b d : Object c}
    (f : HomRepresentative c a b) (g : HomRepresentative c b d) : HomSet c a d :=
  compAt c f g (Classical.choose (exists_ge_ge f.1.1 g.1.1))
    (Classical.choose_spec (exists_ge_ge f.1.1 g.1.1)).1
    (Classical.choose_spec (exists_ge_ge f.1.1 g.1.1)).2

/-- Source: blueprint model proof, independence of upper bound. Transport both products to one
upper bound of their stages; transition functoriality and cancellation of middle tau factors
give identical products there, hence identical classes.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem compRepresentative_eq_compAt {a b d : Object c}
    (f : HomRepresentative c a b) (g : HomRepresentative c b d)
    (m : I) (hf : f.1.1 ≤ m) (hg : g.1.1 ≤ m) :
    compRepresentative c f g = compAt c f g m hf hg := by
  sorry

/-- Source: blueprint model proof, independence of representatives. A generating relation in the
second input transports it to a later stage. Move both products to one upper stage and use the
transition law and preservation of products to identify them.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem compRepresentative_rel_right {a b d : Object c}
    (f : HomRepresentative c a b) (g g' : HomRepresentative c b d)
    (h : (homDiagram c b d).ColimitTypeRel g g') :
    compRepresentative c f g = compRepresentative c f g' := by
  sorry

/-- Source: blueprint model proof, independence of representatives. For a generating relation in
first input, transport both products to a common upper stage and apply the transition law and
preservation of products. This gives equality of the two classes.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem compRepresentative_rel_left {a b d : Object c}
    (f f' : HomRepresentative c a b) (g : HomRepresentative c b d)
    (h : (homDiagram c a b).ColimitTypeRel f f') :
    compRepresentative c f g = compRepresentative c f' g := by
  sorry

/-- Composition descended to the two set colimits. Source: blueprint model, composition
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
noncomputable def compHom {a b d : Object c}
    (f : HomSet c a b) (g : HomSet c b d) : HomSet c a d :=
  Quot.liftOn₂ f g (compRepresentative c)
    (fun f g g' h => compRepresentative_rel_right c f g g' h)
    (fun f f' g h => compRepresentative_rel_left c f f' g h)

/-- Source: blueprint model proof, identity laws. At a common stage, the identity class becomes
an identity by normalization and functoriality; apply the stage's left identity law.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem identity_comp {a b : Object c} (f : HomSet c a b) :
    compHom c (identityHom c a) f = f := by
  sorry

/-- Source: blueprint model proof, identity laws. Transport to one stage, where the normalized
identity represents the identity and the right identity law applies.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem comp_identity {a b : Object c} (f : HomSet c a b) :
    compHom c f (identityHom c b) = f := by
  sorry

/-- Source: blueprint model proof, associativity. Choose one stage above three representatives;
independence of stages identifies both bracketings with the products there. Apply associativity
in that stage category.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem comp_assoc {a b d e : Object c} (f : HomSet c a b)
    (g : HomSet c b d) (h : HomSet c d e) :
    compHom c (compHom c f g) h = compHom c f (compHom c g h) := by
  sorry

/-- The category with pair objects and filtered-colimit Hom sets. Source: blueprint model
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
noncomputable instance category : Category (Object c) where
  Hom := HomSet c
  id := identityHom c
  comp := compHom c
  id_comp := identity_comp c
  comp_id := comp_identity c
  assoc := comp_assoc c

/-- The comparison formula on representatives. Source: blueprint model, comparison functor
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def mapHomRepresentative {a b : Object c} (f : HomRepresentative c a b) :
    (c.Φ a.1).obj a.2 ⟶ (c.Φ b.1).obj b.2 :=
  (c.iso f.1.2.1).inv.app a.2 ≫ (c.Φ f.1.1).map f.2 ≫ (c.iso f.1.2.2).hom.app b.2

/-- Source: blueprint model proof, comparison descent. Substitute the tau-conjugation formula
and the two cocone compatibility equations. Cancel Phi(tau) factors and use naturality of theta
at the middle arrow. Thus moving to a later stage leaves the image unchanged.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem mapHomRepresentative_rel {a b : Object c}
    (f g : HomRepresentative c a b) (h : (homDiagram c a b).ColimitTypeRel f g) :
    mapHomRepresentative c f = mapHomRepresentative c g := by
  sorry

/-- Comparison on the set-colimit Hom. Source: blueprint model, comparison functor
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
def mapHom {a b : Object c} (f : HomSet c a b) :
    (c.Φ a.1).obj a.2 ⟶ (c.Φ b.1).obj b.2 :=
  Quot.liftOn f (mapHomRepresentative c) (mapHomRepresentative_rel c)

/-- Source: blueprint model proof, comparison identity. Normalization makes theta_ii identity;
Phi_i preserves identity, giving the stated identity morphism.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem mapHom_identity (a : Object c) : mapHom c (identityHom c a) = 𝟙 _ := by
  sorry

/-- Source: blueprint model proof, comparison composition. Represent the two arrows at one
stage, cancel the middle theta and its inverse, and use that Phi at that stage preserves products.
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
theorem mapHom_comp {a b d : Object c} (f : HomSet c a b) (g : HomSet c b d) :
    mapHom c (compHom c f g) = mapHom c f ≫ mapHom c g := by
  sorry

/-- The canonical comparison with the cocone vertex. Source: blueprint model, comparison functor
(blueprint: det-def-sfb-filtered-two-colimit-model). -/
noncomputable def comparison : Object c ⥤ D where
  obj a := (c.Φ a.1).obj a.2
  map := mapHom c
  map_id := mapHom_identity c
  map_comp := mapHom_comp c

end FilteredTwoColimit
end CategoryTheory
