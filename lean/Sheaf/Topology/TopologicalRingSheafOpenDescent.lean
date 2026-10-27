module

public import Mathlib.Topology.Category.TopCommRingCat
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Open-cover descent of sheaves of topological commutative rings

Source: Stacks Project, Tags 0AHY, 00AL, 00AM and 00AN, the topological equalizer
condition and the first compatible-tuple gluing construction
(blueprint: lem-per-topological-ring-sheaf-open-descent).

The sheaves and their morphisms use Mathlib's categorical sheaf definition with values in
`TopCommRingCat`: the sheaf condition is a limit in topological rings, including its topology.
The auxiliary declarations only spell out sections, transitions and the tuple model of this node.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.TopologicalRingDescent

variable {X : TopCat.{u}}

/-- Sections of a local sheaf on the inverse image of an ambient open, i.e. its intersection
with the domain. Source: Stacks 00AL, first proof
(blueprint: lem-per-topological-ring-sheaf-open-descent). -/
abbrev sectionsOn (U : Opens X) (F : (TopCat.of U).Sheaf TopCommRingCat.{w})
    (W : Opens X) : TopCommRingCat.{w} :=
  F.obj.obj (op ((Opens.map U.inclusion').obj W))

/-- The continuous unital restriction on local sections.
Source: Stacks 00AL, first proof
(blueprint: lem-per-topological-ring-sheaf-open-descent). -/
abbrev restrictOn (U : Opens X) (F : (TopCat.of U).Sheaf TopCommRingCat.{w})
    {V W : Opens X} (h : V ≤ W) : sectionsOn U F W ⟶ sectionsOn U F V :=
  F.obj.map ((Opens.map U.inclusion').map (homOfLE h)).op

/-- Transition isomorphisms on all ambient opens contained in a double overlap, with
naturality, identity and cocycle. This is the usual overlap isomorphism written on sections;
opens of the overlap are exactly these ambient opens. Source: Stacks 00AL and 00AN
(blueprint: lem-per-topological-ring-sheaf-open-descent). -/
structure Transitions {A : Type v} (U : A → Opens X)
    (F : ∀ a, (TopCat.of (U a)).Sheaf TopCommRingCat.{w}) where
  iso (a b : A) (V : Opens X) (ha : V ≤ U a) (hb : V ≤ U b) :
    sectionsOn (U a) (F a) V ≅ sectionsOn (U b) (F b) V
  naturality (a b : A) (V W : Opens X) (h : V ≤ W) (ha : W ≤ U a) (hb : W ≤ U b) :
    restrictOn (U a) (F a) h ≫ (iso a b V (h.trans ha) (h.trans hb)).hom =
      (iso a b W ha hb).hom ≫ restrictOn (U b) (F b) h
  identity (a : A) (V : Opens X) (ha : V ≤ U a) : iso a a V ha ha = Iso.refl _
  cocycle (a b c : A) (V : Opens X) (ha : V ≤ U a) (hb : V ≤ U b)
      (hc : V ≤ U c) : iso a b V ha hb ≪≫ iso b c V hb hc = iso a c V ha hc

/-- The commutative subring of compatible tuples, with componentwise operations. Its subtype
has the subspace topology of the product, using `instTopologicalSpaceSubtype`.
Source: Stacks 00AL, first proof, refined by 0AHY
(blueprint: lem-per-topological-ring-sheaf-open-descent). -/
def tupleRing {A : Type v} (U : A → Opens X)
    (F : ∀ a, (TopCat.of (U a)).Sheaf TopCommRingCat.{w})
    (t : Transitions U F) (W : Opens X) :
    Subring (∀ a, sectionsOn (U a) (F a) W) :=
  ⨅ (a : A) (b : A), RingHom.eqLocus
    (((t.iso a b (W ⊓ U a ⊓ U b) (inf_le_left.trans inf_le_right) inf_le_right).hom.val.comp
      (restrictOn (U a) (F a) (inf_le_left.trans inf_le_left)).val).comp
      (Pi.evalRingHom (fun a ↦ sectionsOn (U a) (F a) W) a))
    ((restrictOn (U b) (F b) (inf_le_left.trans inf_le_left)).val.comp
      (Pi.evalRingHom (fun a ↦ sectionsOn (U a) (F a) W) b))

/-- Local identifications of a global sheaf with the given sheaves, natural in every open
contained in each cover member, and compatible with the transitions. Source: Stacks 00AL
(blueprint: lem-per-topological-ring-sheaf-open-descent). -/
structure Identifications {A : Type v} (U : A → Opens X)
    (F : ∀ a, (TopCat.of (U a)).Sheaf TopCommRingCat.{w})
    (t : Transitions U F) (G : X.Sheaf TopCommRingCat.{w}) where
  iso (a : A) (V : Opens X) (ha : V ≤ U a) :
    G.obj.obj (op V) ≅ sectionsOn (U a) (F a) V
  naturality (a : A) (V W : Opens X) (h : V ≤ W) (ha : W ≤ U a) :
    G.obj.map (homOfLE h).op ≫ (iso a V (h.trans ha)).hom =
      (iso a W ha).hom ≫ restrictOn (U a) (F a) h
  overlap (a b : A) (V : Opens X) (ha : V ≤ U a) (hb : V ≤ U b) :
    (iso a V ha).hom ≫ (t.iso a b V ha hb).hom = (iso b V hb).hom

/-- Evaluate a morphism of restricted sheaves on an ambient open contained in the domain,
transporting the image-preimage intersection back to that open. Source: Stacks 00AN
(blueprint: lem-per-topological-ring-sheaf-open-descent). -/
def morphismOn (U : Opens X) (H G : X.Sheaf TopCommRingCat.{w})
    (alpha : U.sheafRestrict.obj H ⟶ U.sheafRestrict.obj G)
    (V : Opens X) (hV : V ≤ U) : H.obj.obj (op V) ⟶ G.obj.obj (op V) :=
  (H.obj.mapIso (eqToIso ((Opens.functor_map_eq_inf U V).trans
    (inf_eq_left.mpr hV))).op).hom ≫
    alpha.hom.app (op ((Opens.map U.inclusion').obj V)) ≫
      (G.obj.mapIso (eqToIso ((Opens.functor_map_eq_inf U V).trans
        (inf_eq_left.mpr hV))).op).inv

/-- Open-cover descent, the literal compatible-tuple section model and componentwise
restrictions, full faithfulness on continuous morphisms, and uniqueness of the descended
object with its identifications. Source: Stacks 0AHY, 00AL, 00AM and 00AN
(blueprint: lem-per-topological-ring-sheaf-open-descent).

Proof:
1. Maps to a subspace of a product are continuous iff all coordinates are continuous
   (def-kun-subspace-topology), also for the empty product.
2. The overlap equations define the subring `tupleRing`. The product and subspace topologies
   make its ring operations continuous, coordinate by coordinate.
3. Restrict each coordinate. Naturality of the transitions preserves the equations;
   the presheaf laws and continuity hold coordinatewise.
4. Glue a compatible covering family separately in every local sheaf. Separatedness on
   triple intersections proves that these coordinates satisfy the transition equations.
   This gives the bijective ring map in the sheaf condition.
5. The inverse gluing map is continuous: each coordinate factors through the local sheaf's
   compatible-family subspace and its continuous gluing inverse. Thus this is a sheaf in
   topological rings, not only a sheaf of rings.
6. On V contained in U_a, projection to a is the local identification. Its inverse has
   b-coordinate theta_ab of the restriction of the given section. The cocycle and identity
   laws prove the inverse identities; coordinate continuity proves both maps continuous.
7. To glue local morphisms H to G, apply them to the restrictions of each section of H and
   glue in G. Uniqueness of gluing proves the ring laws and naturality.
8. This map is continuous through the compatible-family subspace for G: all coordinates
   are continuous. Separatedness gives uniqueness of the global morphism.
9. Glue the local maps between two descended objects and their inverses using steps 7-8.
   Their composites are identities by uniqueness. For an empty cover X is empty; the
   empty-cover sheaf axiom and the empty tuple ring both give the one-element ring.
   Empty, repeated and infinitely many cover members require no change.
-/
theorem openCover_descent
    (X : TopCat.{u}) (A : Type v) (U : A → Opens X) (hcover : iSup U = ⊤)
    (F : ∀ a, (TopCat.of (U a)).Sheaf TopCommRingCat.{max v w})
    (t : Transitions U F) :
    (∃ (G : X.Sheaf TopCommRingCat.{max v w}) (e : Identifications U F t G),
      ∃ model : ∀ W : Opens X, G.obj.obj (op W) = TopCommRingCat.of (tupleRing U F t W),
        (∀ (V W : Opens X) (h : V ≤ W) (s : G.obj.obj (op W)) (a : A),
          ((eqToHom (model V)) (G.obj.map (homOfLE h).op s)).val a =
            restrictOn (U a) (F a) h (((eqToHom (model W)) s).val a)) ∧
        (∀ (a : A) (V : Opens X) (ha : V ≤ U a) (s : G.obj.obj (op V)),
          (e.iso a V ha).hom s =
            ((eqToHom (model V)) s).val a)) ∧
    (∀ (H G : X.Sheaf TopCommRingCat.{max v w})
      (alpha : ∀ a, (U a).sheafRestrict.obj H ⟶ (U a).sheafRestrict.obj G),
      (∀ (a b : A) (V : Opens X) (ha : V ≤ U a) (hb : V ≤ U b),
        morphismOn (U a) H G (alpha a) V ha =
          morphismOn (U b) H G (alpha b) V hb) →
      ∃! f : H ⟶ G, ∀ a, (U a).sheafRestrict.map f = alpha a) ∧
    (∀ (G H : X.Sheaf TopCommRingCat.{max v w})
      (e : Identifications U F t G) (d : Identifications U F t H),
      ∃! f : G ⟶ H, IsIso f ∧
        ∀ (a : A) (V : Opens X) (ha : V ≤ U a),
          f.hom.app (op V) ≫ (d.iso a V ha).hom = (e.iso a V ha).hom) := by
  sorry

end TopCat.TopologicalRingDescent
