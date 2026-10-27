module

public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import Mathlib.CategoryTheory.Groupoid

/-! # Covering-sieve descent completion of a prestack

Source: Stacks Project, stacks.tex, Tag 02ZN (lemma-stackify), final construction
in both proofs (blueprint: lem-sfb-prestack-sieve-descent-completion).

The helpers below spell out the construction asserted by that node. Sections use
Mathlib's based functors and vertical natural transformations, rather than a second
notion of fibred groupoid. In a fibred groupoid every arrow is cartesian.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe w

open CategoryTheory Opposite

namespace CategoryTheory.Pseudofunctor

variable {C : Type w} [SmallCategory C]

/-- The full sieve category over the base. Source: Stacks Project, Tag 02ZN, final
construction (blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def sieveBasedCategory {T : C} (R : Sieve T) : BasedCategory.{w, w} C :=
  BasedCategory.ofFunctor R.arrows.diagram

/-- The total category with its projection. Source: Stacks Project, Tag 02ZN
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def groupoidBasedCategory (Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}) :
    BasedCategory.{w, w} C :=
  BasedCategory.ofFunctor (CoGrothendieck.forget Q)

/-- Cartesian sections over a sieve, with vertical natural transformations as arrows.
Source: Stacks Project, Tag 02ZN, final construction
(blueprint: lem-sfb-prestack-sieve-descent-completion).
For groupoid fibres the section's arrows are automatically cartesian. -/
abbrev SieveCartesianSection
    (Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}) {T : C} (R : Sieve T) :=
  BasedFunctor (sieveBasedCategory R) (groupoidBasedCategory Q)

/-- Inclusion of sieve categories over the base. Source: Stacks Project, Tag 02ZN
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def sieveBasedInclusion {T : C} {K R : Sieve T} (h : K ≤ R) :
    BasedFunctor (sieveBasedCategory K) (sieveBasedCategory R) where
  toFunctor :=
    { obj := fun f ↦ ⟨f.obj, h _ f.property⟩
      map := fun g ↦ ObjectProperty.homMk g.hom }
  w := rfl

/-- Restrict a section to a subsieve. Source: Stacks Project, Tag 02ZN
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def restrictSieveSection
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}} {T : C}
    {K R : Sieve T} (h : K ≤ R) (x : SieveCartesianSection Q R) :
    SieveCartesianSection Q K :=
  BasedFunctor.comp (sieveBasedInclusion h) x

/-- Restriction of section isomorphisms, given componentwise. Source: Stacks Project,
Tag 02ZN (blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def restrictSieveSectionIso
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}} {T : C}
    {K R : Sieve T} (h : K ≤ R) {x y : SieveCartesianSection Q R} (a : x ≅ y) :
    restrictSieveSection h x ≅ restrictSieveSection h y where
  hom := BasedCategory.whiskerLeft (sieveBasedInclusion h) a.hom
  inv := BasedCategory.whiskerLeft (sieveBasedInclusion h) a.inv
  hom_inv_id := by
    apply BasedNatTrans.ext
    ext f
    exact congrArg (fun b ↦ b.toNatTrans.app ((sieveBasedInclusion h).obj f)) a.hom_inv_id
  inv_hom_id := by
    apply BasedNatTrans.ext
    ext f
    exact congrArg (fun b ↦ b.toNatTrans.app ((sieveBasedInclusion h).obj f)) a.inv_hom_id

/-- The sieve functor induced by composition with a base arrow; no fibre products
are used. Source: Stacks Project, Tag 02ZN
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def sieveBasedPullback {T V : C} (f : V ⟶ T) (R : Sieve T) :
    BasedFunctor (sieveBasedCategory (R.pullback f)) (sieveBasedCategory R) where
  toFunctor :=
    { obj := fun g ↦ ⟨Over.mk (g.obj.hom ≫ f), g.property⟩
      map := fun g ↦ ObjectProperty.homMk (Over.homMk g.hom.left (by
        change g.hom.left ≫ ( _ ≫ f) = _ ≫ f
        rw [← Category.assoc, Over.w])) }
  w := rfl

/-- Pullback is precomposition on the inverse-image sieve. Source: Stacks Project,
Tag 02ZN (blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def pullbackSieveSection
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}} {T V : C}
    (f : V ⟶ T) {R : Sieve T} (x : SieveCartesianSection Q R) :
    SieveCartesianSection Q (R.pullback f) :=
  BasedFunctor.comp (sieveBasedPullback f R) x

/-- The actual pairs (covering sieve, cartesian section). Source: Stacks Project,
Tag 02ZN, final descent-data construction
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
structure SieveCompletionObject
    (Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w})
    (J : GrothendieckTopology C) (T : C) where
  /-- The chosen covering sieve. -/
  sieve : Sieve T
  /-- Its covering condition. -/
  covering : sieve ∈ J T
  /-- The section on that sieve. -/
  section_ : SieveCartesianSection Q sieve

/-- A representative for a completion arrow on a common covering subsieve.
Source: Stacks Project, Tag 02ZN, less naive proof, morphism colimit
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
structure SieveCompletionArrowRep
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {J : GrothendieckTopology C} {T : C} (X Y : SieveCompletionObject Q J T) where
  /-- The common covering refinement. -/
  sieve : Sieve T
  /-- It covers. -/
  covering : sieve ∈ J T
  /-- Inclusion in the source sieve. -/
  le_left : sieve ≤ X.sieve
  /-- Inclusion in the target sieve. -/
  le_right : sieve ≤ Y.sieve
  /-- A compatible family of fibre isomorphisms. -/
  iso : restrictSieveSection le_left X.section_ ≅ restrictSieveSection le_right Y.section_

/-- Equality after a common covering refinement. Source: Stacks Project, Tag 02ZN,
less naive proof, filtered morphism colimit
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def SieveCompletionArrowRep.EventuallyEq
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {J : GrothendieckTopology C} {T : C} {X Y : SieveCompletionObject Q J T}
    (a b : SieveCompletionArrowRep X Y) : Prop :=
  ∃ (K : Sieve T) (_ : K ∈ J T) (ha : K ≤ a.sieve) (hb : K ≤ b.sieve),
    ∀ f : K.arrows.category,
      HEq (a.iso.hom.toNatTrans.app ((sieveBasedInclusion ha).obj f))
        (b.iso.hom.toNatTrans.app ((sieveBasedInclusion hb).obj f))

/-- The colimit of section isomorphisms under covering refinement, explicitly as a
quotient of representatives. Source: Stacks Project, Tag 02ZN, less naive proof
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def SieveCompletionHom
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {J : GrothendieckTopology C} {T : C} (X Y : SieveCompletionObject Q J T) : Type w :=
  Quot (@SieveCompletionArrowRep.EventuallyEq _ _ Q J T X Y)


/-- Pullback of a completion object, with the prescribed inverse-image sieve and section.
Source: Stacks Project, Tag 02ZN
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def SieveCompletionObject.pullback
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {J : GrothendieckTopology C} {T V : C} (X : SieveCompletionObject Q J T)
    (f : V ⟶ T) : SieveCompletionObject Q J V where
  sieve := X.sieve.pullback f
  covering := J.pullback_stable f X.covering
  section_ := pullbackSieveSection f X.section_

/-- Identity representative on the object's own covering sieve. Source: Stacks Project,
Tag 02ZN (blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def SieveCompletionArrowRep.id
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {J : GrothendieckTopology C} {T : C} (X : SieveCompletionObject Q J T) :
    SieveCompletionArrowRep X X where
  sieve := X.sieve
  covering := X.covering
  le_left := le_rfl
  le_right := le_rfl
  iso := Iso.refl _

/-- Composition on the intersection of the representatives' covering sieves.
Source: Stacks Project, Tag 02ZN, morphism colimit
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def SieveCompletionArrowRep.comp
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {J : GrothendieckTopology C} {T : C} {X Y Z : SieveCompletionObject Q J T}
    (a : SieveCompletionArrowRep X Y) (b : SieveCompletionArrowRep Y Z) :
    SieveCompletionArrowRep X Z where
  sieve := a.sieve ⊓ b.sieve
  covering := J.intersection_covering a.covering b.covering
  le_left := le_trans inf_le_left a.le_left
  le_right := le_trans inf_le_right b.le_right
  iso := (restrictSieveSectionIso inf_le_left a.iso).trans
    (restrictSieveSectionIso inf_le_right b.iso)

/-- Inverse represented by the inverse compatible family on the same sieve.
Source: Stacks Project, Tag 02ZN
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def SieveCompletionArrowRep.inv
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {J : GrothendieckTopology C} {T : C} {X Y : SieveCompletionObject Q J T}
    (a : SieveCompletionArrowRep X Y) : SieveCompletionArrowRep Y X where
  sieve := a.sieve
  covering := a.covering
  le_left := a.le_right
  le_right := a.le_left
  iso := a.iso.symm

/-- Pullback of a representative, componentwise on the inverse-image sieve.
Source: Stacks Project, Tag 02ZN
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def SieveCompletionArrowRep.pullback
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {J : GrothendieckTopology C} {T V : C} {X Y : SieveCompletionObject Q J T}
    (a : SieveCompletionArrowRep X Y) (f : V ⟶ T) :
    SieveCompletionArrowRep (X.pullback f) (Y.pullback f) where
  sieve := a.sieve.pullback f
  covering := J.pullback_stable f a.covering
  le_left := fun _ _ hg ↦ a.le_left _ hg
  le_right := fun _ _ hg ↦ a.le_right _ hg
  iso :=
    { hom := BasedCategory.whiskerLeft (sieveBasedPullback f a.sieve) a.iso.hom
      inv := BasedCategory.whiskerLeft (sieveBasedPullback f a.sieve) a.iso.inv
      hom_inv_id := by
        apply BasedNatTrans.ext
        ext g
        exact congrArg (fun b ↦ b.toNatTrans.app ((sieveBasedPullback f a.sieve).obj g))
          a.iso.hom_inv_id
      inv_hom_id := by
        apply BasedNatTrans.ext
        ext g
        exact congrArg (fun b ↦ b.toNatTrans.app ((sieveBasedPullback f a.sieve).obj g))
          a.iso.inv_hom_id }

/-- Value of a section in the literal fibre over the domain of its indexing arrow.
The transport uses the equality required in Mathlib's `BasedFunctor`.
Source: Stacks Project, Tag 02ZN
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def sieveSectionValue
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}} {T : C} {R : Sieve T}
    (x : SieveCartesianSection Q R) (f : R.arrows.category) :
    Q.obj (.mk (op f.obj.left)) :=
  Eq.mp (congrArg (fun V : C ↦ (Q.obj (.mk (op V)) : Type w)) (x.w_obj f))
    (x.obj f).fiber

/-- The prescribed transition arrow of a pullback section. Source: Stacks Project,
Tag 02ZN (blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def pullbackSectionTransition
    (Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}) {T : C}
    (u : Q.obj (.mk (op T))) {a b : Over T} (g : a ⟶ b) :
    (CoGrothendieck.mk a.left ((Q.map a.hom.op.toLoc).toFunctor.obj u)) ⟶
      (CoGrothendieck.mk b.left ((Q.map b.hom.op.toLoc).toFunctor.obj u)) where
  base := g.left
  fiber := (Q.mapComp' b.hom.op.toLoc g.left.op.toLoc a.hom.op.toLoc
    (by simp only [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w])).hom
      |>.toNatTrans.app u

/-- The canonical pullback section is characterized on both objects and arrows,
including the pseudofunctor's non-strict comparison maps. Source: Stacks Project,
Tag 02ZN (blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def IsPullbackSieveSection
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}} {T : C}
    (u : Q.obj (.mk (op T))) {R : Sieve T} (x : SieveCartesianSection Q R) : Prop :=
  (∀ a : R.arrows.category,
    x.obj a = CoGrothendieck.mk a.obj.left ((Q.map a.obj.hom.op.toLoc).toFunctor.obj u)) ∧
  (∀ (a b : R.arrows.category) (g : a ⟶ b),
    HEq (x.map g) (pullbackSectionTransition Q u g.hom))

/-- The total functor induced by a pullback-compatible functor of fibred categories.
Source: Stacks Project, Tag 02ZN
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def groupoidBasedMap
    {Q A : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}} (e : StrongTrans Q A) :
    BasedFunctor (groupoidBasedCategory Q) (groupoidBasedCategory A) where
  toFunctor := CoGrothendieck.map e
  w := CoGrothendieck.map_comp_forget e


/-- A maximal-sieve section as an object of the completion. Source: Stacks Project,
Tag 02ZN (blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def maximalSieveCompletionObject
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    (J : GrothendieckTopology C) {T : C} (x : SieveCartesianSection Q (⊤ : Sieve T)) :
    SieveCompletionObject Q J T where
  sieve := ⊤
  covering := J.top_mem T
  section_ := x

/-- The arrow from a composite sieve member to its first factor.
Source: Stacks Project, Tag 02ZN
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def sieveMemberTransition {T : C} {R : Sieve T} (f : R.arrows.category)
    (g : (R.pullback f.obj.hom).arrows.category) :
    (sieveBasedPullback f.obj.hom R).obj g ⟶ f :=
  ObjectProperty.homMk (Over.homMk g.obj.hom)

/-- A local comparison as an arrow representative on the full inverse-image sieve.
Source: Stacks Project, Tag 02ZN, local description of descent objects
(blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def localSieveCompletionArrowRep
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {J : GrothendieckTopology C} {T V : C} (X : SieveCompletionObject Q J T)
    (f : V ⟶ T) (s : SieveCartesianSection Q (⊤ : Sieve V))
    (a : restrictSieveSection (le_top : X.sieve.pullback f ≤ ⊤) s ≅
      pullbackSieveSection f X.section_) :
    SieveCompletionArrowRep (maximalSieveCompletionObject J s) (X.pullback f) where
  sieve := X.sieve.pullback f
  covering := J.pullback_stable f X.covering
  le_left := le_top
  le_right := le_rfl
  iso := a

/-- The class of a local arrow in the refinement colimit. Source: Stacks Project,
Tag 02ZN (blueprint: lem-sfb-prestack-sieve-descent-completion). -/
def SieveCompletionArrowRep.toQuot
    {Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}
    {J : GrothendieckTopology C} {T : C} {X Y : SieveCompletionObject Q J T}
    (a : SieveCompletionArrowRep X Y) : SieveCompletionHom X Y :=
  Quot.mk _ a


/-- All the specified formulas for the covering-sieve completion, with their category,
pullback, unit and local-comparison laws. This is construction data, not an additional
hypothesis in the existence theorem below.

Source: Stacks Project, Tag 02ZN, final construction in both proofs, checks (1)--(8)
(blueprint: lem-sfb-prestack-sieve-descent-completion).

`obj` is a bijection on the actual pairs, not an equivalence on isomorphism classes.
`hom` identifies the actual refinement quotient with every Hom set. `hom_eq` explicitly
says that equality in the quotient is precisely equality on a common covering refinement.
The last two fields specify the local comparison by the original section transitions,
and realize it as a natural isomorphism of sections, including all restriction compatibilities.
-/
structure SieveDescentCompletion
    (Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}) (J : GrothendieckTopology C) where
  /-- The resulting fibred category with coherent pullbacks. -/
  stack : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}
  /-- Its fibres are groupoids. -/
  groupoid : ∀ T : C, IsGroupoid (stack.obj (.mk (op T)))
  /-- Morphism descent and effective object descent, for all covering sieves. -/
  isStack : stack.IsStack J
  /-- The pullback-compatible embedding. -/
  unit : StrongTrans Q stack
  /-- Full faithfulness on every fibre. -/
  fullyFaithful : ∀ T : C, (unit.app (.mk (op T))).toFunctor.FullyFaithful
  /-- A literal enumeration by covering-sieve sections. -/
  obj : ∀ T : C, SieveCompletionObject Q J T → stack.obj (.mk (op T))
  /-- No extra objects and no identifications of different pairs. -/
  obj_bijective : ∀ T : C, Function.Bijective (obj T)
  /-- The prescribed colimit Hom sets. -/
  hom : ∀ (T : C) (X Y : SieveCompletionObject Q J T),
    SieveCompletionHom X Y ≃ (obj T X ⟶ obj T Y)
  /-- Equality is equality on a common covering subsieve. -/
  hom_eq : ∀ (T : C) (X Y : SieveCompletionObject Q J T)
    (a b : SieveCompletionArrowRep X Y),
    hom T X Y a.toQuot = hom T X Y b.toQuot ↔ a.EventuallyEq b
  /-- Identity is the identity section family. -/
  hom_id : ∀ (T : C) (X : SieveCompletionObject Q J T),
    hom T X X (SieveCompletionArrowRep.id X).toQuot = 𝟙 (obj T X)
  /-- Composition on common covering refinement. -/
  hom_comp : ∀ (T : C) (X Y Z : SieveCompletionObject Q J T)
    (a : SieveCompletionArrowRep X Y) (b : SieveCompletionArrowRep Y Z),
    hom T X Z (a.comp b).toQuot = hom T X Y a.toQuot ≫ hom T Y Z b.toQuot
  /-- Inverses are componentwise inverses. -/
  hom_inv : ∀ (T : C) (X Y : SieveCompletionObject Q J T)
    (a : SieveCompletionArrowRep X Y),
    hom T X Y a.toQuot ≫ hom T Y X a.inv.toQuot = 𝟙 (obj T X)
  /-- Pullback restricts to the inverse-image sieve on objects. -/
  pullback_obj : ∀ (T V : C) (f : V ⟶ T) (X : SieveCompletionObject Q J T),
    obj V (X.pullback f) = (stack.map f.op.toLoc).toFunctor.obj (obj T X)
  /-- Pullback restricts the representing family of arrows. -/
  pullback_hom : ∀ (T V : C) (f : V ⟶ T) (X Y : SieveCompletionObject Q J T)
    (a : SieveCompletionArrowRep X Y),
    (stack.map f.op.toLoc).toFunctor.map (hom T X Y a.toQuot) =
      eqToHom (pullback_obj T V f X).symm ≫
        hom V (X.pullback f) (Y.pullback f) (a.pullback f).toQuot ≫
          eqToHom (pullback_obj T V f Y)
  /-- Maximal-sieve pullback sections in the original fibred groupoid. -/
  unitSection : ∀ (T : C) (_u : Q.obj (.mk (op T))),
    SieveCartesianSection Q (⊤ : Sieve T)
  /-- Both objects and transitions of these sections are the prescribed pullbacks. -/
  unitSection_formula : ∀ (T : C) (u : Q.obj (.mk (op T))),
    IsPullbackSieveSection u (unitSection T u)
  /-- The unit sends an object to exactly its maximal-sieve section. -/
  unit_obj : ∀ (T : C) (u : Q.obj (.mk (op T))),
    obj T (maximalSieveCompletionObject J (unitSection T u)) =
      (unit.app (.mk (op T))).toFunctor.obj u
  /-- The unit sends an arrow to its compatible family of pullbacks. -/
  unit_hom : ∀ (T : C) (u v : Q.obj (.mk (op T))) (p : u ⟶ v)
    (a : SieveCompletionArrowRep
      (maximalSieveCompletionObject J (unitSection T u))
      (maximalSieveCompletionObject J (unitSection T v))),
    (∀ g : a.sieve.arrows.category,
      HEq (a.iso.hom.toNatTrans.app g)
        ((CoGrothendieck.ι Q g.obj.left).map ((Q.map g.obj.hom.op.toLoc).toFunctor.map p))) →
    (unit.app (.mk (op T))).toFunctor.map p =
      eqToHom (unit_obj T u).symm ≫
        hom T (maximalSieveCompletionObject J (unitSection T u))
          (maximalSieveCompletionObject J (unitSection T v)) a.toQuot ≫
            eqToHom (unit_obj T v)
  /-- Canonical pullback sections in the completed fibred groupoid. -/
  stackSection : ∀ (T : C) (_u : stack.obj (.mk (op T))),
    SieveCartesianSection stack (⊤ : Sieve T)
  /-- They use the completed pseudofunctor's actual comparison isomorphisms. -/
  stackSection_formula : ∀ (T : C) (u : stack.obj (.mk (op T))),
    IsPullbackSieveSection u (stackSection T u)
  /-- The comparison from the section value at a sieve member to the restricted object,
  first written in the original fibred groupoid. -/
  localSectionIso : ∀ (T : C) (X : SieveCompletionObject Q J T)
    (f : X.sieve.arrows.category),
    restrictSieveSection (le_top : X.sieve.pullback f.obj.hom ≤ ⊤)
      (unitSection f.obj.left (sieveSectionValue X.section_ f)) ≅
        pullbackSieveSection f.obj.hom X.section_
  /-- Its components are the original section's transitions: the comparison followed
  by the transition to f equals the canonical cartesian lift. -/
  localSectionIso_formula : ∀ (T : C) (X : SieveCompletionObject Q J T)
    (f : X.sieve.arrows.category) (g : (X.sieve.pullback f.obj.hom).arrows.category),
    HEq ((localSectionIso T X f).hom.toNatTrans.app g ≫
      X.section_.map (sieveMemberTransition f g))
        (CoGrothendieck.cartesianLift (sieveSectionValue X.section_ f) g.obj.hom)
  /-- The local isomorphisms are compatible with every restriction and transition. -/
  localIso : ∀ (T : C) (X : SieveCompletionObject Q J T),
    BasedFunctor.comp X.section_ (groupoidBasedMap unit) ≅
      restrictSieveSection (le_top : X.sieve ≤ ⊤) (stackSection T (obj T X))
  /-- The local isomorphism is the canonical arrow represented by those very section
  transitions, rather than an arbitrary choice of fibrewise isomorphisms. -/
  localIso_formula : ∀ (T : C) (X : SieveCompletionObject Q J T)
    (f : X.sieve.arrows.category),
    HEq ((localIso T X).hom.toNatTrans.app f)
      ((CoGrothendieck.ι stack f.obj.left).map
        (hom f.obj.left
          (maximalSieveCompletionObject J
            (unitSection f.obj.left (sieveSectionValue X.section_ f)))
          (X.pullback f.obj.hom)
          (localSieveCompletionArrowRep X f.obj.hom
            (unitSection f.obj.left (sieveSectionValue X.section_ f))
            (localSectionIso T X f)).toQuot))

/-- Covering-sieve descent data complete a prestack to a stack, with the explicitly
prescribed objects, refinement-colimit arrows, pullbacks and fully faithful unit.

Source: Stacks Project, stacks.tex, Tag 02ZN (lemma-stackify), final construction
in both proofs, including naive checks (1)--(8)
(blueprint: lem-sfb-prestack-sieve-descent-completion).

Proof:
1. The topology axioms give upward closure, covering intersections and covering
composite sieves. All section families and the refinement quotient are sets in w.
2. Apply lem-sfb-cartesian-section-covering-restriction to every covering common
subsieve of R intersect S. Every section isomorphism extends uniquely to R intersect S.
Hence the displayed quotient is the filtered colimit, with equality checked on a
common covering refinement.
3. Compose representatives on intersections. Their inverses and identities are
componentwise. Well-definedness and all category laws follow after one common
refinement. Pullback is precomposition on inverse-image sieve categories and descends
to this quotient. Its coherent comparisons are inherited from the original sections.
The CoGrothendieck construction gives the fibred groupoid, with cartesian lifts
represented by fibre identities.
4. Send u to its canonical pullback section on the maximal sieve. Evaluation at the
identity identifies section arrows between these sections with arrows between u and v,
so the unit is fibrewise fully faithful. For f in R, the section transitions identify
the pullback of (R,x) with the image of x_f. Their cartesian-lift triangles give exactly
localSectionIso_formula, and their coherence gives the based natural isomorphism localIso.
5. To glue arrows A to B on a covering R, intersect R with the two representative
sieves. The local comparisons and full faithfulness of the unit identify the given
arrows there with a compatible family of arrows in Q. That family represents the glued
arrow. Equality can be checked on any further covering refinement, giving uniqueness
and proving the prestack axiom on all slices.
6. For object descent data A on R, write A_f=(S_f,x^f). The sieve H of composites fg
with f in R and g in S_f covers. Choose one such factorization for each actual t in H
and set z_t=x^{f_t}_{g_t}. The local comparisons give b_t:e(z_t) isomorphic to A_t.
Lift b_{th}^{-1} composed with the transition of A and the pullback of b_t through the
fully faithful unit. Faithfulness gives the cocycle, so z is a cartesian section of Q.
7. The object (H,z) realizes A on H. The transition equations make its comparisons
compatible. Apply lem-sfb-cartesian-section-covering-restriction to the prestack just
proved, extending those comparisons from H to R. Thus object descent is effective.
8. If the empty sieve covers, its unique section is a completion object; empty common
refinement gives the unique arrow between any two objects. Empty descent is therefore
effective. No construction chose a member of an empty covering sieve: factorization
choices in step 6 are indexed only by actual members of H. -/
theorem exists_prestack_sieve_descent_completion
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w})
    (hQ : ∀ T : C, IsGroupoid (Q.obj (.mk (op T)))) [Q.IsPrestack J] :
    Nonempty (SieveDescentCompletion Q J) := by
  sorry

end CategoryTheory.Pseudofunctor
