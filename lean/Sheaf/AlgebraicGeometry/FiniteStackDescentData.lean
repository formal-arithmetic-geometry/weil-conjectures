module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Relative sections and finite-scheme descent data on a stack atlas

Source: Stacks Project, Descent, Tags 0245 and 02LA; Sheaves on Algebraic Stacks,
Tag 06WV(1) (blueprint: def-sfb-finite-stack-descent-data).

A representable map to a fibred groupoid is encoded by its presheaf of relative
sections on the total category. Its source is the opposite category of elements.
A finite scheme on an atlas is encoded by its functor of sections. Descent is
encoded by extending that functor to the category with the same chart objects and
all arrows between their images in the stack. Vertical isomorphisms in this
category are the scheme tests of the overlap; functoriality is precisely the
cocycle, and natural transformations are all compatible maps, including maps
that are not invertible. This description never assumes that the overlap is a scheme.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry Opposite

namespace CategoryTheory

/-- The sections of `Z → T` on every scheme mapping to `T`, retaining the map to `T`.
Source: Stacks 0245, functor-of-points formulation
(blueprint: def-sfb-finite-stack-descent-data). -/
def finiteSchemeSections {S : Scheme.{u}} {T Z : Over S} (p : Z ⟶ T) :
    (discreteModuli (yoneda.obj T)).objᵒᵖ ⥤ Type u where
  obj x := {z : x.unop.left ⟶ Z // z ≫ p = yoneda.preimage x.unop.hom}
  map f := TypeCat.ofHom (fun z ↦ ⟨f.unop.left ≫ z.val, by
    rw [Category.assoc, z.property]
    apply yoneda.map_injective
    simp⟩)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact Category.id_comp _
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- A presheaf on the total category of `h_T` is a finite scheme over `T` when it
is naturally represented by sections of an actual finite scheme morphism.
Source: Stacks 0245 and 02LA (blueprint: def-sfb-finite-stack-descent-data). -/
def IsFiniteSchemeSections {S : Scheme.{u}} (T : Over S)
    (P : (discreteModuli (yoneda.obj T)).objᵒᵖ ⥤ Type u) : Prop :=
  ∃ (Z : Over S) (p : Z ⟶ T), IsFinite p.left ∧ Nonempty (P ≅ finiteSchemeSections p)

/-- The relative section presheaves whose restriction to every scheme test is
represented by a finite scheme over that test. No atlas or representative is chosen.
Source: Stacks, representable finite morphism convention and 02LA
(blueprint: def-sfb-finite-stack-descent-data). -/
def IsFiniteStackSections {S : Scheme.{u}} (X : BasedCategory.{v, w} (Over S))
    (P : X.objᵒᵖ ⥤ Type u) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) X),
    IsFiniteSchemeSections T (t.toFunctor.op ⋙ P)

/-- The category of finite representable maps, in the equivalent relative-section
encoding. Morphisms are all natural transformations, not merely isomorphisms.
Source: Stacks 0245 and 06WV(1) (blueprint: def-sfb-finite-stack-descent-data). -/
abbrev FiniteStackSections {S : Scheme.{u}} (X : BasedCategory.{v, w} (Over S)) :=
  ObjectProperty.FullSubcategory (IsFiniteStackSections X)

/-- The chart category has objects maps into the atlas and morphisms the actual
arrows between their images in `X`. Its vertical arrows are all overlap points.
Source: Stacks 003R and 0245 (blueprint: def-sfb-finite-stack-descent-data). -/
abbrev FiniteAtlasCategory {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
    {T : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) X) :=
  InducedCategory X.obj a.obj

/-- The canonical inclusion of chart arrows into all stack arrows between chart
objects. On a base arrow this is precisely its image under the given atlas map.
Source: Stacks 003R and 0245 (blueprint: def-sfb-finite-stack-descent-data). -/
def finiteAtlasInclusion {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
    {T : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) X) :
    (discreteModuli (yoneda.obj T)).obj ⥤ FiniteAtlasCategory a where
  obj x := x
  map f := InducedCategory.homMk (a.map f)
  map_id x := InducedCategory.hom_ext (a.toFunctor.map_id x)
  map_comp f g := InducedCategory.hom_ext (a.toFunctor.map_comp f g)

/-- Finite schemes with descent datum: a presheaf on chart objects and stack arrows,
whose restriction to ordinary chart arrows is represented by a finite scheme.
Functoriality imposes both naturality under test-scheme pullback and the overlap
cocycle. All compatible morphisms are the natural transformations of these presheaves.
Source: Stacks 0245 and 06WV(1) (blueprint: def-sfb-finite-stack-descent-data). -/
abbrev FiniteAtlasDescent {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
    {T : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) X) :=
  ObjectProperty.FullSubcategory (fun P : (FiniteAtlasCategory a)ᵒᵖ ⥤ Type u ↦
    IsFiniteSchemeSections T ((finiteAtlasInclusion a).op ⋙ P))

/-- Pullback to the atlas with its canonical overlap transport is restriction
along the functor sending each chart object to its given image in the stack.
Source: Stacks 0245 and 06WV(1) (blueprint: def-sfb-finite-stack-descent-data). -/
def finiteStackRestriction {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
    {T : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj T)) X) :
    FiniteStackSections X ⥤ FiniteAtlasDescent a where
  obj P := ⟨(inducedFunctor a.obj).op ⋙ P.obj, P.property T a⟩
  map f := ObjectProperty.homMk (Functor.whiskerLeft (inducedFunctor a.obj).op f.hom)

/-- The explicit source of a relative-section presheaf: objects are pairs `(x,s)`,
and arrows are stack arrows taking the target section to the source section.
Source: Stacks 003T; explicit section-groupoid construction in the proof of
finite-scheme stack descent (blueprint: def-sfb-finite-stack-descent-data). -/
def stackSectionTotal {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
    (P : X.objᵒᵖ ⥤ Type u) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor ((CategoryOfElements.π P).leftOp ⋙ X.p)

/-- The actual map from the section groupoid to the original stack.
Source: Stacks 003T (blueprint: def-sfb-finite-stack-descent-data). -/
def stackSectionProjection {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
    (P : X.objᵒᵖ ⥤ Type u) : BasedFunctor (stackSectionTotal P) X where
  toFunctor := (CategoryOfElements.π P).leftOp
  w := rfl

/-- A map of relative-section presheaves acts on pairs by `(x,s) ↦ (x,η(s))`.
This is the canonical map of represented groupoids, retaining noninvertible maps.
Source: Stacks 003T and 0245 (blueprint: def-sfb-finite-stack-descent-data). -/
def stackSectionMap {S : Scheme.{u}} {X : BasedCategory.{v, w} (Over S)}
    {P Q : X.objᵒᵖ ⥤ Type u} (η : P ⟶ Q) :
    BasedFunctor (stackSectionTotal P) (stackSectionTotal Q) where
  toFunctor := (CategoryOfElements.map η).op
  w := rfl

end CategoryTheory
