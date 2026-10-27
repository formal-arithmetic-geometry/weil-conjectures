module

public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.InducedCategory

/-! # Schlessinger (S1) and categories of descent to test subalgebras

Source: Stacks Project, Formal Deformation Theory, condition (S1) and the
paragraph defining S_x immediately before Tag 06T1
(blueprint: def-sfb-artin-schlessinger-descent-category).

These are the shared definitions used by minimal descent and descended versal bases.
The category S_x retains the literal test subalgebra and every commuting triangle.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

variable {R k : Type u} [CommRing R] [Field k] [Algebra R k]

/-- Schlessinger (S1), retaining each specified comparison isomorphism in the
categorical pullback. Source: Stacks, Tag 06T1 and condition (S1)
(blueprint: def-sfb-artin-schlessinger-descent-category). -/
def IsSchlessingerOne [IsNoetherianRing R] [Algebra.FiniteType R k]
    (F : CofibredGroupoids.{u, v, w} R k) : Prop :=
  ∀ (A₁ A₂ A : TestCategory R k) (f₁ : A₁ ⟶ A) (f₂ : A₂ ⟶ A)
    (hs : Function.Surjective (map f₂)),
    (comparison F (fibreProductFst f₁ f₂ hs) (fibreProductSnd f₁ f₂ hs) f₁ f₂
      (fibreProduct_condition f₁ f₂ hs)).EssSurj

/-- A literal test subalgebra, marked by restricting the ambient residue map.
Source: Stacks, paragraph before Tag 06T1
(blueprint: def-sfb-artin-schlessinger-descent-category). -/
def subalgebraTest (A : TestCategory R k) (S : Subalgebra R (ring A))
    (h : IsTestAlgebra R k (A := CommAlgCat.of R S) ((residue A).comp S.val)) :
    TestCategory R k :=
  ⟨Over.mk (CommAlgCat.ofHom ((residue A).comp S.val)), h⟩

/-- The inclusion of a literal test subalgebra. Source: Stacks, before Tag 06T1
(blueprint: def-sfb-artin-schlessinger-descent-category). -/
def subalgebraInclusion (A : TestCategory R k) (S : Subalgebra R (ring A))
    (h : IsTestAlgebra R k (A := CommAlgCat.of R S) ((residue A).comp S.val)) :
    subalgebraTest A S h ⟶ A :=
  ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom S.val) rfl)

/-- The object over a test ring in the total cofibred category. Source: Stacks,
Tags 06GJ and 06T1 (blueprint: def-sfb-artin-schlessinger-descent-category). -/
def totalObject (F : CofibredGroupoids.{u, v, w} R k) {A : TestCategory R k}
    (x : fibre F A) : Pseudofunctor.Grothendieck F.transport := ⟨A, x⟩

/-- Data of an object of S_x: a test subalgebra and an arrow to x over its inclusion.
All fibre arrows are invertible because F has groupoid fibres.
Source: Stacks, paragraph before Tag 06T1
(blueprint: def-sfb-artin-schlessinger-descent-category). -/
structure DescentData (F : CofibredGroupoids.{u, v, w} R k)
    {A : TestCategory R k} (x : fibre F A) where
  subring : Subalgebra R (ring A)
  valid : IsTestAlgebra R k (A := CommAlgCat.of R subring)
    ((residue A).comp subring.val)
  obj : fibre F (subalgebraTest A subring valid)
  arrow : (push F (subalgebraInclusion A subring valid)).obj obj ⟶ x

/-- The corresponding object of the over category of the total category.
Source: Stacks, paragraph before Tag 06T1
(blueprint: def-sfb-artin-schlessinger-descent-category). -/
def descentOver {F : CofibredGroupoids.{u, v, w} R k} {A : TestCategory R k}
    {x : fibre F A} (D : DescentData F x) : Over (totalObject F x) :=
  Over.mk (Y := totalObject F D.obj)
    { base := subalgebraInclusion A D.subring D.valid, fiber := D.arrow }

/-- S_x, with exactly the commuting triangles over x as arrows.
Source: Stacks, paragraph before Tag 06T1
(blueprint: def-sfb-artin-schlessinger-descent-category). -/
abbrev DescentCategory (F : CofibredGroupoids.{u, v, w} R k)
    {A : TestCategory R k} (x : fibre F A) :=
  InducedCategory (Over (totalObject F x)) (descentOver (F := F) (x := x))

/-- A minimal descent object has the same subring as every object mapping to it.
Source: Stacks, paragraph before Tag 06T1
(blueprint: def-sfb-artin-schlessinger-descent-category). -/
def IsMinimalDescent {F : CofibredGroupoids.{u, v, w} R k}
    {A : TestCategory R k} {x : fibre F A} (D : DescentCategory F x) : Prop :=
  ∀ E : DescentCategory F x, (E ⟶ D) → E.subring = D.subring

end AlgebraicGeometry.ArtinDeformation
