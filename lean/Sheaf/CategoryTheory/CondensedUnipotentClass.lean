/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Sheaf.CategoryTheory.CondensedScalarTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Positive unipotent condensed character class

Source: main-20261015 direct-images proof (sk-thm-sf-ctf-stability-direct-images.proof.md),
paragraph (3), agent-formulated formal restriction and cup-product infrastructure;
exact reference wanted
(blueprint: def-sfb-condensed-unipotent-class).

## Main definitions

* `Character`, `Character.restrict`, `Character.coefficients`: additive condensed maps
  a : J → (R,+), with precomposition and coefficient change.
* `unipotentAction`, `extension`, `extensionSequence`: the action j(x,y) = (x + a(j)y, y) on
  R ⊞ R and its short exact sequence with trivial endpoints.
* `classShifted`, `characterClass`: the connecting class [a] : R[-1] → C_R(J), with the
  positive normalization j(0,1) - (0,1) = (a(j),0) (`extensionPositive`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction (inflate trivial)
open CategoryTheory.CondensedBar
namespace CategoryTheory.CondensedDerivedRestriction
variable {A A' : CondensedBar.Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The biproducts are the finite biproducts of the existing abelian module category.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
instance moduleBiproducts : HasFiniteBiproducts (Modules A) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- An additive morphism from the condensed group underline G to the additive group of A.
Naturality is imposed for every profinite base change, not only on global points.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
structure Character (A : CondensedBar.Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] where
  app : ∀ S : Profinite.{u}, C(S, G) → sectionRing A S
  one : ∀ S, app S 1 = 0
  mul : ∀ S g h, app S (g * h) = app S g + app S h
  naturality : ∀ (S T : Profinite.{u}) (f : T ⟶ S) (g : C(S, G)),
    A.X.obj.map f.op (app S g) = app T (g.comp f.hom.hom)

/-- Precomposition gives the unique additive character with these sectionwise values.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class).
Proof: a continuous homomorphism preserves identity and products pointwise, and
composition commutes with every profinite base change. Substitute these identities
into the three character laws. The values determine the character record uniquely. -/
theorem restrictCharacterExist (a : Character A G) (v : H →ₜ* G) :
    ∃! b : Character A H, ∀ S g, b.app S g = a.app S (v.toContinuousMap.comp g) := by
  sorry

/-- Actual precomposition of the condensed additive character on every test object.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
def Character.restrict (a : Character A G) (v : H →ₜ* G) : Character A H :=
  Classical.choose (restrictCharacterExist a v)

/-- The two projections of the actual biproduct, evaluated on a generalized section.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
def first (S : Profinite.{u})
    (z : sections A (Mod.regular A.X ⊞ Mod.regular A.X) S) : sectionRing A S :=
  ((biprod.fst : Mod.regular A.X ⊞ Mod.regular A.X ⟶ Mod.regular A.X).hom.hom.app (op S)) z

/-- Second coordinate of the actual biproduct, evaluated on a generalized section.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
def second (S : Profinite.{u})
    (z : sections A (Mod.regular A.X ⊞ Mod.regular A.X) S) : sectionRing A S :=
  ((biprod.snd : Mod.regular A.X ⊞ Mod.regular A.X ⟶ Mod.regular A.X).hom.hom.app (op S)) z

/-- The unipotent action is specified on the fixed, actual biproduct module. Both
coordinate equations determine every action operator, hence all of this datum uniquely.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
structure UnipotentAction (a : Character A G) where
  act : ∀ S : Profinite.{u}, C(S, G) →*
    Module.End (sectionRing A S) (sections A (Mod.regular A.X ⊞ Mod.regular A.X) S)
  naturality : ∀ (S T : Profinite.{u}) (f : T ⟶ S) (g : C(S, G)) (z),
    ((Mod.regular A.X ⊞ Mod.regular A.X).X.obj.map f.op) (act S g z) =
      act T (g.comp f.hom.hom) (((Mod.regular A.X ⊞ Mod.regular A.X).X.obj.map f.op) z)
  first_action : ∀ S g z, first (A := A) S (act S g z) =
    first (A := A) S z + a.app S g * second (A := A) S z
  second_action : ∀ S g z, second (A := A) S (act S g z) = second (A := A) S z

/-- There is a unique unipotent action with the displayed two coordinates.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class).
Proof: the sectionwise biproduct is a product. Conjugate the linear matrix with entries
1,a(g),0,1 by its coordinate equivalence. The character multiplication law proves the
action law, its naturality proves restriction compatibility. The two projections are
jointly injective, so any action satisfying these equations is this one. -/
theorem unipotentActionExist (a : Character A G) : ∃! d : UnipotentAction a, True := by
  sorry

/-- The unique normalized action, on the actual R direct-sum R module.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
def unipotentAction (a : Character A G) : UnipotentAction a :=
  Classical.choose (unipotentActionExist a)

/-- The specified unipotent equivariant module, constructed from its unique action.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
def extension (a : Character A G) : Equivariant A G where
  module := Mod.regular A.X ⊞ Mod.regular A.X
  act := (unipotentAction a).act
  naturality := (unipotentAction a).naturality

/-- Inclusion in the first coordinate and projection to the second are equivariant.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class).
Proof: substitute (x,0) into the first action equation and read the second equation for
an arbitrary pair. These equations say exactly that both underlying maps are equivariant. -/
theorem extensionMaps (a : Character A G) :
    Profinite.CondensedAction.Equivariant
      ((trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X)) (extension a) biprod.inl ∧
    Profinite.CondensedAction.Equivariant (extension a)
      ((trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X)) biprod.snd := by
  sorry

/-- The first-coordinate inclusion with its actual action-category Hom type.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
def extensionInclusion (a : Character A G) : regularTrivial A G ⟶ extension a :=
  ⟨biprod.inl, (extensionMaps a).1⟩

/-- The second-coordinate projection with its actual action-category Hom type.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
def extensionProjection (a : Character A G) : extension a ⟶ regularTrivial A G :=
  ⟨biprod.snd, (extensionMaps a).2⟩

/-- The exact equivariant extension with its specified endpoint maps.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class).
Proof: the underlying biproduct inclusion followed by the second projection is zero.
This equality is the equivariant equality because forgetting the action is faithful. -/
theorem extensionZero (a : Character A G) :
    extensionInclusion a ≫ extensionProjection a = 0 := by
  sorry

/-- The short complex is the unipotent extension with trivial endpoints.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
def extensionSequence (a : Character A G) : ShortComplex (Equivariant A G) :=
  ShortComplex.mk (extensionInclusion a) (extensionProjection a) (extensionZero a)

/-- The unipotent sequence is short exact in the action category.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class).
Proof: forgetting the action gives the standard split biproduct sequence. Its inclusion
is monic, its projection is epic and the first coordinate is the kernel of the second.
Exactness is detected by forgetting; the faithful exact forgetful functor detects these
monomorphisms and epimorphisms as well. -/
theorem extensionExact (a : Character A G) : (extensionSequence a).ShortExact := by
  sorry

/-- The specified positive section lift of 1 into the second biproduct coordinate.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
def extensionOneSection (a : Character A G) (S : Profinite.{u}) :
    sections A (extension a).module S :=
  ((biprod.inr : Mod.regular A.X ⟶ Mod.regular A.X ⊞ Mod.regular A.X).hom.hom.app
    (op S)) (1 : sectionRing A S)

/-- The positive inhomogeneous cocycle of the chosen section t(1)=(0,1) is exactly a.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class).
Proof: apply the two coordinate equations to (0,1). Their differences are a(g) and zero;
the product projections are jointly injective, yielding (a(g),0), with positive sign. -/
theorem extensionPositive (a : Character A G) (S : Profinite.{u}) (g : C(S, G)) :
    @Sub.sub (sections A (extension a).module S) inferInstance
      ((extension a).act S g (extensionOneSection a S)) (extensionOneSection a S) =
    (((biprod.inl : Mod.regular A.X ⟶ Mod.regular A.X ⊞ Mod.regular A.X).hom.hom.app
      (op S)) (a.app S g)) := by
  sorry

/-- The connecting class applied to the invariant unit, before shifting down by one.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
def classShifted (a : Character A G) :
    (DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X) ⟶
      (cohomology A G)⟦(1 : ℤ)⟧ :=
  (baseUnitIso A).inv ≫ cupUnit (A := A) (G := G) ≫
    (derived A G).map (extensionExact a).singleδ ≫
      ((derived A G).commShiftIso (1 : ℤ)).hom.app (coefficient A G)

/-- The degree-one class has the required source R[-1] and the positive connecting sign.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
def characterClass (a : Character A G) :
    ((DerivedCategory.singleFunctor (Modules A) 0).obj (Mod.regular A.X))⟦(-1 : ℤ)⟧ ⟶
      cohomology A G :=
  (classShifted a)⟦(-1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId (DerivedCategory.{u + 1} (Modules A))
      (1 : ℤ) (-1 : ℤ) (add_neg_cancel 1)).hom.app (cohomology A G)

/-- Composing a character with a condensed ring morphism gives the unique character
with the pointwise composed values.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class).
Proof: the condensed ring map is additive on every test object and natural for every
base change. Compose its section maps with a. The character laws follow by additivity,
and equality on all sections is equality of these character records. -/
theorem coefficientCharacterExist (φ : A ⟶ A') (a : Character A G) :
    ∃! b : Character A' G, ∀ S g,
      b.app S g = (φ.hom.hom.hom.app (op S)) (a.app S g) := by
  sorry

/-- Actual composition of a condensed additive character with the coefficient ring map.
Source: paragraph (3) (blueprint: def-sfb-condensed-unipotent-class). -/
def Character.coefficients (a : Character A G) (φ : A ⟶ A') : Character A' G :=
  Classical.choose (coefficientCharacterExist φ a)

end CategoryTheory.CondensedDerivedRestriction
