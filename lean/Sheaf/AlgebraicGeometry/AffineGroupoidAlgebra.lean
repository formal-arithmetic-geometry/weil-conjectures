module

public import Sheaf.AlgebraicGeometry.SchemeGroupoidLaws
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Ring.Subring.Basic

/-! # Commutative algebras with affine groupoid descent data

Source: Stacks Project, stacks-sheaves.tex, Tag 06WT, applied to algebra objects;
Alper, arXiv:1005.2398v3, Proposition 8.2.1, first two paragraphs
(blueprint: def-sfb-affine-groupoid-algebra).

Ring pushouts are tensor products (`CommRingCat.isPushout_tensorProduct`). The identity
and cocycle equations are expressed on points with values in every commutative ring
in the ambient universe. This avoids choosing associativity identifications for iterated
tensor products. Testing every such ring is faithful by Yoneda. The coordinate rings
are canonically lifted global sections, hence are canonically the original affine rings.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u q

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Lifted coordinate rings, with no restriction on the size of the algebra.
Source: Stacks Tag 06WT (blueprint: def-sfb-affine-groupoid-algebra). -/
def groupoidAlgebraCoordinates (X : Scheme.{u}) : CommRingCat.{max u q} :=
  CommRingCat.of (ULift.{q} (Scheme.Γ.obj (op X)))

/-- Pullback of regular functions, with canonical universe transport.
Source: Stacks Tag 06WT (blueprint: def-sfb-affine-groupoid-algebra). -/
def groupoidAlgebraCoordinateMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    groupoidAlgebraCoordinates.{u, q} Y ⟶ groupoidAlgebraCoordinates.{u, q} X :=
  CommRingCat.ofHom f.appTop.hom.ulift

/-- The relation on algebra-valued points induced by a forward transport `beta`.
The source point is the target point composed with beta; all maps preserve the
coordinate of the arrow. Source: Stacks Tag 06WT, inverse of its transport convention
(blueprint: def-sfb-affine-groupoid-algebra). -/
def groupoidAlgebraTransport {U R : Scheme.{u}} (s t : R ⟶ U)
    (A : Under (groupoidAlgebraCoordinates.{u, q} U))
    (beta : pushout A.hom (groupoidAlgebraCoordinateMap s) ≅
      pushout A.hom (groupoidAlgebraCoordinateMap t))
    (C : CommRingCat.{max u q}) (r : groupoidAlgebraCoordinates R ⟶ C)
    (x y : A.right ⟶ C) : Prop :=
  ∃ h : pushout A.hom (groupoidAlgebraCoordinateMap t) ⟶ C,
    pushout.inr A.hom (groupoidAlgebraCoordinateMap t) ≫ h = r ∧
    pushout.inl A.hom (groupoidAlgebraCoordinateMap t) ≫ h = y ∧
    pushout.inl A.hom (groupoidAlgebraCoordinateMap s) ≫ beta.hom ≫ h = x

/-- Arbitrary commutative algebras with identity and composition compatible descent.
`beta` is an isomorphism of R-algebras because it preserves the right pushout inclusion.
For composable arrows the first pullback projection is the later arrow.
Source: Stacks Tag 06WT; Alper Proposition 8.2.1
(blueprint: def-sfb-affine-groupoid-algebra). -/
structure AffineGroupoidAlgebra {U R : Scheme.{u}} (s t : R ⟶ U)
    (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (_hG : IsGroupoid s t e i c) where
  /-- The coordinate algebra; no finite generation or finite presentation is imposed. -/
  algebra : Under (groupoidAlgebraCoordinates.{u, q} U)
  /-- Forward transport from source to target. -/
  beta : pushout algebra.hom (groupoidAlgebraCoordinateMap s) ≅
    pushout algebra.hom (groupoidAlgebraCoordinateMap t)
  /-- The transport is linear over the arrow coordinate ring. -/
  scalar : pushout.inr algebra.hom (groupoidAlgebraCoordinateMap s) ≫ beta.hom =
    pushout.inr algebra.hom (groupoidAlgebraCoordinateMap t)
  /-- Identity arrows act as the identity after base change. -/
  unit : ∀ (C : CommRingCat.{max u q}) (x : algebra.right ⟶ C),
    groupoidAlgebraTransport s t algebra beta C
      (groupoidAlgebraCoordinateMap e ≫ algebra.hom ≫ x) x x
  /-- Successive transport is transport along composition, on every ring-valued point. -/
  cocycle : ∀ (C : CommRingCat.{max u q})
    (p : groupoidAlgebraCoordinates (pullback s t) ⟶ C) (x y z : algebra.right ⟶ C),
    groupoidAlgebraTransport s t algebra beta C
      (groupoidAlgebraCoordinateMap (pullback.snd s t) ≫ p) x y →
    groupoidAlgebraTransport s t algebra beta C
      (groupoidAlgebraCoordinateMap (pullback.fst s t) ≫ p) y z →
    groupoidAlgebraTransport s t algebra beta C (groupoidAlgebraCoordinateMap c ≫ p) x z

namespace AffineGroupoidAlgebra

variable {U R : Scheme.{u}} {s t : R ⟶ U} {e : U ⟶ R} {i : R ⟶ R}
  {c : pullback s t ⟶ R} {hG : IsGroupoid s t e i c}

/-- All algebra maps commuting with transport, tested faithfully on ring-valued points.
Source: Stacks Tag 06WT (blueprint: def-sfb-affine-groupoid-algebra). -/
def Hom (A B : AffineGroupoidAlgebra.{u, q} s t e i c hG) :=
  {f : A.algebra ⟶ B.algebra // ∀ (C : CommRingCat.{max u q})
    (r : groupoidAlgebraCoordinates R ⟶ C) (x y : B.algebra.right ⟶ C),
    groupoidAlgebraTransport s t B.algebra B.beta C r x y →
    groupoidAlgebraTransport s t A.algebra A.beta C r (f.right ≫ x) (f.right ≫ y)}

/-- Identity and composition are the underlying algebra maps.
Source: Stacks Tag 06WT (blueprint: def-sfb-affine-groupoid-algebra). -/
instance category : Category (AffineGroupoidAlgebra.{u, q} s t e i c hG) where
  Hom := Hom
  id A := ⟨𝟙 A.algebra, by intro C r x y h; simpa using h⟩
  comp f g := ⟨f.val ≫ g.val, by
    intro C r x y h
    simpa only [Under.comp_right, Category.assoc] using
      f.property C r (g.val.right ≫ x) (g.val.right ≫ y) (g.property C r x y h)⟩
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

/-- Forget only the descent datum, retaining the coordinate-algebra structure.
Source: Stacks Tag 06WT (blueprint: def-sfb-affine-groupoid-algebra). -/
def forget : AffineGroupoidAlgebra.{u, q} s t e i c hG ⥤
    Under (groupoidAlgebraCoordinates.{u, q} U) where
  obj A := A.algebra
  map f := f.val

/-- The invariant subring, with its actual equalizer condition beta(a tensor 1)=a tensor 1.
Source: Alper Proposition 8.2.1 (blueprint: def-sfb-affine-groupoid-algebra). -/
def invariants (A : AffineGroupoidAlgebra.{u, q} s t e i c hG) :
    Subring A.algebra.right :=
  RingHom.eqLocus
    (pushout.inl A.algebra.hom (groupoidAlgebraCoordinateMap s) ≫ A.beta.hom).hom
    (pushout.inl A.algebra.hom (groupoidAlgebraCoordinateMap t)).hom

end AffineGroupoidAlgebra

end AlgebraicGeometry.Scheme
