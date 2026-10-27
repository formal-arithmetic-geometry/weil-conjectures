module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Relative rational maps and birational group laws

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 2.5 and 5.1 Definition 1
(blueprint: def-sfb-relative-birational-group-law).

The definitions use the chosen fibre products in the slice category. Associativity is
stated on all scheme-valued points, so includes the scheme structure of the common domain.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry
namespace RelativeGroupLaw

/-- Fibrewise density of a subset of an `S`-scheme, using scheme-theoretic fibres.
Source: BLR 2.5, S-density (blueprint: def-sfb-relative-birational-group-law). -/
def IsFiberwiseDense {S : Scheme.{u}} (X : Over S) (U : Set X.left) : Prop :=
  ∀ s : S, Dense ((X.hom.fiberι s) ⁻¹' U)

/-- A representative of an S-rational map is an S-morphism on an S-dense open.
Source: BLR 2.5 (blueprint: def-sfb-relative-birational-group-law). -/
structure Representative {S : Scheme.{u}} (X Y : Over S) where
  /-- The open domain in the source. -/
  domain : X.left.Opens
  /-- The domain meets every fibre densely. -/
  dense_domain : IsFiberwiseDense X (domain : Set X.left)
  /-- The morphism on this open, over the base. -/
  hom : Over.mk (domain.ι ≫ X.hom) ⟶ Y

/-- The open domain as an S-scheme.
Source: BLR 2.5 (blueprint: def-sfb-relative-birational-group-law). -/
def Representative.source {S : Scheme.{u}} {X Y : Over S}
    (f : Representative X Y) : Over S :=
  Over.mk (f.domain.ι ≫ X.hom)

/-- Inclusion of the domain of a representative.
Source: BLR 2.5 (blueprint: def-sfb-relative-birational-group-law). -/
def Representative.inclusion {S : Scheme.{u}} {X Y : Over S}
    (f : Representative X Y) : f.source ⟶ X :=
  Over.homMk f.domain.ι

/-- Agreement on a fibrewise dense common open is the equivalence on representatives.
Source: BLR 2.5 (blueprint: def-sfb-relative-birational-group-law). -/
def Representative.Agrees {S : Scheme.{u}} {X Y : Over S}
    (f g : Representative X Y) : Prop :=
  ∃ (W : X.left.Opens) (hf : W ≤ f.domain) (hg : W ≤ g.domain),
    IsFiberwiseDense X (W : Set X.left) ∧
    X.left.homOfLE hf ≫ f.hom.left = X.left.homOfLE hg ≫ g.hom.left

/-- S-rational maps are the quotient by agreement on S-dense common opens.
Source: BLR 2.5 (blueprint: def-sfb-relative-birational-group-law). -/
def RationalMap {S : Scheme.{u}} (X Y : Over S) : Type u :=
  Quot (Representative.Agrees (X := X) (Y := Y))

/-- A map on an open domain is S-birational when it becomes an open immersion
between fibrewise dense opens after restriction. An open immersion identifies its source
with its open image, so this is precisely an isomorphism between such opens.
Source: BLR 2.5 and 5.1 Definition 1 (blueprint: def-sfb-relative-birational-group-law). -/
def IsBirationalOnDomain {S : Scheme.{u}} {D X : Over S}
    (inclusion f : D ⟶ X) : Prop :=
  ∃ W : D.left.Opens,
    IsFiberwiseDense X (Set.range (W.ι ≫ inclusion.left)) ∧
    IsOpenImmersion (W.ι ≫ f.left) ∧
    IsFiberwiseDense X (Set.range (W.ι ≫ f.left))

/-- The universal left translation `(x,y) ↦ (x,m(x,y))` on the chosen domain.
Source: BLR 5.1 Definition 1(a) (blueprint: def-sfb-relative-birational-group-law). -/
noncomputable def leftTranslation {S : Scheme.{u}} {X : Over S}
    (m : Representative (X ⊗ X) X) : m.source ⟶ X ⊗ X :=
  lift (m.inclusion ≫ fst X X) m.hom

/-- The universal right translation `(x,y) ↦ (m(x,y),y)` on the chosen domain.
Source: BLR 5.1 Definition 1(a) (blueprint: def-sfb-relative-birational-group-law). -/
noncomputable def rightTranslation {S : Scheme.{u}} {X : Over S}
    (m : Representative (X ⊗ X) X) : m.source ⟶ X ⊗ X :=
  lift m.hom (m.inclusion ≫ snd X X)

/-- Associativity wherever both composites are defined. The four domain lifts express
that `(x,y)`, `(y,z)`, `(m(x,y),z)` and `(x,m(y,z))` lie in the multiplication domain.
Quantifying over every test S-scheme gives equality of morphisms, including nilpotents.
Source: BLR 5.1 Definition 1(b) (blueprint: def-sfb-relative-birational-group-law). -/
def IsAssociative {S : Scheme.{u}} {X : Over S}
    (m : Representative (X ⊗ X) X) : Prop :=
  ∀ (A : Over S) (x y z : A ⟶ X) (a b c d : A ⟶ m.source),
    a ≫ m.inclusion = lift x y →
    b ≫ m.inclusion = lift y z →
    c ≫ m.inclusion = lift (a ≫ m.hom) z →
    d ≫ m.inclusion = lift x (b ≫ m.hom) →
    c ≫ m.hom = d ≫ m.hom

/-- An S-birational group law has birational universal translations and is associative.
Source: BLR 5.1 Definition 1 (blueprint: def-sfb-relative-birational-group-law). -/
def IsBirationalGroupLaw {S : Scheme.{u}} {X : Over S}
    (m : Representative (X ⊗ X) X) : Prop :=
  IsBirationalOnDomain m.inclusion (leftTranslation m) ∧
  IsBirationalOnDomain m.inclusion (rightTranslation m) ∧ IsAssociative m

end RelativeGroupLaw
end AlgebraicGeometry
