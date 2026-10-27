/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Finitely presented étale spaces and cartesian descent realizations

Source: Rydh, Submersions and effective descent of étale morphisms, Notation (5.1),
Remark (5.2), (5.5), and Propositions (5.6)--(5.7), pp.17--19
(blueprint: def-sfb-fp-etale-space-descent).

An ambient scheme `S` is fixed only to use the existing category of algebraic spaces.
Spaces over a scheme `T → S` are objects of the over category of its representable space.
The cartesian-square descriptions below are invariant under the unique isomorphisms
between pullbacks. They specify actual compatible realization maps, not object classes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A scheme morphism as a morphism of its existing representable algebraic spaces.
Source: Rydh (5.1), commutative squares (blueprint: def-sfb-fp-etale-space-descent). -/
def descentSchemeMap {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    schemeSpace X ⟶ schemeSpace Y :=
  ObjectProperty.homMk ⟨yoneda.map f⟩

/-- The fibre category of finitely presented chartwise étale spaces, with all maps over T.
Source: Rydh (5.1)--(5.2) (blueprint: def-sfb-fp-etale-space-descent). -/
abbrev FpEtaleSpace {S : Scheme.{u}} (T : Over S) :=
  ObjectProperty.FullSubcategory (fun A : Over (schemeSpace T) ↦
    IsChartwiseEtale A.hom ∧ MapIsLocallyOfFinitePresentation A.hom ∧
      IsQuasiCompactPresheafMap A.hom.hom.hom ∧
      IsQuasiCompactPresheafMap (pullback.diagonal A.hom.hom.hom))

/-- Descent data use the upstream natural transport, including identity and cocycle.
Source: Rydh (5.5) (blueprint: def-sfb-fp-etale-space-descent). -/
structure FpEtaleDescentData {S : Scheme.{u}} {X T : Over S} (q : X ⟶ T) where
  /-- The finitely presented étale object on the source. -/
  obj : FpEtaleSpace X
  /-- The isomorphism of pullbacks, in its equivalent natural transport form. -/
  datum : Over.DescentDatum (descentSchemeMap q) obj.obj

namespace FpEtaleDescentData

variable {S : Scheme.{u}} {X T : Over S} {q : X ⟶ T}

/-- Arrows are maps over the source which commute with transport.
Source: Rydh (5.5) (blueprint: def-sfb-fp-etale-space-descent). -/
@[ext]
structure Hom (A B : FpEtaleDescentData q) where
  /-- The map over the source. -/
  hom : A.obj.obj ⟶ B.obj.obj
  /-- Compatibility with the descent isomorphisms. -/
  commutes : ∀ {R : AlgebraicSpace S} (f₁ f₂ : R ⟶ schemeSpace X)
    (h : f₁ ≫ descentSchemeMap q = f₂ ≫ descentSchemeMap q)
    (z : Over.mk f₁ ⟶ A.obj.obj),
    B.datum.transport f₁ f₂ h (z ≫ hom) = A.datum.transport f₁ f₂ h z ≫ hom

/-- Composition and identities of compatible arrows are those in the over category.
Source: Rydh (5.5) (blueprint: def-sfb-fp-etale-space-descent). -/
instance : Category (FpEtaleDescentData q) where
  Hom := Hom
  id A := { hom := 𝟙 A.obj.obj, commutes := by intros; simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      commutes := by
        intro R f₁ f₂ h z
        rw [← Category.assoc, g.commutes, f.commutes, Category.assoc] }
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

/-- A realization includes its structural map, cartesian comparison, and compatibility.
The square is exactly the isomorphism of the given object with the sheaf fibre product.
Source: Rydh (5.5) (blueprint: def-sfb-fp-etale-space-descent). -/
structure Realization (D : FpEtaleDescentData q) where
  /-- The descended object in the same finite-presentation fibre category. -/
  obj : FpEtaleSpace T
  /-- The comparison projection to the descended object. -/
  map : D.obj.obj.left ⟶ obj.obj.left
  /-- This is the canonical sheaf pullback, specified by its universal property. -/
  cartesian : IsPullback map D.obj.obj.hom obj.obj.hom (descentSchemeMap q)
  /-- The comparison identifies the given transport with the canonical transport. -/
  compatible : ∀ {R : AlgebraicSpace S} (f₁ f₂ : R ⟶ schemeSpace X)
    (h : f₁ ≫ descentSchemeMap q = f₂ ≫ descentSchemeMap q)
    (z : Over.mk f₁ ⟶ D.obj.obj),
    (D.datum.transport f₁ f₂ h z).left ≫ map = z.left ≫ map

end FpEtaleDescentData

/-- Full faithfulness of the canonical descent comparison, in Hom equalizer form.
A map from the pullback of A into B descends exactly when it is constant on the two
projections of that pullback's kernel pair. The unique descended map is over the base.
Source: Rydh (5.3), (5.5) (blueprint: def-sfb-fp-etale-space-descent). -/
def FpEtaleDescendsMorphisms {S : Scheme.{u}} {X T : Over S} (q : X ⟶ T) : Prop :=
  ∀ (A B : FpEtaleSpace T) (P : AlgebraicSpace S)
    (p : P ⟶ A.obj.left) (r : P ⟶ schemeSpace X),
    IsPullback p r A.obj.hom (descentSchemeMap q) →
    ∀ (v : P ⟶ B.obj.left), v ≫ B.obj.hom = r ≫ descentSchemeMap q →
      (∀ (R : AlgebraicSpace S) (s t : R ⟶ P), s ≫ p = t ≫ p → s ≫ v = t ≫ v) →
      ∃! f : A.obj ⟶ B.obj, p ≫ f.left = v

/-- Universality means Hom descent after every quasi-separated scheme base change.
All cartesian representatives are allowed, so there is no dependence on chosen pullbacks.
Source: Rydh (5.5) (blueprint: def-sfb-fp-etale-space-descent). -/
def IsUniversalFpEtaleDescent {S : Scheme.{u}} {X T : Over S} (q : X ⟶ T) : Prop :=
  ∀ (V P : Over S), QuasiSeparatedSpace V.left → QuasiSeparatedSpace P.left →
    ∀ (g : V ⟶ T) (h : P ⟶ X) (r : P ⟶ V), IsPullback h r q g →
      FpEtaleDescendsMorphisms r

/-- Universal effective descent combines full faithfulness with compatible realizations
of every datum, after every quasi-separated scheme base change.
Source: Rydh (5.5) (blueprint: def-sfb-fp-etale-space-descent). -/
def IsUniversalEffectiveFpEtaleDescent {S : Scheme.{u}} {X T : Over S}
    (q : X ⟶ T) : Prop :=
  IsUniversalFpEtaleDescent q ∧
    ∀ (V P : Over S), QuasiSeparatedSpace V.left → QuasiSeparatedSpace P.left →
      ∀ (g : V ⟶ T) (h : P ⟶ X) (r : P ⟶ V), IsPullback h r q g →
        ∀ D : FpEtaleDescentData r, Nonempty D.Realization

/-- A cartesian map of data along a cartesian square of bases: the transport equation
is the actual comparison with the pullback datum, including the underlying pullback square.
Source: Rydh (5.5), Proposition (5.7) (blueprint: def-sfb-fp-etale-space-descent). -/
structure FpEtaleDatumPullback {S : Scheme.{u}} {X T V P : Over S}
    {q : X ⟶ T} {g : V ⟶ T} {h : P ⟶ X} {r : P ⟶ V}
    (square : IsPullback h r q g) (D : FpEtaleDescentData q)
    (E : FpEtaleDescentData r) where
  /-- The map from the pulled back object to the original one. -/
  map : E.obj.obj.left ⟶ D.obj.obj.left
  /-- Its square is cartesian, rather than just commutative. -/
  cartesian : IsPullback map E.obj.obj.hom D.obj.obj.hom (descentSchemeMap h)
  /-- Compatibility of the two descent isomorphisms. -/
  compatible : ∀ {R : AlgebraicSpace S} (f₁ f₂ : R ⟶ schemeSpace P)
    (e : f₁ ≫ descentSchemeMap r = f₂ ≫ descentSchemeMap r)
    (e' : (f₁ ≫ descentSchemeMap h) ≫ descentSchemeMap q =
      (f₂ ≫ descentSchemeMap h) ≫ descentSchemeMap q)
    (z : Over.mk f₁ ⟶ E.obj.obj) (w : Over.mk (f₁ ≫ descentSchemeMap h) ⟶ D.obj.obj),
    w.left = z.left ≫ map →
      (D.datum.transport _ _ e' w).left = (E.datum.transport _ _ e z).left ≫ map

end AlgebraicGeometry.AlgebraicSpace
