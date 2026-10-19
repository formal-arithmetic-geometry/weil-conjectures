/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.AlgebraicGeometry.GeometricSpecializationCategory
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.CategoryTheory.ComposableArrows.Basic
import Sheaf.AlgebraicGeometry.LocalDimensionFunctionCalculus
import Sheaf.AlgebraicGeometry.RegularDimensionFunctionPullback
import Sheaf.AlgebraicGeometry.RegularStrictLocalModel
import Sheaf.AlgebraicGeometry.StrictLocalRegularIntegralFibres

/-!
# Generic-fibre lifting and codimension for regular specializations

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
Lemmas 4.3.2.3--4.3.2.6, printed pp. 284--285; Expose XIV, Proposition 2.5.4
(blueprint: lem-per-regular-specialization-geometry).

The four predicates below spell out the four conclusions, including commutation of
strict-local maps, uniqueness up to isomorphism, finite factorizations, and the dimension
formula. They impose no finite-type condition on the regular morphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RegularSpecializationGeometry

/-- A map of geometric points over `r`, expressed by a local map of strict localizations.
The last field is the local condition, so these are not arbitrary maps over `r`.
Source: ILO XIV, Definition 2.1.1; XVII, Lemma 4.3.2.4
(blueprint: lem-per-regular-specialization-geometry). -/
structure PointMap {P X : Scheme.{u}} (r : P ⟶ X)
    (p : StrictGeometricPoint P) (x : StrictGeometricPoint X) where
  map : p.localization.left ⟶ x.localization.left
  over : map ≫ x.localization.hom = p.localization.hom ≫ r
  closed : map p.closed = x.closed

/-- Dimension of the local ring of the original scheme-theoretic fibre at a point.
Source: ILO XIV, Proposition 2.5.4; XVII, Lemma 4.3.2.4
(blueprint: lem-per-regular-specialization-geometry). -/
def fibreLocalDimension {P X : Scheme.{u}} (r : P ⟶ X)
    (p : StrictGeometricPoint P) : WithBot ℕ∞ :=
  ringKrullDim ((r.fiber (r p.underlying)).presheaf.stalk (r.asFiber p.underlying))

/-- Fibre-generic means codimension zero in the fibre, using its actual local ring.
Source: ILO XVII, Lemmas 4.3.2.4--4.3.2.6
(blueprint: lem-per-regular-specialization-geometry). -/
def IsFibreGeneric {P X : Scheme.{u}} (r : P ⟶ X) (p : StrictGeometricPoint P) : Prop :=
  fibreLocalDimension r p = 0

/-- A specified specialization lies over another specified specialization.
Source: ILO XVII, Lemma 4.3.2.6
(blueprint: lem-per-regular-specialization-geometry). -/
def LiesOver {P X : Scheme.{u}} {r : P ⟶ X}
    {p q : StrictGeometricPoint P} {x y : StrictGeometricPoint X}
    (a : p ⟶ q) (s : x ⟶ y) (vp : PointMap r p x) (vq : PointMap r q y) : Prop :=
  a.hom.left ≫ vq.map = vp.map ≫ s.hom.left

/-- The commutative generic-fibre square, including both vertical fibre conditions and
both vertical codimensions. Source: ILO XVII, Lemma 4.3.2.6; XIV, Proposition 2.5.4
(blueprint: lem-per-regular-specialization-geometry). -/
def HasGenericSquares {P X : Scheme.{u}} (r : P ⟶ X) : Prop :=
  ∀ (p q : StrictGeometricPoint P) (x y : StrictGeometricPoint X)
    (a : p ⟶ q) (s : x ⟶ y) (vp : PointMap r p x) (vq : PointMap r q y),
    LiesOver a s vp vq →
    ∃ (ep eq : StrictGeometricPoint P) (bp : PointMap r ep x) (bq : PointMap r eq y)
      (h : ep ⟶ eq) (l : ep ⟶ p) (k : eq ⟶ q),
      IsFibreGeneric r ep ∧ IsFibreGeneric r eq ∧
      h ≫ k = l ≫ a ∧ LiesOver h s bp bq ∧
      l.hom.left ≫ vp.map = bp.map ∧ k.hom.left ≫ vq.map = bq.map ∧
      StrictGeometricPoint.codimension l = fibreLocalDimension r p ∧
      StrictGeometricPoint.codimension k = fibreLocalDimension r q

/-- Existence and uniqueness up to a not necessarily unique isomorphism of generic lifts.
The isomorphism commutes with the lift and with its map to the specified base point.
Source: ILO XVII, Lemma 4.3.2.4
(blueprint: lem-per-regular-specialization-geometry). -/
def HasUniqueGenericLifts {P X : Scheme.{u}} (r : P ⟶ X) : Prop :=
  ∀ (q : StrictGeometricPoint P) (y : StrictGeometricPoint X) (vq : PointMap r q y),
    IsFibreGeneric r q →
    ∀ (x : StrictGeometricPoint X) (s : x ⟶ y),
      ∃ (p : StrictGeometricPoint P) (vp : PointMap r p x) (a : p ⟶ q),
        IsFibreGeneric r p ∧ LiesOver a s vp vq ∧
        StrictGeometricPoint.codimension a = StrictGeometricPoint.codimension s ∧
        ∀ (p' : StrictGeometricPoint P) (vp' : PointMap r p' x) (a' : p' ⟶ q),
          IsFibreGeneric r p' → LiesOver a' s vp' vq →
          ∃ i : p' ≅ p, i.hom ≫ a = a' ∧ i.hom.hom.left ≫ vp.map = vp'.map

/-- Every immediate factorization downstairs lifts to one of the specified generic arrow.
Endpoint isomorphisms express equality of geometric points through strict localizations.
The total-arrow equality retains the prescribed arrow, including the empty factorization.
Source: ILO XVII, Lemma 4.3.2.5
(blueprint: lem-per-regular-specialization-geometry). -/
def HasImmediateGenericFactorizations {P X : Scheme.{u}} (r : P ⟶ X) : Prop :=
  ∀ (p q : StrictGeometricPoint P) (x y : StrictGeometricPoint X)
    (a : p ⟶ q) (s : x ⟶ y) (vp : PointMap r p x) (vq : PointMap r q y),
    IsFibreGeneric r p → IsFibreGeneric r q → LiesOver a s vp vq →
    ∀ (n : ℕ) (D : ComposableArrows (StrictGeometricPoint X) n)
      (first : x ≅ D.left) (last : D.right ≅ y),
      first.hom ≫ D.hom ≫ last.hom = s →
      (∀ i : Fin n, StrictGeometricPoint.IsImmediate
        (D.map (homOfLE (Fin.castSucc_le_succ i)))) →
      ∃ (E : ComposableArrows (StrictGeometricPoint P) n)
        (first' : p ≅ E.left) (last' : E.right ≅ q)
        (v : ∀ i : Fin (n + 1), PointMap r (E.obj i) (D.obj i)),
        first'.hom ≫ E.hom ≫ last'.hom = a ∧
        (∀ i : Fin (n + 1), IsFibreGeneric r (E.obj i)) ∧
        (∀ i : Fin n, StrictGeometricPoint.IsImmediate
          (E.map (homOfLE (Fin.castSucc_le_succ i)))) ∧
        (∀ (i j : Fin (n + 1)) (f : i ⟶ j),
          (E.map f).hom.left ≫ (v j).map = (v i).map ≫ (D.map f).hom.left) ∧
        first'.hom.hom.left ≫ (v 0).map = vp.map ≫ first.hom.hom.left ∧
        (v (Fin.last n)).map ≫ last.hom.hom.left = last'.hom.hom.left ≫ vq.map

/-- The integer dimension formula, expressed without truncating extended dimensions:
the existential natural numbers are identified with the actual four Krull dimensions
before the subtraction is taken in the integers. No infinite dimension is assigned zero.
Source: ILO XIV, Proposition 2.5.4; XVII, Lemma 4.3.2.4
(blueprint: lem-per-regular-specialization-geometry). -/
def HasCodimensionFormula {P X : Scheme.{u}} (r : P ⟶ X) : Prop :=
  ∀ (p q : StrictGeometricPoint P) (x y : StrictGeometricPoint X)
    (a : p ⟶ q) (s : x ⟶ y) (vp : PointMap r p x) (vq : PointMap r q y),
    LiesOver a s vp vq →
    ∃ cp cx bp bq : ℕ,
      StrictGeometricPoint.codimension a = (cp : WithBot ℕ∞) ∧
      StrictGeometricPoint.codimension s = (cx : WithBot ℕ∞) ∧
      fibreLocalDimension r p = (bp : WithBot ℕ∞) ∧
      fibreLocalDimension r q = (bq : WithBot ℕ∞) ∧
      (cp : ℤ) = (cx : ℤ) + (bq : ℤ) - (bp : ℤ)

/-- Regular morphisms have generic-fibre specialization squares, unique generic lifts,
immediate generic factorizations, and the stated codimension formula.
Source: ILO XVII, Lemmas 4.3.2.3--4.3.2.6; XIV, Proposition 2.5.4
(blueprint: lem-per-regular-specialization-geometry).

Proof:
1. Work in the specified strict local schemes P_(t) and X_(x).
   `lem-per-regular-strict-local-model` gives regularity, excellence, Noetherianity,
   and preservation of the original local fibre dimensions. Choose a dimension function
   by `lem-per-local-dimension-function-calculus`. By
   `lem-per-regular-dimension-function-pullback`, delta_P(u) = delta_X(r(u)) - b(u).
   The difference formula of the calculus node gives c_P = c_X + b(target) - b(source).
2. At a fibre-generic target, `lem-per-strict-local-regular-integral-fibres` makes the
   geometric fibre over the prescribed generic base point nonempty and integral. Its
   unique generic point gives a fibre-generic lift. Any other lift has the same generic
   point there; identifying separable closures gives an isomorphism over that fibre,
   commuting with the prescribed target map. This isomorphism need not be unique.
3. Both endpoint fibre dimensions of this lift are zero. Step 1 therefore gives equality
   with the base codimension, including identity arrows and geometric isomorphisms.
4. Lift a finite immediate factorization backwards from its specified target by Step 2.
   Step 3 makes every lifted arrow immediate. Uniqueness identifies the composite with
   the prescribed generic lift, up to its source isomorphism. The empty chain gives
   the identity case.
5. For an arbitrary bottom arrow, choose a geometric generic point of the integral
   closed fibre in P_(t), and lift the base arrow by Step 2. The other integral fibre
   contains t' and has one generic point. Identify its generic point with the lifted
   one to obtain the left vertical arrow. Both composites are structural maps over
   P_(t), so the square commutes and both vertical arrows lie in their specified fibres.
6. Apply Step 1 to the two vertical arrows, whose base arrows are identities. Their
   codimensions are b(t') and b(t). The same formula for the original bottom arrow is
   the final identity. Local Noetherian rings and the local reduced closures here have
   finite dimension, justifying the natural representatives used before integer subtraction.
-/
theorem regular_specialization_geometry
    {P X : Scheme.{u}} (r : P ⟶ X) [IsNoetherian P] [IsNoetherian X]
    (hP : ∀ U : P.affineOpens, IsExcellent Γ(P, U))
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    [Flat r]
    (hregular : ∀ (x : X) (L : Type u) [Field L]
      [Algebra (X.residueField x) L] [Module.Finite (X.residueField x) L],
      IsRegularScheme (pullback (r.fiberToSpecResidueField x)
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) L))))) :
    HasGenericSquares r ∧ HasUniqueGenericLifts r ∧
      HasImmediateGenericFactorizations r ∧ HasCodimensionFormula r := by
  sorry

end AlgebraicGeometry.RegularSpecializationGeometry
