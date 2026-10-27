/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Basis.Defs

/-! # Rational projective weight coordinates

Source: Milne, Algebraic Groups (2017), Theorem 12.12, pp.234--235,
Lemma 13.51 and Proposition 13.53(a), pp.274--276, and Theorem 17.65, p.374.
(blueprint: def-sfb-torus-projective-weight-data).

These definitions use the existing group schemes, character morphisms, coordinate
projective space, coordinate sections and generating locus. No action or comparison
map is selected from an existence assertion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace AlgebraicGeometry.TorusProjectiveWeight

variable {k : Type u} [Field k] {I : Type u} [Fintype I] [DecidableEq I]

/-- Coordinates as actual global sections of Spec A.
Source: Milne, Example 13.50, p.274; projective homogeneous coordinates.
(blueprint: def-sfb-torus-projective-weight-data). -/
def sections (A : CommAlgCat.{u} k) (v : I → A) : I → Γ(Spec (.of A), ⊤) :=
  fun i ↦ (Scheme.ΓSpecIso (.of A)).inv (v i)

/-- A generating vector represents the specified line-valued point. Over a general
algebra this describes points whose tautological line is trivialized by that vector;
such points cover all points locally. Over a field these are all projective points.
Source: Milne, Example 13.50 and Proposition 13.53, pp.274--276.
(blueprint: def-sfb-torus-projective-weight-data). -/
def Represents (A : CommAlgCat.{u} k)
    (y : StandardGroupSchemes.affine k A ⟶
      Over.mk (ProjectiveSpace I (Spec (.of k)) ↘ Spec (.of k))) (v : I → A) : Prop :=
  ∃ h : Ideal.span (Set.range (sections A v)) = ⊤,
    ProjectiveSpace.homOfSections (StandardGroupSchemes.affine k A).hom (sections A v) h =
      y.left

/-- The actual matrix action of the rational group-scheme representation on A-vectors.
Source: Milne, Definition 12.11, p.234.
(blueprint: def-sfb-torus-projective-weight-data). -/
def vectorAction (T : Grp (Over (Spec (.of k))))
    (ρ : T.X ⟶ GeneralLinearGroup I k) (A : CommAlgCat.{u} k)
    (t : StandardGroupSchemes.affine k A ⟶ T.X) (v : I → A) : I → A :=
  (GeneralLinearGroup.homMulEquiv I k A (t ≫ ρ) : Matrix I I A).mulVec v

/-- An algebraic projective action is induced by rho precisely when it sends every
trivialized line to its matrix image, over every algebra. Equality on these local
trivializations specifies the action on arbitrary line subbundles as well.
Source: Milne, Section 13f, pp.274--275.
(blueprint: def-sfb-torus-projective-weight-data). -/
def IsInduced (T : Grp (Over (Spec (.of k))))
    (ρ : T.X ⟶ GeneralLinearGroup I k)
    [ModObj T.X (Over.mk (ProjectiveSpace I (Spec (.of k)) ↘ Spec (.of k)))] : Prop :=
  ∀ (A : CommAlgCat.{u} k) (t : StandardGroupSchemes.affine k A ⟶ T.X)
    (y : StandardGroupSchemes.affine k A ⟶
      Over.mk (ProjectiveSpace I (Spec (.of k)) ↘ Spec (.of k))) (v : I → A),
    Represents A y v → Represents A (t • y) (vectorAction T ρ A t v)

/-- The weight-vector equation on every algebra, including nonreduced algebras.
The basis merely identifies E tensor A with A^I.
Source: Milne, Definition 12.11 and Theorem 12.12, pp.234--235.
(blueprint: def-sfb-torus-projective-weight-data). -/
def IsWeightVector {E : Type v} [AddCommGroup E] [Module k E]
    (b : Module.Basis I k E) (T : Grp (Over (Spec (.of k))))
    (ρ : T.X ⟶ GeneralLinearGroup I k) (χ : RankOneRoots.Character T) (e : E) : Prop :=
  ∀ (A : CommAlgCat.{u} k) (t : StandardGroupSchemes.affine k A ⟶ T.X),
    vectorAction T ρ A t (fun i ↦ algebraMap k A (b.repr e i)) =
      fun i ↦ RankOneRoots.multiplicativeValue A (t ≫ χ.hom.hom) *
        algebraMap k A (b.repr e i)

/-- A separating cocharacter and its pairings: equality with the Laurent monomial
is tested over every algebra. Negative exponents are Laurent monomials, so no
field or nonzero-ring restriction on the test algebra is imposed.
Source: Milne, Lemma 13.51, p.274.
(blueprint: def-sfb-torus-projective-weight-data). -/
def Separates {Ω : Type w} (T : Grp (Over (Spec (.of k))))
    (χ : Ω → RankOneRoots.Character T) (ell : RankOneRoots.Cocharacter T)
    (m : Ω → ℤ) : Prop :=
  Function.Injective m ∧ ∀ (A : CommAlgCat.{u} k)
    (z : StandardGroupSchemes.affine k A ⟶ StandardGroupSchemes.multiplicative k) (c : Ω),
    RankOneRoots.multiplicativeValue A (z ≫ ell.hom.hom ≫ (χ c).hom.hom) =
      (Scheme.ΓSpecIso (.of A)).hom
        (z.left.appTop ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv
          (LaurentPolynomial.T (m c))))

/-- D(f), the open where the homogeneous linear form associated to f generates O(1).
Its coefficients are f(b_i), pulled back from k along the projective structure map.
Source: Milne, proof of Theorem 17.65, p.374.
(blueprint: def-sfb-torus-projective-weight-data). -/
def dualOpen {E : Type v} [AddCommGroup E] [Module k E]
    (b : Module.Basis I k E) (f : Module.Dual k E) :
    (ProjectiveSpace I (Spec (.of k))).Opens :=
  Scheme.Modules.generatingLocus
    (∑ i : I, (ProjectiveSpace I (Spec (.of k)) ↘ Spec (.of k)).appTop
      ((Scheme.ΓSpecIso (.of k)).inv (f (b i))) •
        ProjectiveSpace.twistOneSection I (Spec (.of k)) i)

end AlgebraicGeometry.TorusProjectiveWeight
