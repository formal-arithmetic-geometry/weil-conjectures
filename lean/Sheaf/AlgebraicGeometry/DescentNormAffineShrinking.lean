/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# Norm shrinking around finite saturated sets

Source: Stacks Project, Tag 03JE.
(blueprint: lem-pd-descent-norm-affine-shrinking).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

/-- A finite saturated set contained in an affine open admits an invariant affine shrinking.
Source: Stacks Project, Tag 03JE, proof after the choice of the affine open W.
(blueprint: lem-pd-descent-norm-affine-shrinking).

Proof: The transport datum makes (R,s,t) a cartesian groupoid. The source s is the
base change of p. Inversion exchanges s and t, so both are finite locally free.
Let Z = t(s⁻¹(V \ A)). This is closed, and its complement W is invariant, is
contained in A, and contains S: saturation prevents an arrow from S to outside A.
Prime avoidance (00DS) gives f on A with S ⊆ D(f) ⊆ W. On s⁻¹(W), t factors through
A. Form g = Norm_s(t* f) on W. The norm criterion says g is nonzero at w exactly
when f is nonzero at every target of an arrow starting at w. This includes every
point of S, by saturation. It is an invariant condition by inverse and composition,
and the identity arrow gives D(g) ⊆ D(f). The restriction of g to the affine D(f)
has the same nonvanishing locus, so D(g) is affine. Take U = D(g); then U ⊆ A and
s⁻¹(U) = t⁻¹(U). For S empty one can take the empty affine open, including when R
and V are empty. No global degree bound is used: the norm is defined for a finite
locally free morphism of locally varying rank. -/
theorem exists_descent_norm_affine_shrinking
    {X Y R : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    (D : Over.DescentDatum p V) (s : R ⟶ V.left) (q : R ⟶ X) (t : R ⟶ V.left)
    (hsq : IsPullback s q (V.hom ≫ p) p)
    (ht : (D.transport (s ≫ V.hom) q
      (by simpa only [Category.assoc] using hsq.w) (Over.homMk s)).left = t)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    (S : Set V.left) (hS : S.Finite) (hstable : s ⁻¹' S = t ⁻¹' S)
    (A : V.left.Opens) (hA : IsAffineOpen A) (hSA : S ⊆ A) :
    ∃ U : V.left.Opens, S ⊆ U ∧ IsAffineOpen U ∧ U ≤ A ∧ s ⁻¹' (U : Set V.left) =
      t ⁻¹' (U : Set V.left) := by
  sorry

end CategoryTheory.Over.DescentDatum
