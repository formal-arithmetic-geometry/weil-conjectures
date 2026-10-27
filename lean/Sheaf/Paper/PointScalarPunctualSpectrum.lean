/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.Paper.PointWeilHeartFlagData

/-! # Punctual eigenvalues of a scalar local operator at a finite-field point

Source: latest blueprint, `thm-zl-real-mixed-by-curves`, paragraph 7,
identification of the scalar factors of the dimension-zero Jordan filtration
(blueprint: lem-zl-point-scalar-punctual-spectrum).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (y : {y : (zlPointBase D).left // y ∈ closedPoints (zlPointBase D).left})
  (ι : (zlPointBase D).left.residueField y.val →+* D.k)
  (hι : ι.comp ((zlPointBase D).hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)

/-- A scalar local operator at the point determines every eigenvalue in the
finite-presentation definition of the punctual spectrum. Every closed point of
Spec(k0) has residue cardinality q.

Source: latest blueprint, `thm-zl-real-mixed-by-curves`, paragraph 7,
dimension-zero scalar factors, and the local-Frobenius conjugacy convention
(blueprint: lem-zl-point-scalar-punctual-spectrum).

Proof: the spectrum of Spec(k0) is a singleton. Its residue field at its sole point
is canonically isomorphic to k0 over k0, so its cardinality is q and its degree is one.
Every compatible embedding of that residue field into the fixed closure is the same
k0-algebra embedding. For any finite Weil presentation witnessing a punctual eigenvalue,
apply the prescribed scalar/cohomology comparison and its Weil-equivariant comparison
with F. Naturality and coefficient compatibility of point transport intertwine its
extended local Frobenius with the specified local operator on F. Thus its nonzero
eigenvector maps to a nonzero eigenvector for the scalar operator alpha. Subtracting
the two scalar equations gives (beta-alpha) times that vector equal to zero; over a
field this forces beta=alpha. For the zero fibre there are no eigenvalues and the
implication is vacuous. No one-dimensionality hypothesis is needed. -/
theorem zl_point_scalar_punctual_spectrum
    (F : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω) (α : Ω)
    (hα : ∀ v : (zlPointWeilFiber D l hl Ω y ι hι).obj F,
      (zlPointWeilFrobenius D l hl Ω y ι hι F).hom v = α • v)
    (z : {z : (zlPointBase D).left // z ∈ closedPoints (zlPointBase D).left})
    (β : Ω) (hβ : SfPunctualEigenvalue D l hl Ω (zlPointBase D) F z β) :
    β = α ∧ Nat.card ((zlPointBase D).left.residueField z.val) = D.q := by sorry

end WeilConjectures
