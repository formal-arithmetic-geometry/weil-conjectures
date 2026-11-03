/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.AffineCurveRange.LatticePiece.CurveLatticeCompactData
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement

/-!
# Finite quotient compact support on the curve pieces

Source: latest blueprint, `sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/`
`lem-zl-affine-curve-range.proof.md`, torsion-coefficient paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.AffineCurveRange

/-- The geometric field of a finite-field datum is algebraically closed.
Source: the geometric base change in the range proof
(blueprint: lem-zl-curve-lattice-finite-levels). -/
abbrev finiteLevelsDatumIsAlgClosed (D : FiniteFieldDatum.{u}) : IsAlgClosed D.k :=
  IsAlgClosure.isAlgClosed D.k₀

attribute [local instance] finiteLevelsDatumIsAlgClosed

/-- The canonical finite quotient tower of an integral lattice on a smooth curve
piece has finite cohomology, and its cohomology above degree two vanishes.

Source: latest blueprint, `lem-zl-affine-curve-range.proof.md`, torsion paragraph;
range node steps 4--6 (blueprint: lem-zl-curve-lattice-finite-levels).

Proof: a lisse lattice is locally finite free. Its derived reduction modulo
pi^(n+1) is therefore the ordinary quotient sheaf in degree zero, with the
quotient-induced transition. If the piece has dimension one, decompose its
finitely many connected components and choose smooth proper completions. Exact
open extension retains degree zero and constructibility. Finite discrete
coefficient modules have etale origin; the pro-etale/etale comparison and the
scalar-forgetful comparison identify compact cohomology with etale cohomology
of this extended sheaf. The smooth connected proper curve cohomological-dimension
bound gives vanishing above two. Proper finite-type finiteness gives finite
cohomology over the algebraically closed point. For dimension zero, the smooth
finite-type scheme is finite etale over the algebraically closed field, hence
a finite disjoint union of geometric points; its identity compactification
gives a finite product of finite stalks in degree zero. Negative cohomology
vanishes by a nonnegative injective resolution. Compactification independence
and induction using open--closed triangles give the assertion for the supplied
compactification and all finite component unions, including the empty scheme.
-/
theorem curveLattice_finiteLevels (D : FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (d : LatticePiece ell D.k) :
    (∀ (n : ℕᵒᵖ) (i : ℤ),
      Finite ((DerivedCategory.homologyFunctor Ab.{u + 1} i).obj (d.abelianTower.obj n))) ∧
    (∀ (n : ℕᵒᵖ) (i : ℤ), 2 < i →
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} i).obj
        (d.abelianTower.obj n))) := by
  sorry

end WeilConjectures.AffineCurveRange
