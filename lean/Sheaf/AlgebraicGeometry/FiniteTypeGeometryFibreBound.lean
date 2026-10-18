/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Finite-type ambient geometry and a uniform geometric-fibre dimension bound

Source: Stacks Project, Morphisms, Tag 0A3V, with the affine polynomial-presentation
refinement described in the DAG node (blueprint: lem-cbc-compactification-geometry-fibre-bound).
The refinement also uses Algebra Tags 00FN and 00KE, Schemes Tags 01JR and 01I4,
and `MvPolynomial.ringKrullDim_of_isNoetherianRing`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite-type morphism over a scheme with a finite Noetherian affine cover and finite
Krull dimension has the same source finiteness properties, a uniform dimension bound on all
geometric fibres, and preserves invertibility of integers in local rings.

Source: Stacks Project, Morphisms, Tag 0A3V and its affine-generator refinement; Algebra
Tags 00FN and 00KE; Schemes Tags 01JR, 01I4 and 01IJ
(blueprint: lem-cbc-compactification-geometry-fibre-bound).

Proof, following the nine steps of the node:
1. Choose the finite Noetherian affine cover Spec R_a of Y. Finite type gives finite affine
   covers Spec S_ab above each chart and finite algebra generating sets of sizes n_ab
   (`def-weil-finite-type-morphism`, `def-weil-pbc-finite-type-algebra`). Choose e to be the
   maximum of 0 and these finitely many sizes, before choosing a geometric point.
2. Each S_ab is Noetherian by `lem-weil-pbc-finite-type-algebra-noetherian`. These affine
   opens form the required finite Noetherian affine cover of T.
3. Choose D bounding dim Y. Open-subspace monotonicity and the spectrum/ring comparison
   (`lem-weil-pbc-open-subspace-dimension-monotone`,
   `lem-weil-pbc-spec-topological-krull-dimension-ring`) bound dim R_a by D. The polynomial
   dimension theorem `lem-sf-noetherian-polynomial-dimension` bounds R_a[x_1,...,x_n_ab] by
   D + e. The surjection onto S_ab pulls prime chains back strictly, so dim S_ab is at most
   D + e (`def-weil-pbc-krull-dimension-ring`), also for zero rings.
4. Schemes are sober (`lem-sc-scheme-sober`), hence quasi-sober and T0. Apply
   `lem-weil-pbc-dimension-bound-open-cover` to get dim T at most D + e.
5. For h : Spec Omega to Y, choose a base chart containing its unique image point. By
   `lem-weil-pbc-open-fibre-product` the corresponding source charts give an open cover
   of the fibre, and `lem-weil-pbc-fibre-product-affine-spectra` identifies their rings
   with S_ab tensor_{R_a} Omega, compatibly with the projections.
6. The elements s_ab,i tensor 1 generate each tensor algebra over Omega: write s as a
   polynomial in the chosen generators and use balancing to move coefficients across
   each pure tensor, then use additivity. The multiplication and inclusions are those of
   `lem-weil-pbc-algebra-tensor-pushout-universal-property`; the tensor module is
   `def-weil-module-base-change`. Evaluation (`def-weil-pbc-mv-polynomial-ring`) gives a
   surjection Omega[x_1,...,x_n_ab] onto the tensor ring, without a flatness hypothesis.
7. A field is Noetherian of dimension zero. The polynomial dimension theorem and strict
   inverse image of prime chains give dimension at most n_ab, hence e, on each fibre
   chart. The spectrum comparison turns this into its topological dimension bound;
   zero tensor rings have empty spectrum and satisfy the bound as well.
8. Apply `lem-weil-pbc-dimension-bound-open-cover` again, using sobriety of the fibre
   scheme, to obtain its dimension bound e. The same e works for every Omega and h.
   Empty fibres, empty charts and empty covers are permitted throughout.
9. The local ring map from O_{Y,p(t)} to O_{T,t} supplied by the scheme morphism sends
   an inverse of N to an inverse of N. For empty T the stalk assertion is vacuous. -/
theorem finiteType_noetherianCover_dimension_geometricFibres
    {T Y : Scheme.{u}} (p : T ⟶ Y) [LocallyOfFiniteType p] [QuasiCompact p]
    (hYCover : ∃ (n : ℕ) (U : Fin n → Y.affineOpens),
      (⨆ i, (U i).1) = ⊤ ∧ ∀ i, IsNoetherianRing Γ(Y, (U i).1))
    (hYDim : ∃ d : ℕ, topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) :
    (∃ (n : ℕ) (U : Fin n → T.affineOpens),
      (⨆ i, (U i).1) = ⊤ ∧ ∀ i, IsNoetherianRing Γ(T, (U i).1)) ∧
    (∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞)) ∧
    (∃ e : ℕ, ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (h : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (↑(pullback p h) : Type u) ≤ (e : WithBot ℕ∞)) ∧
    ∀ N : ℤ, (∀ y : Y, IsUnit (N : Y.presheaf.stalk y)) →
      ∀ t : T, IsUnit (N : T.presheaf.stalk t) := by
  sorry

end AlgebraicGeometry
