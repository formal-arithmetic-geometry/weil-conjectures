/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.HasUniversallyBoundedFibersOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite

/-!
# Finite fibres transfer from an étale covering to affine étale charts

Source: Stacks Project, Decent Algebraic Spaces, Tag 03JS, implication (1) to (2)
(blueprint: lem-sfb-etale-chart-finite-fibre-transfer).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Finite fibres above a point in a jointly surjective étale scheme covering imply
finite fibres above that point in every affine étale chart. The covering schemes need
not be affine or quasi-compact; their fibres may be empty, and no condition is imposed
on their self-intersections.

Source: Stacks Project, Decent Algebraic Spaces, Tag 03JS, implication (1) to (2)
(blueprint: lem-sfb-etale-chart-finite-fibre-transfer).

Proof:
1. For an affine étale chart `V → X`, form the schemes `Pᵢ = V ×_X Uᵢ`.
   Representability and base change give étale projections `pᵢ : Pᵢ → Uᵢ` and
   `qᵢ : Pᵢ → V`; the latter are jointly surjective
   (`def-trf-algebraic-space`, `lem-trf-space-fibre-products-etale-covers`).
2. Cover each `Pᵢ` by affine opens. Their images in `V` are open and cover `V`.
   Compactness of the affine scheme `V` selects finitely many such opens `Wⱼ`,
   each quasi-compact. This uses `lem-weil-pbc-affine-opens-basis`,
   `lem-weil-pbc-etale-morphism-open-map`, and
   `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`.
3. Each restriction `rⱼ : Wⱼ → Uᵢⱼ` is locally quasi-finite: étale implies
   unramified, and local quasi-finiteness survives open restriction
   (`def-weil-etale-morphism`, `lem-weil-pbc-unramified-quasi-finite-at-points`,
   `lem-weil-pbc-lqf-restriction-to-opens`). The quasi-compact-source theorem
   `lem-weil-pbc-lqf-qc-source-bounded-fibres` makes every scheme fibre finite
   over its residue field. The spectrum of that field has one point, so
   `lem-weil-pbc-finite-closed-map-finite-fibres` makes the scheme fibre's point
   set finite. Its homeomorphism with the point inverse image
   (`def-pc-scheme-fibre`, `def-weil-affine-spectrum`) gives finite fibres of `rⱼ`.
4. The inverse image under `rⱼ` of the given finite fibre in `Uᵢⱼ` is therefore
   finite. Its image under `qᵢⱼ` lies in the fibre in `V` by commutativity of
   the pullback square. Conversely, every point of that fibre lifts to some
   `Wⱼ`, and its image in `Uᵢⱼ` lies over `x`. Thus the desired fibre is the
   finite union of these finite images. Empty fibres and the empty chart
   contribute empty sets. -/
theorem finite_preimage_singleton_of_etaleCover {S : Scheme.{u}}
    (X : AlgebraicSpace S) (x : Point X.obj.obj) {I : Type w}
    (U : I → Over S) (a : ∀ i : I, yoneda.obj (U i) ⟶ X.obj.obj)
    (ha : ∀ i : I, IsEtale (a i))
    (hcover : ∀ y : Point X.obj.obj,
      ∃ (i : I) (t : (U i).left), schemePointMap (a i) t = y)
    (hfinite : ∀ i : I, (schemePointMap (a i) ⁻¹' {x}).Finite)
    (V : Over S) [IsAffine V.left] (v : yoneda.obj V ⟶ X.obj.obj)
    (hv : IsEtale v) : (schemePointMap v ⁻¹' {x}).Finite := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
