/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Algebraic field-valued images in decent spaces are closed

Source: Stacks Project, Decent Spaces, Tag 07U5; the field-monomorphism condition is
Tag 03JV(4), equivalent to decency, Tag 03I8
(blueprint: lem-sfb-decent-algebraic-field-image-closed).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A field-valued image over a closed base point with algebraic residue extension is a
closed singleton, assuming quasi-compact monomorphic field representatives of all points.
Monomorphic means cancellation against all algebraic-space test objects. Quasi-compact
means representable with quasi-compact scheme projections after every scheme test.
Source: Stacks Project, Decent Spaces, Tags 07U5 and 03JV(4)
(blueprint: lem-sfb-decent-algebraic-field-image-closed).

Proof:
1. Let `x` be the image of `a` and let `x₀` specialize from `x`. Choose an étale scheme
atlas `p : U → X` and `u₀` over `x₀`, using [def-trf-algebraic-space]. Apply
[lem-sfb-decent-space-etale-generalization-lifting] to get `u` specializing to `u₀`
with `p(u) = x`.
2. The scheme `W = Spec L ×_X U` is étale over `Spec L`. By
[lem-a1-space-fibre-product-point] there is `w` above `u`. By
[lem-weil-pbc-etale-fibre-discrete-separable-points], `κ(w)/L` is finite separable,
hence algebraic.
3. The residue-field maps of [def-weil-residue-field] give compatible towers
`κ(s) → L → κ(w)` and `κ(s) → κ(u) → κ(w)`. Apply
[lem-sfb-algebraic-element-tower] to the first tower. Injectivity in the second tower
then implies that every element of `κ(u)` is algebraic over `κ(s)`.
4. Apply [lem-sfb-scheme-algebraic-residue-closed-point] to `U → S`: `u` is closed.
Thus `u = u₀` and `x = x₀`. Every specialization of `x` equals `x`, so `{x}` is closed.
Since `Spec L` has exactly one point [def-weil-affine-spectrum], the point image of `a`
is precisely this singleton. -/
theorem isClosed_pointImage_of_algebraic_residueField
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hdecent : ∀ x : Point X.obj.obj,
      ∃ (K : Type u) (_ : Field K) (b : Spec (CommRingCat.of K) ⟶ S)
        (i : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
        schemePointMap i (IsLocalRing.closedPoint K) = x ∧
        (∀ (Y : AlgebraicSpace S) (f g : Y.obj.obj ⟶ yoneda.obj (Over.mk b)),
          f ≫ i = g ≫ i → f = g) ∧
        IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left) i)
    (L : Type u) [Field L] (b : Spec (CommRingCat.of L) ⟶ S)
    (a : yoneda.obj (Over.mk b) ⟶ X.obj.obj)
    (hs : IsClosed ({b (IsLocalRing.closedPoint L)} : Set S))
    (halg : ∀ c : L, ∃ p : Polynomial (S.residueField (b (IsLocalRing.closedPoint L))),
      p ≠ 0 ∧ p.eval₂ (S.descResidueField (Scheme.stalkClosedPointTo b)).hom c = 0) :
    IsClosed ({schemePointMap a (IsLocalRing.closedPoint L)} : Set (Point X.obj.obj)) ∧
      pointImage a = {schemePointMap a (IsLocalRing.closedPoint L)} := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
