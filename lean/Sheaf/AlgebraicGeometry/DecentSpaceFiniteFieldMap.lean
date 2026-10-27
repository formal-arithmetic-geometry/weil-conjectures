/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Finite field-valued maps to decent algebraic spaces

Source: Stacks Project, Decent Spaces, Tag 08AL, finite-morphism assertion;
decency is Tag 03I8, equivalently Tag 03JV(6)
(blueprint: lem-sfb-decent-space-finite-field-map).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A field-valued map to a decent algebraic space is representable and finite when its
image in the base is closed and its canonical residue-field extension is finite.
Decency is expanded using the affine scheme tests in Tag 03JV(6). The conclusion uses
`IsRepresentableWith`, so includes both scheme representability and finite projections
for every scheme test.
Source: Stacks Project, Decent Spaces, Tag 08AL, finite-morphism assertion only
(blueprint: lem-sfb-decent-space-finite-field-map).
Proof:
1. By [lem-sfb-decent-quasicompact-monomorphic-points], decency gives quasi-compact
monomorphic field representatives. The affine-test quasi-compactness implies the
scheme-test version: cover a quasi-compact open by finitely many affine opens and
use that their quasi-compact inverse images cover its inverse image. A finite field
extension is algebraic (powers are linearly dependent), so
[lem-sfb-decent-algebraic-field-image-closed] makes the image point of `a` closed.
2. By [lem-sfb-decent-closed-point-field-immersion], choose a representable closed
immersion `i : Spec K → X` representing that closed point.
3. The pullback `P = Spec L ×_X Spec K` is a closed subscheme of `Spec L`. It is
nonempty because `a` and `i` represent the same point: a common field extension gives
a point of `P` [def-a1-algebraic-space-point-classes]. Thus `P = Spec (L/I)` for a
proper ideal of the field `L`, hence `I = 0`; its projection to `Spec L` is an
isomorphism. The other projection yields a factorization `a = i ∘ b`.
4. The residue-field inclusions are `κ(s) ⊆ K ⊆ L`. A finite spanning set over `κ(s)`
also spans over `K`, so `b` is finite by [lem-weil-pbc-spec-finite-ring-map-finite].
5. For each scheme `T → X`, form the closed subscheme `W = T ×_X Spec K`. Pasting
pullback squares identifies `T ×_X Spec L` with `W ×_Spec K Spec L`. Its projection
to `W` is finite by [lem-trf-finite-radicial-basechange], and `W → T` is finite by
[lem-weil-pbc-closed-immersion-finite]. Their composite is finite by
[lem-weil-pbc-finite-composition]. This proves the conclusion for every scheme test,
without any radiciality assumption. -/
theorem finite_of_decent_of_finite_residueField {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hdecent : ∀ (K : Type u) [Field K] (b : Spec (CommRingCat.of K) ⟶ S)
      (c : yoneda.obj (Over.mk b) ⟶ X.obj.obj) (U : Over S), IsAffine U.left →
      ∀ t : yoneda.obj U ⟶ X.obj.obj,
        ∃ (V : Over S) (p : V ⟶ U) (q : yoneda.obj V ⟶ yoneda.obj (Over.mk b)),
          IsPullback q (yoneda.map p) c t ∧ CompactSpace V.left)
    (L : Type u) [Field L] (b : Spec (CommRingCat.of L) ⟶ S)
    (a : yoneda.obj (Over.mk b) ⟶ X.obj.obj)
    (hs : IsClosed ({b (IsLocalRing.closedPoint L)} : Set S))
    (hfinite : (S.descResidueField (Scheme.stalkClosedPointTo b)).hom.Finite) :
    IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) a := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
