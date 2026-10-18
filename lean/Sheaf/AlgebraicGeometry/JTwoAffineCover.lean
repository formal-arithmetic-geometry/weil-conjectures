/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.RingTheory.ExcellentRing
import Sheaf.AlgebraicGeometry.IsRegularScheme

/-! # The J-2 property on affine opens

Source: Stacks Project, Morphisms, Lemma 29.15.4 (Tag 07R4), implication (4) implies (3)
(blueprint: lem-trf-j2-affine-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open AlgebraicGeometry

namespace AlgebraicGeometry

/-- For a locally Noetherian scheme, the J-2 property of the coordinate rings on an
affine open cover implies the J-2 property on every affine open.

Source: Stacks Project, Morphisms, Lemma 29.15.4 (Tag 07R4), implication (4) implies (3)
(blueprint: lem-trf-j2-affine-cover).

Proof (following Tag 07R4 and the five proof steps of the node):
1. For an affine open `V` and a finite type algebra `R → B` with `R = Γ(X,V)`,
   the affine morphism `Spec B → V` is locally of finite type by
   `lem-weil-pbc-lft-pointwise-criterion`; this also includes the zero algebra.
2. The open immersion `V ⟶ X` is an immersion and hence locally of finite type by
   `lem-weil-pbc-immersion-base-change-lft`; composing with the previous morphism and
   using `lem-weil-pbc-proper-fp-permanence` gives a locally finite type map to `X`.
   Since `X` is locally Noetherian, `pqf-lem-locnoeth-lft` makes its affine source
   locally Noetherian, and `def-weil-regular-scheme` supplies the regular-local predicate.
3. The inverse images of the cover `U i` cover the source. By
   `lem-weil-pbc-affine-opens-basis`, refine each by an affine `W_y`, and apply
   `lem-weil-pbc-lft-affine-pairs` to obtain a finite type map
   `Γ(X,U i) → Γ(Y,W_y)`.
4. The J-2 hypothesis `hJ i` makes the regular locus of each `Γ(Y,W_y)` open;
   `lem-weil-pbc-affine-open-stalk-localization` identifies it with the regular locus
   of the source on `W_y`. These opens glue to the open regular locus of the source,
   including the empty source.
5. Applying the same stalk-localization identification to the whole affine source
   `Spec B` shows that its regular locus is open. Since `V` and `B` were arbitrary,
   this is exactly the J-2 predicate for every affine coordinate ring.
-/
theorem j2_of_affine_open_cover
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (I : Type v) (U : I → X.affineOpens)
    (hU : ⨆ i : I, (U i : X.Opens) = ⊤)
    (hJ : ∀ i : I, ∀ (A : Type u) [CommRing A]
      [Algebra Γ(X, U i) A] [Algebra.FiniteType Γ(X, U i) A],
      IsOpen {p : PrimeSpectrum A |
        IsRegularLocalRing (Localization.AtPrime p.asIdeal)}) :
    ∀ V : X.affineOpens, ∀ (A : Type u) [CommRing A]
      [Algebra Γ(X, V) A] [Algebra.FiniteType Γ(X, V) A],
      IsOpen {p : PrimeSpectrum A |
        IsRegularLocalRing (Localization.AtPrime p.asIdeal)} := by
  sorry

end AlgebraicGeometry
