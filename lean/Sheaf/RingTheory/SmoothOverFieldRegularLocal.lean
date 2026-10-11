module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Smooth algebras over fields have regular local rings

Source: Stacks Project, Algebra, Lemma Tag 00TT (blueprint:
lem-weil-pbc-smooth-over-field-regular-local).
-/

@[expose] public section

universe u v

namespace Algebra

/-- If `A` is a smooth algebra over a field, every localization at a prime ideal
is a regular local ring (blueprint: lem-weil-pbc-smooth-over-field-regular-local).

Source: Stacks Project, Algebra, Lemma Tag 00TT, final assertion.
Proof (the eight steps of the node):
1. Smoothness gives finite presentation, hence finite type, and smoothness at `q`.
   By `lem-weil-pbc-smooth-over-field-dimension-differentials`, the dimension of
   the fibre of the differentials at `q` equals the dimension at that point.
2. Choose an algebraic closure `K` of the residue field of `q`, and set
   `A_K = K ⊗[k] A`, using `lem-weil-pbc-algebra-tensor-pushout-universal-property`.
   The images of finite algebra generators of `A` generate `A_K` over `K`.
3. The map sending `λ ⊗ a` to `λ` times the residue of `a` in `K` is surjective.
   Its kernel `m` is maximal, has residue field `K`, and contracts to `q`.
4. By `lem-weil-pbc-dimension-at-point-field-extension` and
   `lem-weil-pbc-closed-point-dimension-local-ring`, the dimension at `q` equals
   the Krull dimension of `R = (A_K)_m`; interchange tensor factors as needed.
5. By `lem-weil-pbc-kahler-differentials-base-change`, the differential fibre
   at `m` is the extension to `K` of that at `q`. Extending a basis preserves
   its dimension, so this dimension equals the Krull dimension of `R`.
6. Finite type over a field and localization make `R` Noetherian and local
   (`lem-weil-pbc-finite-type-algebra-noetherian`,
   `lem-weil-pbc-localization-noetherian`). The Jacobi-Zariski sequence
   (`lem-weil-pbc-jacobi-zariski-differential-maps`) makes the conormal map from
   `n/n²` onto the differential fibre surjective, since the residue field is `K`.
   The quotient `R/n² → K` has a section induced by its `K`-algebra structure.
   By `lem-weil-pbc-square-zero-section-conormal-retraction`, its conormal map
   is injective. The conormal map for `R` maps to this map, hence is injective
   as well. Thus the cotangent space is isomorphic to the differential fibre.
7. By `lem-weil-pbc-kahler-differentials-localization`, this fibre agrees with
   the differential fibre in step 5. Therefore the cotangent dimension equals
   the Krull dimension. Apply `lem-weil-pbc-regular-local-cotangent-dimension`
   to conclude that `R` is regular local.
8. By `lem-weil-pbc-field-extension-base-change-faithfully-flat` and
   `lem-weil-pbc-flat-local-ring-maps`, the map `A_q → R` is flat and local.
   Both rings are Noetherian. Descend regularity using
   `lem-weil-pbc-flat-under-regular`. Since `q` was arbitrary, the result follows.
-/
theorem smooth_over_field_regular_local
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [Algebra.Smooth k A] (q : Ideal A) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  sorry

end Algebra
