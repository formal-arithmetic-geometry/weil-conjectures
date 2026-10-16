/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.FieldTheory.SeparableExtension
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.RingTheory.ReducedNoetherianTotalRingFractions
import Mathlib.RingTheory.Localization.Integral
import Sheaf.RingTheory.IntegralClosureFiniteNormalProduct
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.FieldTheory.SeparablyGenerated
import Sheaf.RingTheory.NormalAlgebraSeparableScalarExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# Geometry and separable field change of reduced algebraic normalization

Source: Stacks Project, Varieties, Tags 0BXR and 0C3N; Morphisms, Tags 035Q, 035K, 0CDV
(blueprint: lem-weil-pbc-reduced-algebraic-normalization-field-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Componentwise normalization is finite, surjective, an isomorphism over the dense open
normal locus, compatible with restriction to opens, and compatible with separable field change.
The comparison is characterized over the base by its projection equations.
Source: Stacks Project, Varieties, Tags 0BXR and 0C3N; Morphisms, Tags 035Q, 035K, 0CDV
(blueprint: lem-weil-pbc-reduced-algebraic-normalization-field-change).

Proof:
1. Finite type over a field makes X Noetherian
(`lem-weil-pbc-finite-type-over-noetherian`), hence its components are finite in number
(`lem-weil-pbc-noetherian-finitely-many-components`). Normalize their reduced structures
using `lem-sc-normalization-exists`. Each resulting map is finite and surjective, as is
its finite disjoint union. On affine charts the coordinate ring is the finite product of
the integral closures of the component domains. This includes the empty coproduct.
2. By `lem-weil-pbc-reduced-noetherian-total-ring-fractions` the total fraction ring is the
product of the component fields. Projection of monic equations and multiplication of
finitely many lifted monic equations identify the preceding product with the integral
closure in this total fraction ring. Localization compatibility is
`lem-weil-pbc-integral-closure-commutes-localization`.
3. The integral closure is normal by `lem-sbc-integral-closure-finite-normal-product`.
Clear the denominators of its finite module generators by a common nonzerodivisor s.
Then A_s = B_s. By `lem-weil-pbc-reduced-zerodivisors-union-minimal-primes`, D(s) contains
all generic points and is dense.
4. Localization compatibility and `lem-weil-pbc-primes-of-localization` show that A_p is a
normal domain exactly when (B/A)_p = 0. The support of the finite module B/A is closed:
the product of elements killing its finitely many generators kills the whole module.
The complementary open is therefore precisely the normal locus, contains D(s), and the
normalization restricts to an isomorphism there.
5. On principal opens, localization gives the normalization of the restricted scheme;
use `lem-weil-pbc-affine-open-section-vanishing-prime` for the affine charts. These
identifications preserve fractions on further restrictions and hence glue over every W.
They are canonical because two maps over W agree on the dense isomorphism locus and
the target is separated over W.
6. For separable K/k, `lem-weil-pbc-normal-algebra-separable-scalar-extension` makes B_K
normal. Flatness (`lem-weil-pbc-module-over-field-flat`, `def-weil-pbc-flat-ring-map`)
preserves A → B and multiplication by s as injections. Thus A_K is reduced, B_K is
finite over A_K, and s B_K lies in A_K. Both rings are Noetherian.
7. These inclusions identify their total fraction rings: a fraction b/t in Q(B_K) is
(sb)/(st) in Q(A_K). Apply `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions`
and `lem-weil-pbc-noetherian-finitely-many-minimal-primes` to B_K. Its normality and
`lem-weil-pbc-finite-algebra-is-integral` identify B_K with the integral closure of A_K.
The comparison sends b tensor c to c times the image of b in Q(A_K). This formula
commutes with localization, so glues over X_K. Uniqueness over X_K follows on the dense
isomorphism locus, since the target is separated over X_K and the source is reduced.
8. For algebraically closed k, `lem-weil-pbc-algclosed-fg-field-separating-basis` makes
every finitely generated intermediate extension separably generated, exactly
`Algebra.IsSeparableExtension k K`. Apply the preceding comparison, without algebraicity
or finiteness assumptions on K/k. -/
theorem reduced_algebraic_normalization_field_change
    {k : Type u} [Field k] (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [IsReduced X] [LocallyOfFiniteType q] [QuasiCompact q] :
    IsFinite X.fromReducedNormalization ∧ Surjective X.fromReducedNormalization ∧
    (∃ N : X.Opens,
      (∀ x : X, x ∈ N ↔
        IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) ∧
      Dense (N : Set X) ∧ IsIso (X.fromReducedNormalization ∣_ N)) ∧
    (∀ W : X.Opens,
      ∃! e : W.toScheme.reducedNormalization ≅
          (X.fromReducedNormalization ⁻¹ᵁ W).toScheme,
        e.hom ≫ (X.fromReducedNormalization ∣_ W) = W.toScheme.fromReducedNormalization) ∧
    (∀ (K : Type u) [Field K] [Algebra k K], Algebra.IsSeparableExtension k K →
      ∃! e : (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reducedNormalization ≅
          pullback (X.fromReducedNormalization ≫ q)
            (Spec.map (CommRingCat.ofHom (algebraMap k K))),
        (e.hom ≫ pullback.fst _ _ ≫ X.fromReducedNormalization =
          (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ≫
            pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        (e.hom ≫ pullback.snd _ _ =
          (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ≫
            pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k K))))) ∧
    (IsAlgClosed k → ∀ (K : Type u) [Field K] [Algebra k K],
      ∃! e : (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reducedNormalization ≅
          pullback (X.fromReducedNormalization ≫ q)
            (Spec.map (CommRingCat.ofHom (algebraMap k K))),
        (e.hom ≫ pullback.fst _ _ ≫ X.fromReducedNormalization =
          (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ≫
            pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        (e.hom ≫ pullback.snd _ _ =
          (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))).fromReducedNormalization ≫
            pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k K))))) := by
  sorry

end AlgebraicGeometry
