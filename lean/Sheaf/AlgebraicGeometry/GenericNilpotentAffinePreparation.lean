/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso
import WeilConjectures.AlgebraicGeometry.AffineChartBaseChangeIso
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Affine nilpotent preparation over the reduced integral base

Source: Stacks Project, More on Morphisms, Tag 0575,
`lemma-nonreduced-in-neighbourhood`, proof through the second shrinking
(blueprint: lem-trf-generic-nilpotent-affine-preparation).

Affine opens are specified by open immersions from spectra. The principal-localization
clause specifies its affine fibre product by `IsPullback`, retaining both structure maps,
including for the empty principal open at zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A nonreduced generic fibre supplies a nilpotent affine section which stays nonzero
in the fraction-field base change, after passing to the reduced base and shrinking.

Source: Stacks Project, More on Morphisms, Tag 0575,
`lemma-nonreduced-in-neighbourhood`, first proof paragraph and its two shrinkings
(blueprint: lem-trf-generic-nilpotent-affine-preparation).

Proof:
1. The reduction is reduced and universally homeomorphic to the original base by
   lem-weil-pbc-reduction-universal-homeomorphism. Transport the generic point and
   irreducibility; reducedness then gives integrality (def-pc-integral-scheme).
   Finite type survives base change by lem-sfb-finite-type-composition-base-change.
2. Reduction induces residue-field isomorphisms by
   lem-weil-pbc-closed-immersion-residue-field-iso. The cartesian comparison of
   lem-weil-pbc-fibre-of-base-change therefore gives the canonical fibre isomorphism,
   characterized by its projections (def-pc-fibre-product). In particular the new
   generic fibre remains nonreduced.
3. Choose an affine neighbourhood Spec A0 of the new generic point using
   lem-weil-pbc-affine-opens-basis. Its ring is a domain, with generic stalk its fraction
   field K, by lem-weil-pbc-spec-domain-stalks-function-field and def-weil-residue-field.
4. Choose a nonreduced local ring in the generic fibre and an affine neighbourhood
   Spec B0 of its image. Its A0-algebra is finite type by lem-weil-pbc-lft-affine-pairs.
   By lem-weil-pbc-affine-chart-base-change-iso the generic chart has ring B0 tensor K.
   If it were reduced, its local ring would be reduced by
   lem-weil-pbc-affine-open-stalk-localization and
   lem-weil-pbc-localization-preserves-reduced. Thus it has a nonzero nilpotent h,
   with h^n = 0 for n at least one. Tensor symmetry gives the indicated factor order.
5. By lem-weil-pbc-localization-base-change write h = c/s, s nonzero. The localization
   zero criterion supplies u nonzero with u*c^n = 0. Shrink to D(s*u) using
   lem-weil-pbc-affine-open-section-vanishing-prime. By lem-weil-pbc-open-fibre-product,
   lem-weil-pbc-fibre-product-affine-spectra and localization base change, the source
   chart has ring B = (B0)_(s*u), over A = (A0)_(s*u), compatibly with both maps.
6. Both s and u are now units, so b = c/s satisfies b^n = 0. The universal property
   lem-weil-pbc-ring-localization-universal-property identifies the new fraction field
   and generic tensor ring with the old ones; b tensor 1 is h, hence nonzero. The
   nonempty affine base has domain ring, and the images of generators of B0 generate
   B over A, proving finite type.
7. For every a, lem-weil-pbc-affine-open-section-vanishing-prime identifies D(a) with
   Spec A_a. Open fibre products (lem-weil-pbc-open-fibre-product), the affine formula
   (lem-weil-pbc-fibre-product-affine-spectra), and lem-weil-pbc-localization-base-change
   identify its source chart with Spec B_a. These maps give the displayed cartesian
   square and commute with the maps to the original source, including when a = 0. -/
theorem exists_generic_nilpotent_affine_preparation
    {X T : Scheme.{u}} (f : X ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f]
    [IrreducibleSpace T] (ξ : T) (hξ : IsGenericPoint ξ (Set.univ : Set T))
    (hgeneric : ¬ IsReduced (f.fiber ξ)) :
    IsIntegral T.nilradical.subscheme ∧
    IsHomeomorph T.nilradical.subschemeι ∧
    LocallyOfFiniteType (pullback.snd f T.nilradical.subschemeι) ∧
    QuasiCompact (pullback.snd f T.nilradical.subschemeι) ∧
    (∀ t' : T.nilradical.subscheme,
      IsIso (T.nilradical.subschemeι.residueFieldMap t') ∧
      ∃ e : (pullback.snd f T.nilradical.subschemeι).fiber t' ≅
          f.fiber (T.nilradical.subschemeι t'),
        e.hom ≫ f.fiberι (T.nilradical.subschemeι t') =
          (pullback.snd f T.nilradical.subschemeι).fiberι t' ≫
            pullback.fst f T.nilradical.subschemeι ∧
        e.hom ≫ f.fiberToSpecResidueField (T.nilradical.subschemeι t') =
          (pullback.snd f T.nilradical.subschemeι).fiberToSpecResidueField t' ≫
            Spec.map (T.nilradical.subschemeι.residueFieldMap t')) ∧
    ∃ ξ' : T.nilradical.subscheme,
      IsGenericPoint ξ' (Set.univ : Set T.nilradical.subscheme) ∧
      T.nilradical.subschemeι ξ' = ξ ∧
      ∃ (A : CommRingCat.{u}) (B K : CommAlgCat.{u} A),
        IsDomain A ∧ IsFractionRing A K ∧
        ∃ (eK : CommRingCat.of K ≅ T.nilradical.subscheme.residueField ξ')
          (j : Spec A ⟶ T.nilradical.subscheme)
          (k : Spec (.of B) ⟶ pullback (pullback.snd f T.nilradical.subschemeι) j),
          IsOpenImmersion j ∧ ξ' ∈ Set.range j ∧ IsOpenImmersion k ∧
          k ≫ pullback.snd (pullback.snd f T.nilradical.subschemeι) j =
            Spec.map (CommRingCat.ofHom (algebraMap A B)) ∧
          Spec.map eK.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ j =
            T.nilradical.subscheme.fromSpecResidueField ξ' ∧
          (algebraMap A B).FiniteType ∧
          (∃ (b : B) (n : ℕ), 1 ≤ n ∧ b ^ n = 0 ∧ b ⊗ₜ[A] (1 : K) ≠ 0) ∧
          ∀ a : A,
            Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a)))) =
              (↑(PrimeSpectrum.basicOpen a) : Set (PrimeSpectrum A)) ∧
            ∃ ka : Spec (.of (Localization.Away (algebraMap A B a))) ⟶
                pullback (pullback.snd f T.nilradical.subschemeι)
                  (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ j),
              IsOpenImmersion ka ∧
              IsPullback
                (Spec.map (CommRingCat.ofHom
                  (algebraMap B (Localization.Away (algebraMap A B a)))))
                (ka ≫ pullback.snd (pullback.snd f T.nilradical.subschemeι)
                  (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ j))
                (Spec.map (CommRingCat.ofHom (algebraMap A B)))
                (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a)))) ∧
              ka ≫ pullback.fst (pullback.snd f T.nilradical.subschemeι)
                  (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ j) =
                Spec.map (CommRingCat.ofHom
                    (algebraMap B (Localization.Away (algebraMap A B a)))) ≫
                  k ≫ pullback.fst (pullback.snd f T.nilradical.subschemeι) j := by
  sorry

end AlgebraicGeometry
