/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q121
-/
module

public import Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension
import Sheaf.AlgebraicGeometry.UnramifiedOverFieldLocalCriterion
import Sheaf.RingTheory.SmoothLocalCompleteIntersection
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.DthFittingSmoothLocus
import Sheaf.AlgebraicGeometry.NodalPointLocalCriterion

/-! # Nodal curves and the first-Fitting singular subscheme

Source: Stacks Project, Curves, Tag 0C4E (blueprint: lem-trf-nodal-curve-lci-criterion).

## Main statements

* `nodal_curve_lci_criterion`: closed points are smooth or nodal exactly when the
  curve is locally a complete intersection and its first-Fitting singular subscheme is
  unramified.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Source: Stacks Project, Curves, Tag 0C4E (blueprint: lem-trf-nodal-curve-lci-criterion).

Proof plan:
1. Apply `lem-trf-dth-fitting-smooth-locus` in relative dimension one. Flatness holds over
   a field; `pqf-lem-lft-fp-locnoeth` gives local finite presentation. Apply
   `lem-trf-flat-dense-generic-fibre-pure-dimension` over `Spec k`, whose generic fibre is
   the whole curve, to get pure dimension one for every nonempty geometric fibre. Thus
   the support of the first-Fitting subscheme is the nonsmooth locus. For any point z of
   that subscheme, `lem-sc-lft-over-field-jacobson-space` gives a closed specialization x
   still in the subscheme.
2. Assume the closed points are smooth or nodes. The chosen singular closed specialization
   is nodal. By `lem-trf-nodal-point-local-criterion` it has an affine LCI neighbourhood,
   finite separable residue field, and singular-subscheme stalk equal to that field. The
   primes in this field force z = x. Thus all singular points are closed and satisfy the
   pointwise criterion. Smooth points have LCI neighbourhoods by
   `lem-weil-pbc-smooth-over-field-local-complete-intersection`; these neighbourhoods cover
   C. The singular subscheme is locally of finite type, since its affine coordinate rings
   are quotients of finite-type k-algebras. Its field stalks and finite separable residue
   fields give unramifiedness by `lem-trf-unramified-over-field-local-criterion`.
3. Conversely, apply `lem-trf-unramified-over-field-local-criterion` to the singular
   subscheme. Every point in it is closed, with field stalk and finite separable residue
   field. The assumed LCI cover supplies the affine LCI neighbourhood. Apply the converse
   of `lem-trf-nodal-point-local-criterion` to obtain a node. All other closed points are
   smooth by the first-Fitting smooth-locus identification from step 1.
-/
theorem nodal_curve_lci_criterion
    (k : Type u) [Field k] (C : Scheme.{u})
    (f : C ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hC : C.IsPureDimension 1) :
    (∀ x : C, x ∈ closedPoints C → (x ∈ (f.smoothLocus : Set C) ∨
      ∃ xbar : (pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))),
        pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) xbar = x ∧
        Nonempty
          (AdicCompletion
              (IsLocalRing.maximalIdeal
                ((pullback (C := Scheme.{u}) f
                  (Spec.map (CommRingCat.ofHom
                    (algebraMap k (AlgebraicClosure k))))).presheaf.stalk xbar))
              ((pullback (C := Scheme.{u}) f
                (Spec.map (CommRingCat.ofHom
                  (algebraMap k (AlgebraicClosure k))))).presheaf.stalk xbar) ≃+*
            (MvPowerSeries (Fin 2) (AlgebraicClosure k) ⧸
              Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AlgebraicClosure k)) *
                (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (AlgebraicClosure k))})))) ↔
      ((∀ x : C, ∃ U : C.affineOpens, x ∈ U.1 ∧
          ∃ (ft : @Algebra.FiniteType k Γ(C, U.1) _ _ ((f.appLE ⊤ U.1 (by simp)).hom.comp
                (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra),
            @Algebra.IsLocalCompleteIntersection k Γ(C, U.1) _ _
              ((f.appLE ⊤ U.1 (by simp)).hom.comp
                (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra ft) ∧
        (LocallyOfFiniteType (Scheme.firstFittingSingularSubscheme f ≫ f) ∧
          IsOpenImmersion
            (pullback.diagonal (Scheme.firstFittingSingularSubscheme f ≫ f)))) := by
  sorry

end AlgebraicGeometry
