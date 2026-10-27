/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q157
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.NodalDualizingDatum
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import Sheaf.AlgebraicGeometry.NodalCurveLCICriterion
import Sheaf.TraceFormula.LciAffineOpenLocality
import Sheaf.RingTheory.LocalCompleteIntersectionFieldChange
import Sheaf.TraceFormula.LciPointwiseCriterion
import Sheaf.TraceFormula.SyntomicPointwiseLocalModel
import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersectionPresentation
import WeilConjectures.RingTheory.RelativeGlobalCompleteIntersectionLocalRegularSequence
import Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Regular affine presentations of nodal families

Source: Stacks Project, Algebra, Tags 00SY, 00SV, 061L, 08JZ; Curves, Tag 0C4E;
Morphisms, Tag 01UE (blueprint: lem-sfb-nodal-family-regular-affine-presentations).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Nodal geometric fibres give ordinary LCI curve fibres and regular affine curve charts.
The completion isomorphism fixes the geometric field via the displayed coefficient equation.
Source: Stacks Project, Algebra, Tags 00SY, 00SV, 061L, 08JZ; Curves, Tag 0C4E
(blueprint: lem-sfb-nodal-family-regular-affine-presentations).

Proof plan:
1. Base change preserves local finite presentation (qcqs-morphism-permanence).
   On affine pairs, lfp-affine-opens-finite-presentation gives finitely presented, hence
   finite type algebras; lft-affine-pairs gives locally finite type fibre morphisms.
2. Apply nodal-curve-lci-criterion, Tag 0C4E, to each geometric fibre: its closed
   nonsmooth points have precisely the nodal completions, so it is LCI over its field.
3. Geometric-pure-fibre-point-dimension and field-extension-component-local-dimension
   descend pure dimension one to ordinary fibres and their nonempty open subschemes.
4. Open-preimage-fibre-product and fibre-product-affine-spectra identify affine fibre
   charts with tensor-product spectra. Lci-affine-open-locality makes their geometric
   coordinate rings LCI. Lci-field-change descends this to the ordinary fibre rings.
   Affine-opens-basis gives the cover; lci-pointwise-criterion gives CI fibre stalks.
5. At x over the prescribed V, flatness and the pointwise CI fibre criterion give a
   syntomic-pointwise-local-model B=P/(a_1,...,a_r), a relative global CI presentation.
   Its nonempty fibre is an affine open of a pure curve, so n-r=1, hence n=r+1.
6. Relative-global-complete-intersection-local-regular-sequence gives regularity at
   the prime over x. The affine-open-locnoeth and finite-type-algebra-noetherian lemmas
   make P Noetherian. Regular-sequence-principal-neighbourhood supplies h outside
   that prime with regular equations in P_h. Principal-localization-open-immersion
   gives the corresponding affine neighbourhood of x.
7. In P[y], hy-1 is a nonzerodivisor: coefficient comparison first gives b_0=0 and
   then b_i=h*b_(i-1)=0. Localization-away-polynomial-quotient identifies its quotient
   with P_h. Place hy-1 first, then the a_i: regularity follows from regular-sequence.
   The final quotient is nonzero since it contains x. With c=r+1, it has c+1 variables
   and c equations. All maps fix the prescribed base ring. Repeating for each x
   gives the claimed cover over every V, without connectedness or properness.
-/
theorem nodal_family_regular_affine_presentations
    {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [Flat f] [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hgeom : ∀ s : S,
      Nonempty (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s)) ∧
      IsReduced (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s)) ∧
      (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s)).IsPureDimension 1 ∧
      ∀ x : (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s)),
        x ∈ closedPoints (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s)) →
        x ∉ ((pullback.snd f (Spec.map (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s)).smoothLocus : Set (pullback (C := Scheme.{u}) f (Spec.map
              (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s))) →
        ∃ e : AdicCompletion (IsLocalRing.maximalIdeal ((pullback (C := Scheme.{u}) f (Spec.map
          (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s)).presheaf.stalk x)) ((pullback (C := Scheme.{u}) f (Spec.map
              (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s)).presheaf.stalk x) ≃+* (MvPowerSeries (Fin 2)
              (AlgebraicClosure (S.residueField s)) ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AlgebraicClosure (S.residueField
              s))) *
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (AlgebraicClosure (S.residueField s)))}),
          ∀ a : (AlgebraicClosure (S.residueField s)),
            e (AdicCompletion.of (IsLocalRing.maximalIdeal ((pullback (C := Scheme.{u}) f (Spec.map
              (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s)).presheaf.stalk x)) ((pullback (C := Scheme.{u}) f (Spec.map
              (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s)).presheaf.stalk x) (((Scheme.ΓSpecIso (.of (AlgebraicClosure
              (S.residueField s)))).inv ≫
            (pullback.snd f (Spec.map (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s)).appLE ⊤ ⊤ le_top ≫
            (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom
              (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s)).presheaf.germ ⊤ x trivial).hom a)) =
              Ideal.Quotient.mk _ (MvPowerSeries.C a)) :
    (∀ s : S, (f.fiber s).IsPureDimension 1 ∧
      ∀ x : f.fiber s, ∃ U : (f.fiber s).affineOpens, x ∈ U.1 ∧
        ∃ ft : @Algebra.FiniteType (S.residueField s) Γ(f.fiber s, U.1) _ _
          (((Scheme.ΓSpecIso (.of (S.residueField s))).inv ≫
            (f.fiberToSpecResidueField s).appLE ⊤ U.1 le_top).hom.toAlgebra),
          @Algebra.IsLocalCompleteIntersection (S.residueField s) Γ(f.fiber s, U.1) _ _
            (((Scheme.ΓSpecIso (.of (S.residueField s))).inv ≫
              (f.fiberToSpecResidueField s).appLE ⊤ U.1 le_top).hom.toAlgebra) ft) ∧
    (∀ (V : S.affineOpens) (x : X), f x ∈ V.1 →
      ∃ A : NodalCanonicalPresentation f, A.V = V ∧ x ∈ A.U.1) := by
  sorry

end AlgebraicGeometry
