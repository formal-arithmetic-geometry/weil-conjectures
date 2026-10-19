/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q88
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import WeilConjectures.ZetaSeries
import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete
import Sheaf.AlgebraicGeometry.ComplementaryPureSubcurveComponents
import Sheaf.TraceFormula.CurveNormalizationCompletion
import Sheaf.TraceFormula.ReducedSchemeImage
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.RegularLocalSeparableResidueSmooth
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Reduced closed subcurves of a split nodal curve

Source: Stacks Project, `curves.tex`, Tag 0E38 (1), (2)(a)--(c), specialized to
split nodes in the sense of Tags 0C4D and 0CBU
(blueprint: lem-trf-stacks-nodal-closed-subcurve).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A reduced closed pure subcurve of a split nodal curve is again split nodal.
Its intersection with the scheme-theoretic complementary closure is a finite disjoint
union of spectra of finite separable extensions of the ground field, consists of ambient
nonsmooth nodes, and lies in the smooth locus of the subcurve.

The complementary closure is the canonical scheme-theoretic image of the complementary
open immersion. The intersection is the scheme pullback of its inclusion and `i`.
Every completion isomorphism below respects the original `k`-structure: the displayed
scalar identity is exactly the condition of being a `k`-algebra isomorphism. The disjoint
union isomorphism likewise commutes with the maps to `Spec k` on every summand.

Source: Stacks Project, `curves.tex`, Tag 0E38 (1), (2)(a)--(c), with the split
completed-local-ring convention of Tags 0C4D and 0CBU
(blueprint: lem-trf-stacks-nodal-closed-subcurve).

Proof plan, following the nine steps of the node:
1. A field is Noetherian, so finite type makes X Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). Apply
   lem-trf-complementary-pure-subcurve-components: Y is a reduced union of components,
   and the complementary reduced closure is the union of the remaining components.
   The open complement is reduced, so lem-trf-reduced-scheme-image identifies this
   with the scheme-theoretic closure Z. No component generic point belongs to both
   unions. Every nonclosed point of a Noetherian dimension-one scheme is generic in
   a component, since otherwise a closed specialization gives a chain of length two.
   Thus every boundary point is closed. Sobriety makes every irreducible closed subset
   of the boundary a singleton, so its dimension is at most zero; it is Noetherian.
2. At a smooth closed ambient point, lem-weil-pbc-smooth-over-field-regular-local and
   lem-sc-regular-local-domain make the local ring a domain. Components through the point
   correspond to minimal primes of that local ring by
   lem-weil-pbc-spec-irreducible-components-minimal-primes and localization. Hence only
   one component passes through it; removing the other finitely many components makes
   X and Y coincide near the point. It is smooth on Y and outside the boundary.
3. At a nonsmooth closed point put A = O_X,x, F = kappa(x), and C = completion(A).
   The hypothesis identifies C with F[[u,v]]/(uv). Its primes are precisely (u), (v),
   and (u,v), since the one-variable quotients are local dimension-one domains by
   lem-weil-pbc-power-series-field-cohen-regular-complete.
   By lem-weil-pbc-local-completion-faithfully-flat every minimal prime of A lifts;
   lem-weil-pbc-local-completion-local-ring identifies the maximal ideal and its
   contraction. Thus A has at most two minimal primes and X at most two incident components.
4. If Y contains all incident components, remove the others: Y and X coincide near x,
   including their local k-algebras, residue fields and completions. Thus the node is
   preserved and x is outside Z. This also treats an irreducible self-node.
5. Otherwise two distinct components pass through x and exactly one belongs to Y.
   Their distinct minimal primes p1,p2 are nonzero. By
   lem-trf-curve-normalization-completion the completions of the reduced local
   dimension-one algebras A/pi are reduced and dimension one. By
   lem-weil-pbc-local-completion-quotient these are C/piC. The prime list and
   lem-weil-pbc-zero-locus-eq-iff-radical-eq leave only 0,(u),(v) for piC.
   Lem-weil-pbc-faithfully-flat-ideal-contraction excludes 0 and distinguishes the
   two extended primes. After exchanging u,v they are the two axis ideals, and the
   completed quotient maps are the actual axis projections.
6. The sum p1+p2 defines the intersection. Its extension is (u,v) = mC by
   lem-weil-pbc-local-completion-local-ring. Faithfully flat contraction gives
   p1+p2 = m. The boundary local ring is consequently F, with its original k-structure.
7. The completed local ring of Y at a boundary point is F[[u]], hence regular by the
   power-series theorem. Lem-weil-pbc-completion-regular-local descends regularity.
   Finite separable algebraic F/k is separable in the sense of
   def-weil-pbc-separable-field-extension: every intermediate field is separably
   generated using the empty transcendence basis. The finite-type affine criterion
   lem-weil-pbc-regular-local-separable-residue-smooth now makes Y smooth at the point.
8. These cases prove inheritance of the split nodal condition. Every boundary point
   is in the two-component case, so is a nonsmooth ambient node and is smooth on Y.
9. Lem-sc-zero-dim-noetherian-finite-discrete makes the boundary finite and discrete.
   Each open singleton is the spectrum of its local ring: an affine neighbourhood
   inside the singleton is the entire singleton, and localization changes nothing.
   Step 6 identifies this ring with its finite separable residue field over k.
   This gives the claimed finite disjoint union over k, including the empty union.
-/
theorem stacks_nodal_closed_subcurve
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    (hX : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = 1)
    (hnodal : ∀ x : X, IsClosed ({x} : Set X) →
      (¬ ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) →
      (f.residueFieldAlgebraMap x).Finite ∧
      @Algebra.IsSeparable k (X.residueField x) _ _
        (f.residueFieldAlgebraMap x).toAlgebra ∧
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) (X.residueField x) ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (X.residueField x)) *
              MvPowerSeries.X 1}),
        ∀ a : k,
          e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x)
            (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.Γgerm x).hom a)) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (f.residueFieldAlgebraMap x a)))
    (i : Y ⟶ X) [IsClosedImmersion i] [IsReduced Y]
    (hY : ∀ C ∈ irreducibleComponents Y, topologicalKrullDim C = 1) :
    (∀ y : Y, IsClosed ({y} : Set Y) →
      (¬ ∃ U : Y.Opens, y ∈ U ∧ Smooth (U.ι ≫ i ≫ f)) →
      ((i ≫ f).residueFieldAlgebraMap y).Finite ∧
      @Algebra.IsSeparable k (Y.residueField y) _ _
        ((i ≫ f).residueFieldAlgebraMap y).toAlgebra ∧
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y) ≃+*
          (MvPowerSeries (Fin 2) (Y.residueField y) ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (Y.residueField y)) *
              MvPowerSeries.X 1}),
        ∀ a : k,
          e (AdicCompletion.of (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
            (Y.presheaf.stalk y)
            (((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop ≫
              Y.presheaf.Γgerm y).hom a)) =
          Ideal.Quotient.mk _ (MvPowerSeries.C ((i ≫ f).residueFieldAlgebraMap y a))) ∧
    (∃ (n : ℕ) (K : Fin n → Type u) (_ : ∀ a, Field (K a)) (ι : ∀ a, k →+* K a),
      (∀ a, (ι a).Finite ∧ @Algebra.IsSeparable k (K a) _ _ (ι a).toAlgebra) ∧
      ∃ e : (∐ fun a : Fin n => Spec (.of (K a))) ≅
          pullback (C := Scheme.{u}) i
            (Scheme.openComplementOfIsClosedImmersion i).ι.imageι,
        ∀ a : Fin n,
          Sigma.ι (fun b : Fin n => Spec (.of (K b))) a ≫ e.hom ≫
            pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι ≫ i ≫ f =
          Spec.map (CommRingCat.ofHom (ι a))) ∧
    (∀ t : pullback (C := Scheme.{u}) i
        (Scheme.openComplementOfIsClosedImmersion i).ι.imageι,
      ¬(∃ U : X.Opens,
        i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t) ∈ U ∧
          Smooth (U.ι ≫ f)) ∧
      (∃ e : AdicCompletion
          (IsLocalRing.maximalIdeal (X.presheaf.stalk
            (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t))))
          (X.presheaf.stalk
            (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t))) ≃+*
          (MvPowerSeries (Fin 2) (X.residueField
            (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t))) ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (X.residueField
              (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t)))) *
                MvPowerSeries.X 1}),
        ∀ a : k,
          e (AdicCompletion.of
            (IsLocalRing.maximalIdeal (X.presheaf.stalk
              (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t))))
            (X.presheaf.stalk
              (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t)))
            (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.Γgerm
              (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t))).hom
                a)) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (f.residueFieldAlgebraMap
            (i (pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t)) a))) ∧
      ∃ U : Y.Opens,
        pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t ∈ U ∧
          Smooth (U.ι ≫ i ≫ f)) := by
  sorry

end AlgebraicGeometry
