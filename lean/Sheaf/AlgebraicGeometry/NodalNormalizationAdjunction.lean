/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.TraceFormula.CurveNormalizationCompletion
import Sheaf.AlgebraicGeometry.DthFittingSmoothLocus
import Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension
import Sheaf.AlgebraicGeometry.NodalCurveLCICriterion
import Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition
import Sheaf.RingTheory.CompletionFiniteExtension
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.CompletionRegularLocal
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.RingTheory.GlobalCompleteIntersectionLocalRegularSequence
import Mathlib.RingTheory.Localization.Integral
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.PowerSeriesNormalDomain
import Sheaf.RingTheory.ReducedNoetherianTotalRingFractions
import WeilConjectures.RingTheory.RegularLocalSeparableResidueSmooth
import Sheaf.AlgebraicGeometry.FormalPlaneAdjunctionLattice

/-! # Normalization adjunction on a component of a nodal curve

Source: Temkin, Stable Modification, §1.2(b), pp. 2–3; Stacks Project, Curves,
Tags 0C4D and 0C4E, lemmas split-node and closed-subscheme-nodal-curve
(blueprint: lem-trf-nodal-normalization-adjunction).

## Main declarations

* `IsNodalNormalizationAdjunctionComparison`: the smooth-locus normalization of the
  adjunction isomorphism, specified on universal differentials and the divisor unit.
* `nodal_normalization_adjunction`: component normalization, branch counts, and adjunction.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- The adjunction comparison agrees with the prescribed smooth-locus identification.
The section of `O(B)` is the inclusion `I_B → O` under the internal-Hom equivalence;
thus it is the canonical divisor section, not a choice of trivialization. On every
ambient smooth open, a section corresponding to `da` is carried to `d(a ∘ r) ⊗ 1`.
Exterior degree one is retained on the ambient side to use the normalized adjunction
interface verbatim. These local generators determine the comparison uniquely.
Source: Temkin §1.2(b), normalization and residues; Stacks, Duality, fundamental-class-lci
(blueprint: lem-trf-nodal-normalization-adjunction). -/
def IsNodalNormalizationAdjunctionComparison
    {k : Type u} [Field k] {C N : Scheme.{u}} (p : C ⟶ Spec (.of k))
    (F : FlatLCIAdjunctionSystem p 1) (r : N ⟶ C) (B : N.IdealSheafData)
    (e : (Scheme.Modules.tensorPullback r).obj (F.line (FlatLCIBaseChange.identity p)) ≅
      (r ≫ p).relativeDifferentials ⊗ Scheme.Modules.dual B.toModules) : Prop :=
  ∀ (U : C.Opens), Smooth (U.ι ≫ p) →
    ∀ eU : (Scheme.Modules.tensorPullback U.ι).obj
        (F.line (FlatLCIBaseChange.identity p)) ≅
          Scheme.Modules.exteriorSheaf (U.ι ≫ p).relativeDifferentials 1,
      F.IsSmoothComparison (FlatLCIBaseChange.identity p) U eU →
      ∀ (a : Γ(C, U)) (m : Γ(F.line (FlatLCIBaseChange.identity p), U)),
        eU.hom.app (U.ι ⁻¹ᵁ U)
            (Scheme.Modules.tensorPullbackSection U.ι
              (F.line (FlatLCIBaseChange.identity p)) U m) =
          Scheme.Modules.exteriorSheafSection (U.ι ≫ p).relativeDifferentials 1
            (U.ι ⁻¹ᵁ U) (fun _ ↦ (U.ι ≫ p).relativeDifferentialsDerivation.d
              (X := op (U.ι ⁻¹ᵁ U)) (U.ι.app U a)) →
        e.hom.app (r ⁻¹ᵁ U)
            (Scheme.Modules.tensorPullbackSection r
              (F.line (FlatLCIBaseChange.identity p)) U m) =
          Scheme.Modules.tmulSection (X := N)
            (M := (r ≫ p).relativeDifferentials) (N := Scheme.Modules.dual B.toModules)
            (U := r ⁻¹ᵁ U)
            ((r ≫ p).relativeDifferentialsDerivation.d (X := op (r ⁻¹ᵁ U)) (r.app U a))
            (((SheafOfModules.homObjSectionsEquiv B.toModules
              (SheafOfModules.unit N.ringCatSheaf)).symm B.toModulesι).1 (op (r ⁻¹ᵁ U)))

open Classical in
/-- Normalization adjunction for every proper reduced irreducible component of a
finite-type nodal curve. An integral closed immersion whose image is a component is
exactly its reduced closed subscheme structure. The branch assertion is also stated
for nonproper components, so the one-or-two component classification accounts for
both branches of every ambient node. The reduced ideal `B` has exactly the inverse
image of the ambient singular locus as support, including smooth intersection points
of the component. The unique normalized isomorphism expresses canonicity.

Source: Temkin, Stable Modification, §1.2(b), pp. 2–3; Stacks Project, Curves,
Tag 0C4D, split-node and closed-subscheme-nodal-curve
(blueprint: lem-trf-nodal-normalization-adjunction).

Proof plan, following all eleven steps of the DAG:
1. Finite type gives Noetherianity. Faithful flatness of completion makes each nodal
   local ring reduced; smooth local rings are normal. A reduced component is integral.
   Normalization properties give finiteness, properness, dimension one and smoothness
   over the perfect field. Integrality gives nonempty connectedness.
2. The nodal LCI criterion supplies regular presentations. Flatness over the field,
   local finite presentation, quasi-compactness and quasi-separatedness, and purity
   of geometric fibres permit flat-lci-canonical-adjunction in dimension one.
3. The first Fitting singular subscheme is unramified over the field and quasi-compact;
   unramified-field-fibre-decomposition makes its support a finite set of closed nodes.
4. The complete node is the equal-constant-term subring of k[[u]] × k[[v]]. Adjoining
   the integral idempotent (1,0) gives its normalization. Each power-series factor is
   normal and has residue field k.
5. The total fraction ring of a reduced Noetherian curve ring is the product of the
   component fraction fields. Integral closure is componentwise: use projections of
   monic equations in one direction and their product in the other. Localization of
   integral closure identifies this description with scheme normalization.
6. Curve-normalization-completion and completion-finite-extension give two points over
   a node. Completion-finite-module-tensor identifies each completed component quotient:
   it contains one branch or both. Faithful flatness separates distinct component ideals.
   Thus one component uses both branches, or two components use one branch each.
7. At an intersection with another component the component completion is k[[t]], hence
   the component is regular and smooth. At a self-node it is k[[u,v]]/(uv), hence singular.
   Normalization is an isomorphism over every smooth point of the component.
8. The finite set of inverse images of ambient nodes consists of reduced closed points
   on a smooth curve. Point-cartier makes their sum an effective Cartier divisor B.
   Off B, the normalized adjunction and the divisor unit specify a rational comparison.
9. Formal-plane-adjunction-lattice computes its image on the two completed branches:
   du/u and -dv/v, respectively. These are continuous formal differentials.
10. The divisor ideal at a branch point is the uniformizer ideal. Its dual is the
    inverse lattice, so both completed line lattices are k[[t]] dt/t. The sign is a
    unit also in characteristic two. The rational comparison therefore has order zero.
11. In the component DVR, write its multiplier as a unit times a power of a uniformizer.
    The equality of completed lattices forces that power to be zero. It extends over
    every point. The local extensions agree in the function field and glue uniquely,
    since the normalization is integral. They satisfy the displayed smooth normalization.
-/
theorem nodal_normalization_adjunction
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hpure : ∀ T : Set C, T ∈ irreducibleComponents C → topologicalKrullDim T = 1)
    (hnodal : ∀ x : C, x ∉ p.smoothLocus → IsClosed ({x} : Set C) ∧
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
          (C.presheaf.stalk x) ≃+*
            (MvPowerSeries (Fin 2) k ⧸ Ideal.span
              {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}),
        ∀ a : k, e (AdicCompletion.of (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
          (C.presheaf.stalk x)
          (C.presheaf.germ ⊤ x (Set.mem_univ x)
            (p.appTop ((Scheme.ΓSpecIso (.of k)).inv a)))) =
              Ideal.Quotient.mk _ (MvPowerSeries.C a)) :
    (∀ x : C, x ∉ p.smoothLocus →
      Nat.card {T : irreducibleComponents C // x ∈ T.1} = 1 ∨
        Nat.card {T : irreducibleComponents C // x ∈ T.1} = 2) ∧
    (∀ (Z : Scheme.{u}) [IsIntegral Z] (i : Z ⟶ C) [IsClosedImmersion i],
      Set.range i ∈ irreducibleComponents C →
      ∀ x : C, x ∉ p.smoothLocus →
        Nat.card {z : Z.normalization // (Z.fromNormalization ≫ i) z = x} =
          if x ∈ Set.range i then
            if ∃ T ∈ irreducibleComponents C, x ∈ T ∧ T ≠ Set.range i then 1 else 2
          else 0) ∧
    ∃ F : FlatLCIAdjunctionSystem p 1, F.IsNormalized ∧
      (∀ U : C.Opens, Smooth (U.ι ≫ p) →
        ∃ eU : (Scheme.Modules.tensorPullback U.ι).obj
            (F.line (FlatLCIBaseChange.identity p)) ≅
              Scheme.Modules.exteriorSheaf (U.ι ≫ p).relativeDifferentials 1,
          F.IsSmoothComparison (FlatLCIBaseChange.identity p) U eU) ∧
      ∀ (Z : Scheme.{u}) [IsIntegral Z] (i : Z ⟶ C) [IsClosedImmersion i],
        Set.range i ∈ irreducibleComponents C → IsProper (i ≫ p) →
        IsFinite Z.fromNormalization ∧
        IsProper (Z.fromNormalization ≫ i ≫ p) ∧
        Smooth (Z.fromNormalization ≫ i ≫ p) ∧
        IsConnectedCurve (Z.fromNormalization ≫ i ≫ p) ∧
        (∀ z : Z, z ∉ (i ≫ p).smoothLocus ↔
          i z ∉ p.smoothLocus ∧
            ¬ ∃ T ∈ irreducibleComponents C, i z ∈ T ∧ T ≠ Set.range i) ∧
        (∀ z : Z, z ∉ (i ≫ p).smoothLocus →
          Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (Z.presheaf.stalk z))
            (Z.presheaf.stalk z) ≃+*
              (MvPowerSeries (Fin 2) k ⧸ Ideal.span
                {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1}))) ∧
        IsIso (pullback.snd Z.fromNormalization (i ≫ p).smoothLocus.ι) ∧
        ∃ B : Z.normalization.IdealSheafData,
          B.radical = B ∧ B.IsInvertible ∧
          (B.support : Set Z.normalization) =
            {z | (Z.fromNormalization ≫ i) z ∉ p.smoothLocus} ∧
          ∃! e : (Scheme.Modules.tensorPullback (Z.fromNormalization ≫ i)).obj
              (F.line (FlatLCIBaseChange.identity p)) ≅
                ((Z.fromNormalization ≫ i) ≫ p).relativeDifferentials ⊗
                  Scheme.Modules.dual B.toModules,
            IsNodalNormalizationAdjunctionComparison p F (Z.fromNormalization ≫ i) B e := by
  sorry

end AlgebraicGeometry
