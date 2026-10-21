/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.TraceFormula.ValuationHorizontalCurveModels
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest
import Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal
import Sheaf.TraceFormula.RelativeDimensionBaseChange
import Sheaf.TraceFormula.ValuationCurveProjectivePreparation
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.SepClosedValuationGeometricComponents

/-! # Proper completion of a valuation-curve modification near a smooth centre

Source: Temkin, Stable modification of relative curves, Lemma 4.4.1(i),(ii) and the
local-to-proper reduction in Lemma 4.4.2, printed pp. 30--31
(blueprint: lem-trf-valuation-modification-proper-completion).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Temkin

/-- The canonical localization of the valuation base at a specified prime.
Source: Temkin, proof of Lemma 4.4.2, p. 30
(blueprint: lem-trf-valuation-modification-proper-completion). -/
def valuationCompletionBaseMap {K : Type u} [Field K] (V : ValuationSubring K)
    (p : PrimeSpectrum V) : Spec (.of (Localization.AtPrime p.asIdeal)) ⟶ Spec (.of V) :=
  Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime p.asIdeal)))

/-- The generic point of the localized base, constructed by the localization universal
property from the given fraction field. Denominators outside the prime are nonzero.
Source: Temkin, proof of Lemma 4.4.2, p. 30
(blueprint: lem-trf-valuation-modification-proper-completion). -/
def valuationCompletionGenericMap {K : Type u} [Field K] (V : ValuationSubring K)
    (p : PrimeSpectrum V) : Spec (.of K) ⟶ Spec (.of (Localization.AtPrime p.asIdeal)) :=
  Spec.map (CommRingCat.ofHom
    (IsLocalization.lift (S := Localization.AtPrime p.asIdeal) (g := algebraMap V K)
      (fun a ↦ IsLocalization.map_units K
        ⟨a.val, p.asIdeal.primeCompl_le_nonZeroDivisors a.property⟩)))

/-- The induced geometric centre in the base-changed completion. It is the value of the
canonical section supplied by the specified geometric point, not a chosen lift.
Source: Temkin, proof of Lemma 4.4.2, pp. 30--31
(blueprint: lem-trf-valuation-modification-proper-completion). -/
def valuationCompletionGeometricCentre {U C S : Scheme.{u}} (c : C ⟶ S) (j : U ⟶ C)
    {Ω : Type u} [Field Ω] (a : Spec (.of Ω) ⟶ U) :
    ↥(pullback (C := Scheme.{u}) c ((a ≫ j) ≫ c)) :=
  (pullback.lift (a ≫ j) (𝟙 (Spec (.of Ω))) (Category.id_comp _).symm)
    (IsLocalRing.closedPoint Ω)

/-- A modification of relative valuation curves admits a simultaneous proper completion
near a smooth point with positive-dimensional fibre. The cartesian square preserves the
whole original neighbourhood. Nodal fibres are tested over the chosen algebraic closures
of residue fields; the conclusions quantify over every algebraically closed geometric point.

Source: Temkin, Lemma 4.4.1(i),(ii) and the local-to-proper reduction in the proof of
Lemma 4.4.2, pp. 30--31
(blueprint: lem-trf-valuation-modification-proper-completion).

Proof, following the ten steps of the node:
1. Localize V at c(x). The base localization is open since the prime chain is finite.
   Flatness, finite presentation, fibre purity, properness, the generic isomorphism and
   schematic density restrict. The generic-point case cannot have a positive-dimensional fibre.
2. Choose a smooth affine neighbourhood of x. Properness removes the image of the complement
   of the given nodal neighbourhood of the fibre. The resulting target and source have
   geometrically reduced fibres, the latter by the empty-marking semistable-curve clause of
   lem-trf-geometrically-reduced-eta-normal.
3. Normalize both restrictions using lem-trf-valuation-curve-projective-preparation.
   The finite normalizations are isomorphisms by eta-normality on affine opens. Thus neither
   the original fibre nor its ambient neighbourhood changes.
4. The horizontal-model lemma gives finitely many components. Normality makes them disjoint
   and open and closed. Retain the component through x. Flat torsion-free sections inject
   into the generic localization, making its integral generic fibre schematically dense;
   the restricted source is integral as well.
5. The preparation lemma makes the modification locus finite and quasi-finite over the base.
   Its closed fibre is discrete, so x is closed. Shrink to an affine neighbourhood U where
   x is the only closed modification point.
6. Apply projective preparation to the normal affine U, and extend the modification by the
   identity off its closed modification locus. The resulting cartesian square retains Y_U.
   Projectivity and composition of proper morphisms give properness over the base.
7. Retain the open-and-closed integral components containing U and Y_U. Flatness and finite
   generic components justify this operation. Apply the algebraic-closure reducedness test
   to obtain geometrically reduced fibres over every field extension.
8. The separably closed valuation geometric-component lemma makes the integral reduced
   generic fibres geometrically integral. Their generic isomorphism and the schematically
   dense generic opens give the stated modification.
9. The modification locus meets the closed fibre only at x. Its residue extension over the
   separably closed base residue field is finite purely inseparable, by the closed-point
   field lemma. Universal injectivity of that extension gives the single induced geometric
   centre and the isomorphism away from it, for every specified geometric point.
10. Smoothness of U is preserved by base change. The cartesian square identifies both the
    original geometric exceptional fibre and its open ambient neighbourhood.
-/
theorem valuation_modification_proper_completion
    (K : Type u) [Field K] [IsSepClosed K]
    (V : ValuationSubring K) [Finite (PrimeSpectrum V)]
    {C Y : Scheme.{u}} (c : C ⟶ Spec (.of V))
    (hC : RelativeCurve c) (f : Y ⟶ C) (hY : RelativeCurve (f ≫ c))
    [IsReduced Y]
    (hCgeneric : Smooth (pullback.snd c (Spec.map (CommRingCat.ofHom V.subtype))))
    (hYgeneric : Smooth (pullback.snd (f ≫ c)
      (Spec.map (CommRingCat.ofHom V.subtype))))
    (hf : EtaModification (Spec.map (CommRingCat.ofHom V.subtype)) f c)
    (x : C) (hx : ∃ W : C.Opens, x ∈ W ∧ Smooth (W.ι ≫ c))
    (hpositive : 0 < topologicalKrullDim (f.fiber x))
    (hnodal : ∃ N : Y.Opens, (∀ z : Y, f z = x → z ∈ N) ∧
      ∀ (t : Spec (.of V))
        (z : pullback (C := Scheme.{u}) (f ≫ c) (Orgogozo.geometricPoint (Spec (.of V)) t)),
        pullback.fst (f ≫ c) (Orgogozo.geometricPoint (Spec (.of V)) t) z ∈ N →
        (∃ W : (pullback (f ≫ c) (Orgogozo.geometricPoint (Spec (.of V)) t)).Opens,
          z ∈ W ∧ Smooth (W.ι ≫
            pullback.snd (f ≫ c) (Orgogozo.geometricPoint (Spec (.of V)) t))) ∨
        Orgogozo.IsOrdinaryDoublePoint
          (pullback.snd (f ≫ c) (Orgogozo.geometricPoint (Spec (.of V)) t)) z) :
    ∃ (U : Scheme.{u}) (u : U)
      (j₀ : U ⟶ pullback c (valuationCompletionBaseMap V (c x)))
      (Cbar Ybar : Scheme.{u})
      (cbar : Cbar ⟶ Spec (.of (Localization.AtPrime (c x).asIdeal)))
      (j : U ⟶ Cbar) (fbar : Ybar ⟶ Cbar)
      (i : pullback f (j₀ ≫ pullback.fst c (valuationCompletionBaseMap V (c x))) ⟶ Ybar),
      IsAffine U ∧ IsOpenImmersion j₀ ∧
      (j₀ ≫ pullback.fst c (valuationCompletionBaseMap V (c x))) u = x ∧
      IsIntegral Cbar ∧ IsIntegral Ybar ∧
      IsProper cbar ∧ IsProper (fbar ≫ cbar) ∧
      RelativeCurve cbar ∧ RelativeCurve (fbar ≫ cbar) ∧
      IsOpenImmersion j ∧ j ≫ cbar =
        j₀ ≫ pullback.snd c (valuationCompletionBaseMap V (c x)) ∧
      (∀ z : Cbar, IsDomain (Cbar.presheaf.stalk z) ∧
        IsIntegrallyClosed (Cbar.presheaf.stalk z)) ∧
      GeometricallyReduced cbar ∧ GeometricallyReduced (fbar ≫ cbar) ∧
      GeometricallyIntegral (pullback.snd cbar (valuationCompletionGenericMap V (c x))) ∧
      GeometricallyIntegral
        (pullback.snd (fbar ≫ cbar) (valuationCompletionGenericMap V (c x))) ∧
      EtaModification (valuationCompletionGenericMap V (c x)) fbar cbar ∧
      IsPullback i (pullback.snd f
        (j₀ ≫ pullback.fst c (valuationCompletionBaseMap V (c x)))) fbar j ∧
      cbar (j u) = IsLocalRing.closedPoint (Localization.AtPrime (c x).asIdeal) ∧
      IsClosed ({cbar.asFiber (j u)} : Set (cbar.fiber (cbar (j u)))) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ U),
        a (IsLocalRing.closedPoint Ω) = u →
        {z : pullback (C := Scheme.{u}) cbar ((a ≫ j) ≫ cbar) |
          pullback.fst cbar ((a ≫ j) ≫ cbar) z = j u} =
          {valuationCompletionGeometricCentre cbar j a} ∧
        (∃ W : (pullback cbar ((a ≫ j) ≫ cbar)).Opens,
          valuationCompletionGeometricCentre cbar j a ∈ W ∧
          Smooth (W.ι ≫ pullback.snd cbar ((a ≫ j) ≫ cbar))) ∧
        ∀ W : (pullback cbar ((a ≫ j) ≫ cbar)).Opens,
          valuationCompletionGeometricCentre cbar j a ∉ W →
          IsIso ((pullback.snd fbar (pullback.fst cbar ((a ≫ j) ≫ cbar))) ∣_ W) := by
  sorry

end AlgebraicGeometry.Temkin
