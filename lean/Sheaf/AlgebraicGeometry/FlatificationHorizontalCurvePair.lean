/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
import Sheaf.AlgebraicGeometry.GenericFlatFinitePresentation
import Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup
import Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension
import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.RingTheory.QuasiFiniteAtPrime
import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.Blowup.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.RingHom.Flat

/-! # Simultaneous flatification of a generic curve and its horizontal marking

Source: ILO, Travaux de Gabber, Expose X, proof of Theorem 3.4, Step 2, printed p. 160;
Stacks Project Tags 081R, 080D, 02NS, 0GSJ, 07QU and 02LS
(blueprint: lem-trf-flatification-horizontal-curve-pair).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A single admissible blowup simultaneously flattens the projective curve and its
horizontal marking. Kernel equalities specify schematic closures, including the empty
marking. The two generic-fibre squares specify the original generic fibres and their
embeddings. The auxiliary map `k₁` identifies the marking transform inside its own ambient
base change; its two projection equations specify the canonical ambient map.

Source: ILO, Expose X, Theorem 3.4, proof Step 2, printed p. 160; Stacks Tags 081R,
080D, 02NS, 0GSJ, 07QU and 02LS
(blueprint: lem-trf-flatification-horizontal-curve-pair).

Proof:
1. Projectivity gives properness by `lem-pc-projective-proper`. Properness of the closed
   marking follows by `lem-weil-pbc-proper-fp-permanence`. Apply
   `lem-sbc-generic-flat-finite-presentation` to their disjoint union to choose a common
   nonempty flat, locally finitely presented open. Noetherianity makes that open compact.
2. Apply `lem-trf-flattening-by-admissible-blowup` once to the disjoint union. Kernels of
   restriction are componentwise, so both strict transforms are flat and finitely
   presented. Use `lemma-nagata-strict-transform-closure-characterization` to identify
   them with the closures over the centre complement.
3. The standard blowup charts are the subrings A[I/a] of Frac(A), with zero charts empty.
   Thus the blowup is integral and isomorphic over the dense centre complement.
   `lemma-nagata-blowup-proper`, `lem-weil-pbc-finite-type-over-noetherian` and
   `lem-exc-finite-type-localization-excellent` give its Noetherianity and excellence.
4. The surjection Sym(I) to the Rees algebra and
   `prop-nagata-relative-proj-functoriality` embed the blowup into P(I), as required by
   `def-trf-projective-bundle-morphism`. Apply `lem-pc-projective-base-change` to the curve
   and compose the closed immersions to retain finite-projective-space projectivity.
5. Both transforms retain their generic fibres. Flatness over the integral base injects
   each local ring into its localization over the base fraction field, by
   `def-weil-pbc-flat-ring-map`. The generic fibres are therefore schematically dense,
   giving the stated kernel equalities with the generic-fibre closures.
6. Those localized curve rings are domains, hence so are the original local rings.
   The dense irreducible generic curve makes its transform integral. Inclusion of the
   generic marking gives inclusion of its closure. Proper base change and composition
   (`lem-weil-pbc-proper-fp-permanence`) give properness of the curve projection, which is
   an isomorphism over a dense open and hence birational.
7. Apply `lem-trf-flat-dense-generic-fibre-pure-dimension` in dimensions one and zero.
   Properness and the nonempty generic curve make every curve fibre nonempty.
   `lem-weil-pbc-etale-smooth-zero-dimensional-fibres` gives the marking's generic
   dimension zero; the empty marking has empty closure and causes no exception.
8. The marking is proper, and its zero-dimensional fibres give local quasi-finiteness by
   `lem-weil-pbc-ring-quasifinite-zero-fibre-dimension` and `pqf-def-quasifinite`.
   `pqf-lem-proper-lqf-finite` then makes it finite. -/
theorem exists_flatification_horizontal_curve_pair
    {S C H Hη : Scheme.{u}} [IsIntegral S] [IsNoetherian S]
    (hexc : ∀ V : S.Opens, IsAffineOpen V → IsExcellent Γ(S, V))
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S))
    (h : C ⟶ S) [IsHProjective h] [IsIntegral C]
    [Smooth (h.fiberToSpecResidueField η)] [IrreducibleSpace (h.fiber η)]
    (hdim : topologicalKrullDim (h.fiber η) = 1)
    (jη : Hη ⟶ h.fiber η) [IsClosedImmersion jη]
    [IsFinite (jη ≫ h.fiberToSpecResidueField η)]
    [Etale (jη ≫ h.fiberToSpecResidueField η)]
    (i : H ⟶ C) [IsClosedImmersion i]
    (hclosure : i.ker = (jη ≫ h.fiberι η).ker) :
    ∃ (U : S.Opens) (B : IsAdmissible S U)
      (C₁ H₁ : Scheme.{u}) (c₁ : C₁ ⟶ pullback h B.I.blowupMap)
      (i₁ : H₁ ⟶ C₁) (k₁ : H₁ ⟶ pullback (i ≫ h) B.I.blowupMap),
      Dense (U : Set S) ∧
      IsIntegral B.I.blowup ∧ IsNoetherian B.I.blowup ∧
      (∀ V : B.I.blowup.Opens, IsAffineOpen V → IsExcellent Γ(B.I.blowup, V)) ∧
      IsProjectiveBundle B.I.blowupMap ∧ IsIso (B.I.blowupMap ∣_ U) ∧
      IsIntegral C₁ ∧ IsClosedImmersion c₁ ∧ IsClosedImmersion i₁ ∧
      IsClosedImmersion k₁ ∧
      k₁ ≫ pullback.fst (i ≫ h) B.I.blowupMap ≫ i =
        i₁ ≫ c₁ ≫ pullback.fst h B.I.blowupMap ∧
      k₁ ≫ pullback.snd (i ≫ h) B.I.blowupMap =
        i₁ ≫ c₁ ≫ pullback.snd h B.I.blowupMap ∧
      c₁.ker = (strictTransformι h B.I.blowupMap B.I.support.compl).ker ∧
      k₁.ker = (strictTransformι (i ≫ h) B.I.blowupMap B.I.support.compl).ker ∧
      c₁.ker =
        (pullback.snd (h.fiberι η) (pullback.fst h B.I.blowupMap)).ker ∧
      (i₁ ≫ c₁).ker =
        (pullback.snd (jη ≫ h.fiberι η) (pullback.fst h B.I.blowupMap)).ker ∧
      IsHProjective (c₁ ≫ pullback.snd h B.I.blowupMap) ∧
      Flat (c₁ ≫ pullback.snd h B.I.blowupMap) ∧
      LocallyOfFinitePresentation (c₁ ≫ pullback.snd h B.I.blowupMap) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (s : Spec (.of Ω) ⟶ B.I.blowup),
        Nonempty (pullback (C := Scheme.{u}) (c₁ ≫ pullback.snd h B.I.blowupMap) s) ∧
        ∀ Z ∈ irreducibleComponents
          (pullback (C := Scheme.{u}) (c₁ ≫ pullback.snd h B.I.blowupMap) s),
          topologicalKrullDim Z = 1) ∧
      IsFinite (i₁ ≫ c₁ ≫ pullback.snd h B.I.blowupMap) ∧
      Flat (i₁ ≫ c₁ ≫ pullback.snd h B.I.blowupMap) ∧
      LocallyOfFinitePresentation (i₁ ≫ c₁ ≫ pullback.snd h B.I.blowupMap) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (s : Spec (.of Ω) ⟶ B.I.blowup),
        Nonempty (pullback (C := Scheme.{u}) (i₁ ≫ c₁ ≫ pullback.snd h B.I.blowupMap) s) →
        ∀ Z ∈ irreducibleComponents
          (pullback (C := Scheme.{u}) (i₁ ≫ c₁ ≫ pullback.snd h B.I.blowupMap) s),
          topologicalKrullDim Z = 0) ∧
      (∃ (gC : h.fiber η ⟶ C₁) (gH : Hη ⟶ H₁),
        gC ≫ c₁ ≫ pullback.fst h B.I.blowupMap = h.fiberι η ∧
        gH ≫ i₁ = jη ≫ gC ∧
        IsPullback gC (h.fiberToSpecResidueField η)
          (c₁ ≫ pullback.snd h B.I.blowupMap ≫ B.I.blowupMap)
          (S.fromSpecResidueField η) ∧
        IsPullback gH (jη ≫ h.fiberToSpecResidueField η)
          (i₁ ≫ c₁ ≫ pullback.snd h B.I.blowupMap ≫ B.I.blowupMap)
          (S.fromSpecResidueField η)) ∧
      IsProper (c₁ ≫ pullback.fst h B.I.blowupMap) ∧
      (∃ V : C.Opens, Dense (V : Set C) ∧
        IsIso ((c₁ ≫ pullback.fst h B.I.blowupMap) ∣_ V)) := by
  sorry

end AlgebraicGeometry
