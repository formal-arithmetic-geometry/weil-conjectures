/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.OrgogozoInductionData
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Sober
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import Sheaf.AlgebraicGeometry.ChowProjectiveClosedImmersions
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import Sheaf.AlgebraicGeometry.FlatProperComponentCountLowerSemicontinuous
import Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.AlgebraicGeometry.ProperBirationalNormalCurveIso
import Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair
import Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import Sheaf.TraceFormula.ProjectiveBundleProper
import WeilConjectures.AlgebraicGeometry.ChowLemma
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
import WeilConjectures.Blowup.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-! # Arbitrary-base marked semistable alteration

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé IX, Theorem 1.2
(i), (iii)--(vi), p. 131 (blueprint: lem-trf-dejong-arbitrary-base-marked-semistable).

## Main statement

* `exists_deJong_arbitraryBaseMarkedSemistable` states the marked semistable alteration over
  an arbitrary excellent integral Noetherian base.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Orgogozo

namespace AlgebraicGeometry

/-- A proper family of smooth geometrically integral generic curves with a finite étale generic
marking admits an arbitrary-base marked semistable alteration.
Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé IX, Theorem 1.2
(i), (iii)--(vi), p. 131 (blueprint: lem-trf-dejong-arbitrary-base-marked-semistable).

Proof plan (the node's twelve steps):
1. Apply Stein factorisation and identify the finite separable constants extension on the generic
   fibre, transporting the finite étale marking.
2. Apply Chow projectivisation and take the integral scheme-theoretic image of the dense open.
3. Identify the generic proper birational curve with the smooth normal generic fibre and close
   the transported marking.
4. Apply horizontal flatification and then stable modification of the marked curve pair.
5. Base-change the generic fibre, prove integrality and excellence of the new total space, and
   assemble the two alteration maps and the commutative square.
6. Use proper-flat component semicontinuity for connected nonempty fibres, the nodal local
   equation for reducedness and ordinary double points, and the relative Cartier criterion for
   the marking divisor.
7. Remove the singular and vertical boundary images from the base; the resulting closed set is
   nowhere dense and contains all points not already lying on the marking divisor.
-/
theorem exists_deJong_arbitraryBaseMarkedSemistable
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsNoetherian X] [IsNoetherian Y]
    (hX : IsExcellentScheme X) (hY : IsExcellentScheme Y)
    (y : Y) (hy : IsGenericPoint y Set.univ)
    [Smooth (f.fiberToSpecResidueField y)]
    [GeometricallyIntegral (f.fiberToSpecResidueField y)]
    (hdim : topologicalKrullDim (f.fiber y) = 1)
    (Z : Scheme.{u}) (j : Z ⟶ X) [IsClosedImmersion j]
    (hZ : IsNowhereDense (Set.range j))
    [IsFinite ((j ≫ f).fiberToSpecResidueField y)]
    [Etale ((j ≫ f).fiberToSpecResidueField y)] :
    ∃ (X₁ Y₁ : Scheme.{u}) (a : X₁ ⟶ X) (b : Y₁ ⟶ Y) (f₁ : X₁ ⟶ Y₁)
      (hfp : LocallyOfFinitePresentation f₁),
      a ≫ f = f₁ ≫ b ∧
      IsIntegral X₁ ∧ IsExcellentScheme X₁ ∧ IsNoetherian X₁ ∧
      IsIntegral Y₁ ∧ IsExcellentScheme Y₁ ∧ IsNoetherian Y₁ ∧
      (IsProper a ∧ Surjective a ∧
        (∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (pullback.snd a U.ι))) ∧
      (IsProper b ∧ Surjective b ∧
        (∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (pullback.snd b U.ι))) ∧
      IsProper f₁ ∧ Flat f₁ ∧ QuasiCompact f₁ ∧ QuasiSeparated f₁ ∧
      @HasNodalGeometricFibres _ _ f₁ hfp ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Y₁),
        (pullback (C := Scheme.{u}) f₁ g).IsPureDimension 1) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Y₁),
        IsReduced (pullback f₁ g)) ∧
      (∃ D : Scheme.{u}, ∃ i : D ⟶ X₁,
        IsEffectiveCartierCenter i ∧ IsProper (i ≫ f₁) ∧ Etale (i ≫ f₁) ∧
        (∀ d : D, i d ∈ ((@Scheme.Hom.smoothLocus _ _ f₁ hfp) : Set X₁)) ∧
        ∃ (T : Set Y₁) (hT : IsClosed T), IsNowhereDense T ∧
          Smooth (f₁ ∣_ (⟨Tᶜ, hT.isOpen_compl⟩ : Y₁.Opens)) ∧
          Set.preimage a (Set.range j) ⊆ Set.range i ∪ Set.preimage f₁ T) ∧
      (∃ y₁ : Y₁, IsGenericPoint y₁ Set.univ ∧
        Smooth (f₁.fiberToSpecResidueField y₁) ∧
        GeometricallyIntegral (f₁.fiberToSpecResidueField y₁)) := by
  sorry

end AlgebraicGeometry
