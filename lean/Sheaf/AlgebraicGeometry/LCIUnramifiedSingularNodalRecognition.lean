/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
import Sheaf.AlgebraicGeometry.NodalCurveLCICriterion
import Sheaf.AlgebraicGeometry.UnramifiedOverFieldLocalCriterion
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Recognizing nodes from complete intersection fibres

Source: Stacks Project, Curves, Tags 0C59 and 0C4E; Divisors, Tags 0C3I and 0C3K;
Morphisms, Tag 02G7 (blueprint: lem-trf-lci-unramified-singular-nodal-recognition).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a flat locally finitely presented morphism with empty or pure one-dimensional
local complete intersection geometric fibres, unramifiedness of its first-Fitting singular
subscheme forces every nonsmooth geometric-fibre point to be closed with nodal completion.

Source: Stacks Project, Curves, Tag 0C59, implication (2) => (1), using Tag 0C4E;
Divisors, Tags 0C3I and 0C3K; Morphisms, Tag 02G7.
(blueprint: lem-trf-lci-unramified-singular-nodal-recognition)

Proof plan:
1. Fix an algebraically closed field Ω and a geometric point y. Put C = T ×_B Spec Ω.
   An empty C has no points to check. Otherwise the hypothesis gives pure dimension one
   and an affine cover by finite-type local complete intersection Ω-algebras. Finite
   presentation of g also gives local finite type (def-weil-finite-type-morphism and
   def-sbc-locally-finite-presentation).
2. Relative differential base change (lem-trf-relative-differential-sheaf-base-change)
   and Fitting pullback (lem-trf-fitting-ideal-sheaf-pullback) identify the first-Fitting
   subscheme W of C/Ω with C ×_T Sing(g). Isomorphic finite-type modules have equal
   Fitting ideals, computed by the kernel-minor ideals defining Sing. Pullback pasting
   identifies W with Sing(g) ×_B Spec Ω (def-pc-fibre-product). Thus W/Ω is unramified
   by lem-weil-pbc-unramified-base-change-open.
3. The nonsmooth locus of C/Ω is precisely the image of W by
   lem-trf-field-curve-fitting-smooth-preparation. Since W/Ω is unramified it is locally
   of finite type, and lem-trf-unramified-over-field-local-criterion says every point of
   W is closed in W.
4. W is a closed subscheme of C (def-weil-closed-immersion). A singleton closed in W
   is closed in C, so every nonsmooth point z is closed, with no closedness assumption.
5. Apply lem-trf-nodal-curve-lci-criterion, implication (2) => (1). The closed nonsmooth
   point z is a node. Any algebraic closure of the already algebraically closed Ω is
   isomorphic to Ω (def-weil-algebraic-closure). Its base-change projection to C is an
   isomorphism by def-pc-fibre-product, giving isomorphic local rings and maximal-ideal
   completions at the corresponding points. Transport coefficients along the inverse
   field isomorphism in the nodal power-series quotient. This yields exactly the
   completed local ring over Ω asserted here. Since Ω, y and z were arbitrary, finish.
-/
theorem lci_unramified_singular_nodal_recognition
    {T B : Scheme.{u}} (g : T ⟶ B) [Flat g] [LocallyOfFinitePresentation g]
    (hfibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (CommRingCat.of Ω) ⟶ B),
      IsEmpty (pullback (C := Scheme.{u}) g y) ∨
        ((pullback (C := Scheme.{u}) g y).IsPureDimension 1 ∧
          ∀ z : pullback (C := Scheme.{u}) g y,
            ∃ U : (pullback (C := Scheme.{u}) g y).affineOpens, z ∈ U.1 ∧
            ∃ (ft : @Algebra.FiniteType Ω
                Γ(pullback (C := Scheme.{u}) g y, U.1) _ _
                (((pullback.snd g y).appLE ⊤ U.1 (by simp)).hom.comp
                  (Scheme.ΓSpecIso (.of Ω)).inv.hom).toAlgebra),
              @Algebra.IsLocalCompleteIntersection Ω
                Γ(pullback (C := Scheme.{u}) g y, U.1) _ _
                (((pullback.snd g y).appLE ⊤ U.1 (by simp)).hom.comp
                  (Scheme.ΓSpecIso (.of Ω)).inv.hom).toAlgebra ft))
    (hSing : IsUnramified (Scheme.firstFittingSingularSubscheme g ≫ g)) :
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (CommRingCat.of Ω) ⟶ B) (z : pullback (C := Scheme.{u}) g y),
      z ∉ (pullback.snd g y).smoothLocus →
        z ∈ closedPoints (pullback (C := Scheme.{u}) g y) ∧
          Nonempty
            (AdicCompletion
                (IsLocalRing.maximalIdeal
                  ((pullback (C := Scheme.{u}) g y).presheaf.stalk z))
                ((pullback (C := Scheme.{u}) g y).presheaf.stalk z) ≃+*
              (MvPowerSeries (Fin 2) Ω ⧸
                Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                  (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)})) := by
  sorry

end AlgebraicGeometry
