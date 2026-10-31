/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstantPurityFrobenius.CommonConstantUnitFrobenius
public import Mathlib.CategoryTheory.Whiskering

/-! # Natural comparison from integral to common-stage pullback

Source: the unchanged-object and pure-tensor formulas in
`rationalDerivedPullback_existsUnique` and `commonStageDerivedPullback_map_inclusion`.
(blueprint: def-pur-completed-unit-inclusion-pullback-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback

/-- Rationalization followed by the literal least-stage inclusion.
Source: blueprint coefficient conventions.
(blueprint: def-pur-completed-unit-inclusion-pullback-data). -/
def tensorUnitInclusion (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X : Scheme.{u}) :
    sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
          (Padic.finiteCoefficientBase l Ω)) X ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω)) X ⋙
    GeneralAlgebraicallyClosedCoefficients.inclusion (Padic.finiteCoefficientBase l Ω)

/-- The specified object equalities give a natural rational pullback comparison.
Source: unchanged-object pullback and its pure-tensor map formula.
(blueprint: def-pur-completed-unit-inclusion-pullback-data). -/
def tensorRationalPullbackComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    sfRationalConstructibleLocalization l E Y ⋙ rationalDerivedPullback l E f ≅
      constructibleIntegralPullback l E f ⋙ sfRationalConstructibleLocalization l E X := by
  let Q := sfRationalConstructibleLocalization l E Y
  let R := sfRationalConstructibleLocalization l E X
  let F := rationalDerivedPullback l E f
  let h := (rationalDerivedPullback_existsUnique l E f).exists.choose_spec
  refine NatIso.ofComponents (fun K ↦ eqToIso (h.2.1 (Q.obj K))) ?_
  intro K L a
  change F.map (Q.map a) ≫ eqToHom (h.2.1 (Q.obj L)) =
    eqToHom (h.2.1 (Q.obj K)) ≫ R.map ((constructibleIntegralPullback l E f).map a)
  have hm : F.map (Q.map a) = eqToHom (h.2.1 (Q.obj K)) ≫
      R.map ((constructibleIntegralPullback l E f).map a) ≫
        eqToHom (h.2.1 (Q.obj L)).symm :=
    (conj_eqToHom_iff_heq _ _ (h.2.1 (Q.obj K)) (h.2.1 (Q.obj L))).mpr
      (h.2.2 K L a 1)
  rw [hm]
  simp

set_option maxHeartbeats 1600000 in
-- Elaborating the two literal stage object equalities requires the larger bound.
/-- The literal stage inclusion commutes naturally with pullback.
Source: the prescribed common-stage map formula at the self stage.
(blueprint: def-pur-completed-unit-inclusion-pullback-data). -/
def tensorCommonPullbackComparison
    (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.inclusion L ⋙ commonStageDerivedPullback l Ω f ≅
      rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f ⋙
        GeneralAlgebraicallyClosedCoefficients.inclusion L := by
  let h := (commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec
  refine NatIso.ofComponents (fun K ↦ eqToIso (h.1 _)) ?_
  intro K M a
  change (commonStageDerivedPullback l Ω f).map
      ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map a) ≫ eqToHom (h.1 _) =
    eqToHom (h.1 _) ≫ (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
      ((rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).map a)
  have hm := ConstantPurityFrobenius.commonStageDerivedPullback_map_inclusion l Ω f L K M a
  have he := (conj_eqToHom_iff_heq _ _ (h.1 _) (h.1 _)).mpr hm
  rw [he]
  simp

/-- The normalized comparison through rationalization and least-stage inclusion.
Source: the preceding two natural object comparisons.
(blueprint: def-pur-completed-unit-inclusion-pullback-data). -/
def tensorInclusionPullbackComparison
    (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    tensorUnitInclusion l Ω Y ⋙ commonStageDerivedPullback l Ω f ≅
      constructibleIntegralPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
          (Padic.finiteCoefficientBase l Ω)) f ⋙ tensorUnitInclusion l Ω X :=
  Functor.isoWhiskerLeft (sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω)) Y)
    (tensorCommonPullbackComparison l Ω f (Padic.finiteCoefficientBase l Ω)) ≪≫
  Functor.isoWhiskerRight (tensorRationalPullbackComparison l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω)) f)
    (GeneralAlgebraicallyClosedCoefficients.inclusion (Padic.finiteCoefficientBase l Ω))

end WeilConjectures.CompletedUnitPullback
