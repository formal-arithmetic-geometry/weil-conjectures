/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrientationIntegralCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum
public import WeilConjectures.AlgebraicGeometry.DlLocallyConstructibleAdicHeart
public import WeilConjectures.AlgebraicGeometry.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.AlgebraicGeometry.IntegralTwistBaseChange
public import WeilConjectures.AlgebraicGeometry.IntegralAmbientOperationModels
public import WeilConjectures.AlgebraicGeometry.PuritySourceTransports
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.SfIntegralConstructibleTriangulated
import Mathlib.Data.Nat.Prime.Infinite

/-! # Canonical positive coefficient-line comparisons

Source: main-20261015, def-coefficient-twists-detailed, completed tensor and
scheme pullback conventions (blueprint: def-sf-orientation-scalar-line-comparisons).
The original coefficient lines are reexported. Their normalized inverse-image
maps are supplied for arbitrary scheme morphisms, as required by orientations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

/-- The positive shifted line has intrinsic bounded constructibility and uniform
finite Tor amplitude. Source: coefficient-line conventions
(blueprint: def-sf-orientation-scalar-line-comparisons).
Proof: locally trivialize the complete rank-one root line. Every finite reduction
is the coefficient unit in degree -2d, so it is constructible with one support
interval and one Tor interval, independent of the finite level. The completed
root tower with its quotient units reconstructs the line. These are exactly the
constructibility, derived-completeness and uniform finite-Tor clauses. -/
theorem sfOrientationIntegralComplex_mem
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (d : ℕ) :
    finiteTorConstructibleIntegral l E X
      (DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d)) := by
  obtain ⟨p, hlp, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_rfl
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := Nat.ne_of_lt (Nat.lt_of_succ_le hlp)
  rw [← (integral_residue_tor D l hl E X).2]
  let e : DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d) ≅
      (sfIntegralTwistingObject l E X (d : ℤ))⟦2 * (d : ℤ)⟧ :=
    ((DerivedCategory.singleFunctors _).shiftIso (2 * (d : ℤ)) (-2 * (d : ℤ)) 0
      (by omega)).symm.app (FrobeniusCoefficientTwists.positiveLine l E X d)
  exact (sfIntegralConstructible l E X).prop_of_iso e.symm
    ((sfIntegralConstructible l E X).le_shift (2 * (d : ℤ)) _
      (sfIntegralTwistingObject_mem l E X (d : ℤ)))

/-- The existing integral positive shifted line in intrinsic constructible coordinates.
Source: coefficient conventions (blueprint: def-sf-orientation-scalar-line-comparisons). -/
def sfOrientationIntegralLine
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (d : ℕ) :
    sfIntegralConstructibleCategory l E X :=
  ⟨DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d),
    (sfOrientationIntegralComplex_mem l E X d).1⟩


/-- The one-term representative is the published Tate coefficient shifted by 2d.
This is the standard single-functor shift constraint, with no orientation choice.
Source: twist and shift conventions (blueprint: def-sf-orientation-scalar-line-comparisons). -/
def sfOrientationIntegralShiftIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (d : ℕ) :
    DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d) ≅
      (sfIntegralTwistingObject l E X (d : ℤ))⟦2 * (d : ℤ)⟧ :=
  ((DerivedCategory.singleFunctors _).shiftIso (2 * (d : ℤ)) (-2 * (d : ℤ)) 0
    (by omega)).symm.app (FrobeniusCoefficientTwists.positiveLine l E X d)

/-- Completed scalar extension of the shifted positive root line. Completion is
compared with ordinary scalar extension first, and the ordinary root comparison
is then localized on the one-term representative. Thus all local root tensors
and the coefficient scalar map are retained.
Source: scalar extension convention (blueprint: def-sf-orientation-scalar-line-comparisons). -/
def sfOrientationIntegralScalarAmbient
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L] (a : E →ₐ[Padic l] L)
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] (d : ℕ) :=
  (scalarCompletionIso l E L a X
    (DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d))
    (sfOrientationIntegralComplex_mem l E X d).1.1).symm ≪≫
    (integralOrdinaryScalar l E L a X).mapDerivedCategoryFactors.app
      (sfOrientationIntegralComplex l E X d) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (integralOrdinaryScalar l E L a X) (.up ℤ) (-2 * (d : ℤ))).app
        (FrobeniusCoefficientTwists.positiveLine l E X d)) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.single _ (.up ℤ) (-2 * (d : ℤ))).mapIso
        (twistLineScalarIso l E X L a (d : ℤ)))

private theorem fullSubcategoryIso_existsUnique_of_source_eq
    {C : Type*} [Category C] (P : ObjectProperty C) {X Y : P.FullSubcategory}
    {Z : C} (h : X.obj = Z) (e : Z ≅ Y.obj) :
    ∃! e' : X ≅ Y, HEq e'.hom.hom e.hom := by
  subst Z
  exact ⟨P.isoMk e, HEq.rfl, fun e' he' ↦
    Iso.ext (ObjectProperty.hom_ext _ (eq_of_heq he'))⟩

/-- The completed scalar line comparison lifts uniquely to the intrinsic
integral representative of rational scalar extension.
Source: scalar extension (blueprint: def-sf-orientation-scalar-line-comparisons).
Proof: the intrinsic scalar functor is completed ordinary scalar extension.
The preceding augmentation-normalized comparison therefore has exactly these
underlying objects. Lift it through the fully faithful full-subcategory inclusion;
the underlying map equation and faithfulness give uniqueness. -/
theorem sfOrientationRationalScalarLine_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L] (a : E →ₐ[Padic l] L)
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] (d : ℕ) :
    ∃! e : ((sfRationalScalarExtension l E X 0 (Fact.out : l.Prime).ne_zero L a).obj
      ((sfRationalConstructibleLocalization l E X).obj
        (sfOrientationIntegralLine l E X d))).obj ≅ sfOrientationIntegralLine l L X d,
      HEq e.hom.hom (sfOrientationIntegralScalarAmbient l E L a X d).hom := by
  have h := (sfRationalScalarExtension_existsUnique l E X 0
    (Fact.out : l.Prime).ne_zero L a).exists.choose_spec.2.1
      ((sfRationalConstructibleLocalization l E X).obj (sfOrientationIntegralLine l E X d))
  have h' : ((sfRationalScalarExtension l E X 0 (Fact.out : l.Prime).ne_zero L a).obj
      ((sfRationalConstructibleLocalization l E X).obj
        (sfOrientationIntegralLine l E X d))).obj.obj =
      (integralScalarExtension l E L a X).obj
        (DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d)) :=
    congrArg (fun K ↦ K.obj.obj) h
  exact fullSubcategoryIso_existsUnique_of_source_eq (sfIntegralConstructible l L X)
    (Y := sfOrientationIntegralLine l L X d)
    h' (sfOrientationIntegralScalarAmbient l E L a X d)

/-- The scalar comparison in raw intrinsic rational coordinates.
Source: coefficient convention (blueprint: def-sf-orientation-scalar-line-comparisons). -/
def sfOrientationRationalScalarLine
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L] (a : E →ₐ[Padic l] L)
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] (d : ℕ) :
    (sfRationalScalarExtension l E X 0 (Fact.out : l.Prime).ne_zero L a).obj
      ((sfRationalConstructibleLocalization l E X).obj (sfOrientationIntegralLine l E X d)) ≅
        (sfRationalConstructibleLocalization l L X).obj (sfOrientationIntegralLine l L X d) :=
  (sfRationalConstructibleLocalization l L X).mapIso
    (sfOrientationRationalScalarLine_existsUnique l E L a X d).exists.choose


/-- The integral shifted root line on the given k-scheme. Residue invertibility
comes from ell different from the characteristic, rather than an extra hypothesis.
Source: coefficient conventions (blueprint: def-sf-orientation-scalar-line-comparisons). -/
def sfOrientationIntegralLineOn (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D) (d : ℕ) :
    sfIntegralConstructibleCategory C.l E X.obj.left :=
  @sfOrientationIntegralLine C.l _ E _ _ _ X.obj.left
    (dlAdicGeometricResidueInvertible D C X.obj.left) d

/-- The integral pullback arrow with the invertibility already supplied by k.
Source: coefficient comparison convention
(blueprint: def-sf-orientation-scalar-line-comparisons). -/
def sfOrientationIntegralPullOn (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {X Y : SixFunctorSpace D} (f : X ⟶ Y) (d : ℕ) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  letI := dlAdicGeometricResidueInvertible D C Y.obj.left
  (sfOrientationIntegralDerivedPull C.l E f.hom.left d).hom

/-- The completed tensor comparison with the same geometric invertibility witness.
Source: coefficient comparison convention
(blueprint: def-sf-orientation-scalar-line-comparisons). -/
def sfOrientationIntegralProductOn (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D) (d e : ℕ) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  (sfOrientationIntegralDerivedProduct C.l E X.obj.left d e).hom

/-- The actual coefficient-transition comparison on the shifted root line, using
the completed ordinary scalar comparison before rational localization.
Source: finite coefficient-field compatibility
(blueprint: def-sf-orientation-scalar-line-comparisons). -/
def sfOrientationStageScalarLine (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    {E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E₀ ≤ L)
    (X : SixFunctorSpace D) (d : ℕ) :
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left).T h).obj
      ((sfRationalConstructibleLocalization C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left).obj
          (sfOrientationIntegralLineOn D C
            (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X d)) ≅
    (sfRationalConstructibleLocalization C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X.obj.left).obj
        (sfOrientationIntegralLineOn D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X d) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  (operationStageTransitionIso C.l C.Qbar X.obj.left E₀ L h).app
    ((sfRationalConstructibleLocalization C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left).obj
        (sfOrientationIntegralLineOn D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X d)) ≪≫
    sfOrientationRationalScalarLine C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀)
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion C.l C.Qbar E₀ L h)
      X.obj.left d

end WeilConjectures
