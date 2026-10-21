/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.FiniteReductionComparisons
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer

/-! # Finite reduction comparisons for the Kummer-normalized affine orientation

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
thm-pur-finite-reduction-of-purity, orientation clause
(blueprint: def-pur-finite-affine-orientation-comparison).
The supported boundary fixes the orientation at every positive coefficient level.

## Main definitions

- `finiteReductionOrientation`: the supported-Kummer affine orientation.
- `finiteReductionOrientationInputComparison`: its coefficient-input comparison.
- `finiteReductionOrientationExceptionalComparison`: its exceptional comparison.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/- The affine-line projection is finite type, quasi-compact and separated over
the finite-type base.  These interfaces are recorded here because the pinned
library does not expose the corresponding affine-space instances. -/
/-- Relative affine space is locally of finite type over a locally finite-type base.
Proof: over Spec R its coordinate algebra is the polynomial algebra R[t], generated
by t over R. Compose these locally finite-type affine charts with the base map.
Source: blueprint thm-pur-finite-reduction-of-purity, affine-orientation setup
(blueprint: def-pur-finite-affine-orientation-comparison). -/
theorem affineSpace_over_locallyOfFiniteType {S Y : Scheme.{u}}
    [Y.Over S] [LocallyOfFiniteType (Y ↘ S)] :
    LocallyOfFiniteType (AffineSpace (ULift.{u} (Fin 1)) Y ↘ S) := by
  sorry

/-- Relative affine space is quasi-compact over a quasi-compact base morphism.
Proof: the inverse image of an affine base chart is its affine polynomial spectrum,
so the projection is quasi-compact. Quasi-compact morphisms are closed under composition.
Source: blueprint thm-pur-finite-reduction-of-purity, affine-orientation setup
(blueprint: def-pur-finite-affine-orientation-comparison). -/
theorem affineSpace_over_quasiCompact {S Y : Scheme.{u}}
    [Y.Over S] [QuasiCompact (Y ↘ S)] :
    QuasiCompact (AffineSpace (ULift.{u} (Fin 1)) Y ↘ S) := by
  sorry

/-- Relative affine space is separated over a separated base morphism.
Proof: on a polynomial chart its diagonal is the closed immersion cut out by t1-t2.
The projection is separated, and composing separated morphisms preserves separatedness.
Source: blueprint thm-pur-finite-reduction-of-purity, affine-orientation setup
(blueprint: def-pur-finite-affine-orientation-comparison). -/
theorem affineSpace_over_isSeparated {S Y : Scheme.{u}}
    [Y.Over S] [IsSeparated (Y ↘ S)] :
    IsSeparated (AffineSpace (ULift.{u} (Fin 1)) Y ↘ S) := by
  sorry

/-- The canonical locally finite-type instance for the relative affine line.
Source: blueprint thm-pur-finite-reduction-of-purity, affine-orientation setup
(blueprint: def-pur-finite-affine-orientation-comparison). -/
noncomputable instance affineSpace_over_locallyOfFiniteType_inst {S Y : Scheme.{u}}
    [Y.Over S] [LocallyOfFiniteType (Y ↘ S)] :
    LocallyOfFiniteType (AffineSpace (ULift.{u} (Fin 1)) Y ↘ S) :=
  affineSpace_over_locallyOfFiniteType

/-- The canonical quasi-compact instance for the relative affine line.
Source: blueprint thm-pur-finite-reduction-of-purity, affine-orientation setup
(blueprint: def-pur-finite-affine-orientation-comparison). -/
noncomputable instance affineSpace_over_quasiCompact_inst {S Y : Scheme.{u}}
    [Y.Over S] [QuasiCompact (Y ↘ S)] :
    QuasiCompact (AffineSpace (ULift.{u} (Fin 1)) Y ↘ S) :=
  affineSpace_over_quasiCompact

/-- The canonical separated instance for the relative affine line.
Source: blueprint thm-pur-finite-reduction-of-purity, affine-orientation setup
(blueprint: def-pur-finite-affine-orientation-comparison). -/
noncomputable instance affineSpace_over_isSeparated_inst {S Y : Scheme.{u}}
    [Y.Over S] [IsSeparated (Y ↘ S)] :
    IsSeparated (AffineSpace (ULift.{u} (Fin 1)) Y ↘ S) :=
  affineSpace_over_isSeparated


/-- The zero section is over its own base, by the existing section equation.
Source: AffineSpace.zeroSection_comp_over; blueprint affine-orientation setup
(blueprint: def-pur-finite-affine-orientation-comparison). -/
instance finiteReductionZeroSectionOverBase (Y : Scheme.{u}) :
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).IsOver Y :=
  ⟨AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y⟩

/-- The zero section remains over a base of its base, using the canonical tower.
Source: CategoryTheory.homIsOver_of_isOverTower; blueprint affine-orientation setup
(blueprint: def-pur-finite-affine-orientation-comparison). -/
instance finiteReductionZeroSectionOver {S Y : Scheme.{u}} [Y.Over S] :
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).IsOver S :=
  CategoryTheory.homIsOver_of_isOverTower
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y) Y S

/-- The zero section of the relative line is the effective Cartier divisor t = 0.
Source: Stacks 01WQ and blueprint Step 3
(blueprint: def-pur-finite-affine-orientation-comparison).
Proof: on each affine base chart the ideal is (t) in R[t]. Multiplication by t is
injective even when R has zero divisors. The generator identifies this ideal with
R[t]; these identifications are compatible with base localization and glue. -/
theorem finiteReductionZeroCartier (Y : Scheme.{u}) :
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).ker.IsInvertible := by
  sorry

/-- The affine-line orientation has its actual supported relative Kummer boundary.
The uniqueness clause is the relative boundary characterization, rather than a
choice among generators of a rank-one module.
Source: Stacks 03PL, 0A45; blueprint Step 3
(blueprint: def-pur-finite-affine-orientation-comparison).
Proof: apply ordinary_supported_kummer to the zero Cartier divisor. Its relative
frame torsor is the torsor trivialized by t off zero; the relative Kummer boundary
therefore is precisely the coordinate boundary. The boundary uniqueness clause
of that theorem gives uniqueness here, for the annihilator ell^n at every
positive n, including ramified levels not divisible by the ramification index. -/
theorem existsUnique_finiteReductionOrientationClass (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))] :
    ∃! κ : CategoryTheory.Abelian.Ext
        ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj
            (Etale.ordinaryFiniteConstant P.Coefficient Y))
        (Scheme.finiteEtaleTateLine (AffineSpace (ULift.{u} (Fin 1)) Y)
          P.diagonalExponent P.Coefficient P.diagonalExponent_annihilates) 2,
      Etale.SupportedKummerBoundary P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)
        (finiteReductionZeroCartier Y)
        (P.diagonalExponent_isUnit
          (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Spec (.of P.field.k))) κ := by
  sorry

/-- Ordinary affine-line orientation, as the exceptional adjunct of the supported
coordinate boundary. Source: blueprint Step 3; Stacks 03PL, 0A45
(blueprint: def-pur-finite-affine-orientation-comparison). -/
def finiteReductionEtaleOrientation (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))] :
    Etale.ordinaryFiniteUnit P.Coefficient Y ⟶
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj
          ((Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates
            (AffineSpace (ULift.{u} (Fin 1)) Y))⟦(2 : ℤ)⟧) :=
  let s := AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y
  ((Etale.rightDerivedUpperShriekAdjunction
    (ModuleCat.{u + 1} P.Coefficient) s).homEquiv _ _)
      (((Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} P.Coefficient) s).app
            (Etale.ordinaryFiniteUnit P.Coefficient Y)).hom ≫
        Etale.supportedExactDerivedMap
          (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) s)
          (Etale.ordinaryFiniteConstant P.Coefficient Y)
          (Scheme.finiteEtaleTateLine (AffineSpace (ULift.{u} (Fin 1)) Y)
            P.diagonalExponent P.Coefficient P.diagonalExponent_annihilates)
          (P.existsUnique_finiteReductionOrientationClass Y).choose)

/-- The intrinsic affine-line coefficient A(1)[2], using the ordinary root line.
Source: blueprint orientation clause (blueprint: def-pur-finite-affine-orientation-comparison). -/
def finiteReductionOrientationInput (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    Scheme.proEtaleDerivedCategory (AffineSpace (ULift.{u} (Fin 1)) Y) P.Ring :=
  (Scheme.sfIntrinsicDerivedEquivalence (AffineSpace (ULift.{u} (Fin 1)) Y) P.Ring).functor.obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace (ULift.{u} (Fin 1)) Y)).mapDerivedCategory.obj
          ((Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates (AffineSpace (ULift.{u} (Fin 1)) Y))⟦(2 : ℤ)⟧))

/-- Transport the Kummer-defined ordinary orientation through the very same
comparison adjunction and realization equivalence used by the exceptional functor.
Source: blueprint Step 3; finite exceptional conventions
(blueprint: def-pur-finite-affine-orientation-comparison). -/
def finiteReductionOrientation (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))] :
    P.coefficientUnit Y ⟶
      (P.compositionExceptional (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj
      (P.finiteReductionOrientationInput Y) :=
  let L := AffineSpace (ULift.{u} (Fin 1)) Y
  let s := AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y
  letI := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring L
  let E := Scheme.sfIntrinsicDerivedEquivalence L P.Ring
  let V := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory
  let K₀ := (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates L)⟦(2 : ℤ)⟧
  let K := P.finiteReductionOrientationInput Y
  (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.map
    (V.map (P.finiteReductionEtaleOrientation Y) ≫
      V.map ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) s).map
        ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) L).unit.app K₀ ≫
          (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) L).rightDerivedFunctor.map
              (E.unitIso.app
                ((ProEtale.comparisonUpperStar
                  (ModuleCat.{u + 1} P.Coefficient) L).mapDerivedCategory.obj K₀)).hom)) ≫
      ((P.smoothPurityExceptionalComparison s).app (E.inverse.obj K)).inv)


/-- The root chart of the shifted affine-line coefficient input is the actual
section-normalized root-line chart, mapped through comparison inverse image and
intrinsic realization with their canonical shifts.
Source: blueprint reduction Step 1; Stacks 03PK
(blueprint: def-pur-finite-affine-orientation-comparison). -/
def finiteReductionOrientationInputChart (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    P.finiteReductionOrientationInput Y ≅
      (P.coefficientUnit (AffineSpace (ULift.{u} (Fin 1)) Y))⟦(2 : ℤ)⟧ :=
  let L := AffineSpace (ULift.{u} (Fin 1)) Y
  letI := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring L
  let F := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) L).mapDerivedCategory
  let E := (Scheme.sfIntrinsicModuleEquivalence L P.Ring).functor.mapDerivedCategory
  E.mapIso (F.mapIso (P.finiteReductionShiftedLineChart L ζ hζ) ≪≫
    (F.commShiftIso (2 : ℤ)).app (Etale.ordinaryFiniteUnit P.Coefficient L)) ≪≫
    (E.commShiftIso (2 : ℤ)).app (F.obj (Etale.ordinaryFiniteUnit P.Coefficient L))

/-- The affine-line input comparison is fixed in every pair of compatible root charts.
Source: blueprint Step 3, reduction of the Kummer line
(blueprint: def-pur-finite-affine-orientation-comparison).
Proof: use primitive roots of orders ell^n and ell^m related by the indicated
power map. Tensoring a root-line generator with the smaller coefficient ring
sends it to that generator; the shifted scalar-unit adjunct therefore gives an
isomorphism between the displayed objects. Changing the primitive root rescales
both sides by the same coefficient unit. The resulting isomorphism is independent
of the chart and satisfies every displayed equation, which also proves uniqueness. -/
theorem existsUnique_finiteReductionOrientationInputComparison
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))] :
    ∃! e : (P.finiteReduction m hm hmn (AffineSpace (ULift.{u} (Fin 1)) Y)).obj
        (P.finiteReductionOrientationInput Y) ≅
      (P.finiteReductionSetting m hm).finiteReductionOrientationInput Y,
      ∀ (ζ η : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
        (hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent),
        η = ζ ^ (P.coefficients.l ^ (P.level - m)) →
        e.hom ≫ ((P.finiteReductionSetting m hm).finiteReductionOrientationInputChart Y η hη).hom =
        (P.finiteReduction m hm hmn (AffineSpace (ULift.{u} (Fin 1)) Y)).map
          (P.finiteReductionOrientationInputChart Y ζ hζ).hom ≫
        ((P.finiteReduction m hm hmn (AffineSpace (ULift.{u} (Fin 1)) Y)).commShiftIso
          (2 : ℤ)).hom.app _ ≫
        (P.finiteReductionUnitComparison m hm hmn
          (AffineSpace (ULift.{u} (Fin 1)) Y))⟦(2 : ℤ)⟧' := by
  sorry

/-- The root-normalized reduction of the coefficient input to the zero-section adjoint.
Source: blueprint Step 3
(blueprint: def-pur-finite-affine-orientation-comparison). -/
def finiteReductionOrientationInputComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))] :
    (P.finiteReduction m hm hmn (AffineSpace (ULift.{u} (Fin 1)) Y)).obj
        (P.finiteReductionOrientationInput Y) ≅
      (P.finiteReductionSetting m hm).finiteReductionOrientationInput Y :=
  (P.existsUnique_finiteReductionOrientationInputComparison m hm hmn Y).choose

/-- The closed zero-section exceptional comparison is uniquely counit-normalized.
Source: blueprint Step 3, supported adjoint and coefficient comparison
(blueprint: def-pur-finite-affine-orientation-comparison).
Proof: the coefficient line is finite locally free of rank one and the zero
section is a regular Cartier immersion. Closed purity gives the bounded
constructible finite-Tor exceptional value. The compact-support coefficient mate
is invertible there. Transpose the reduced counit through that inverse and the
standing exceptional adjunction. Its Hom bijection proves existence and uniqueness. -/
theorem existsUnique_finiteReductionOrientationExceptionalComparison
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))] :
    ∃! b : (P.finiteReduction m hm hmn Y).obj
        ((P.compositionExceptional (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj
          (P.finiteReductionOrientationInput Y)) ⟶
      ((P.finiteReductionSetting m hm).compositionExceptional
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj
          ((P.finiteReduction m hm hmn (AffineSpace (ULift.{u} (Fin 1)) Y)).obj
            (P.finiteReductionOrientationInput Y)),
      P.finiteReductionCompactSupportComparison m hm hmn
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)
          ((P.compositionExceptional (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj
            (P.finiteReductionOrientationInput Y)) ≫
        ((P.finiteReductionSetting m hm).smoothCompactSupport
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).map b ≫
        (P.finiteReductionSetting m hm).smoothExceptionalCounit
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)
          ((P.finiteReduction m hm hmn (AffineSpace (ULift.{u} (Fin 1)) Y)).obj
            (P.finiteReductionOrientationInput Y)) =
      (P.finiteReduction m hm hmn (AffineSpace (ULift.{u} (Fin 1)) Y)).map
        (P.smoothExceptionalCounit (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)
          (P.finiteReductionOrientationInput Y)) := by
  sorry

/-- The specified zero-section coefficient comparison, determined without an orientation.
Source: blueprint Step 3
(blueprint: def-pur-finite-affine-orientation-comparison). -/
def finiteReductionOrientationExceptionalComparison
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))] :
    (P.finiteReduction m hm hmn Y).obj
        ((P.compositionExceptional (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj
          (P.finiteReductionOrientationInput Y)) ⟶
      ((P.finiteReductionSetting m hm).compositionExceptional
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj
          ((P.finiteReduction m hm hmn (AffineSpace (ULift.{u} (Fin 1)) Y)).obj
            (P.finiteReductionOrientationInput Y)) :=
  (P.existsUnique_finiteReductionOrientationExceptionalComparison m hm hmn Y).choose

/-- The canonical zero-section exceptional coefficient map is an isomorphism.
Source: blueprint Step 3, finite exceptional compatibility for the zero section
(blueprint: def-pur-finite-affine-orientation-comparison).
Proof: closed purity identifies the shifted rank-one coefficient input's
exceptional value with the degree-zero coefficient unit. Its scalar reduction is
the ordinary rank-one balancing isomorphism. Transposing that computation through
the compact-support adjunction gives precisely the counit normalization above.
Uniqueness identifies the specified comparison with this isomorphism. -/
theorem finiteReductionOrientationExceptionalComparison_isIso
    (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))] :
    IsIso (P.finiteReductionOrientationExceptionalComparison m hm hmn Y) := by
  sorry

end WeilConjectures.PurityFiniteSetting
