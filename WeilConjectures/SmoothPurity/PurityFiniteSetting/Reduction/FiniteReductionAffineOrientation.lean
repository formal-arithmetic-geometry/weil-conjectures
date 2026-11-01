/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionLineChartScalars
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptional
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionLineInputConstructible
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts

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
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/- Compose the existing affine-space projection instances with the base map. -/
/-- Relative affine space is locally of finite type over a locally finite-type base.
Proof: over Spec R its coordinate algebra is the polynomial algebra R[t], generated
by t over R. Compose these locally finite-type affine charts with the base map.
Source: blueprint thm-pur-finite-reduction-of-purity, affine-orientation setup
(blueprint: def-pur-finite-affine-orientation-comparison). -/
theorem affineSpace_over_locallyOfFiniteType {S Y : Scheme.{u}}
    [Y.Over S] [LocallyOfFiniteType (Y ↘ S)] :
    LocallyOfFiniteType (AffineSpace (ULift.{u} (Fin 1)) Y ↘ S) := by
  change LocallyOfFiniteType ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ S))
  infer_instance

/-- Relative affine space is quasi-compact over a quasi-compact base morphism.
Proof: the inverse image of an affine base chart is its affine polynomial spectrum,
so the projection is quasi-compact. Quasi-compact morphisms are closed under composition.
Source: blueprint thm-pur-finite-reduction-of-purity, affine-orientation setup
(blueprint: def-pur-finite-affine-orientation-comparison). -/
theorem affineSpace_over_quasiCompact {S Y : Scheme.{u}}
    [Y.Over S] [QuasiCompact (Y ↘ S)] :
    QuasiCompact (AffineSpace (ULift.{u} (Fin 1)) Y ↘ S) := by
  change QuasiCompact ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ S))
  infer_instance

/-- Relative affine space is separated over a separated base morphism.
Proof: on a polynomial chart its diagonal is the closed immersion cut out by t1-t2.
The projection is separated, and composing separated morphisms preserves separatedness.
Source: blueprint thm-pur-finite-reduction-of-purity, affine-orientation setup
(blueprint: def-pur-finite-affine-orientation-comparison). -/
theorem affineSpace_over_isSeparated {S Y : Scheme.{u}}
    [Y.Over S] [IsSeparated (Y ↘ S)] :
    IsSeparated (AffineSpace (ULift.{u} (Fin 1)) Y ↘ S) := by
  change IsSeparated ((AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y) ≫ (Y ↘ S))
  infer_instance

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
Source: Stacks 0B9D, the Cartier criterion, and blueprint Step 3
(blueprint: def-pur-finite-affine-orientation-comparison).
Proof: the affine line is smooth of relative dimension one. The zero section is
a closed immersion, canonically isomorphic to the closed subscheme of its kernel.
The projection of that subscheme to Y is inverse to this isomorphism, by the
section equation. It is therefore finite, flat and locally of finite presentation.
The Cartier criterion makes its defining ideal invertible, over arbitrary Y. -/
theorem finiteReductionZeroCartier (Y : Scheme.{u}) :
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).ker.IsInvertible := by
  let p : AffineSpace (ULift.{u} (Fin 1)) Y ⟶ Y :=
    AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y
  have : SmoothOfRelativeDimension 1 p := by
    simpa only [Nat.card_ulift, Nat.card_fin] using
      AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin 1)) Y
  let s := AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y
  have hs : s ≫ p = 𝟙 Y := AffineSpace.zeroSection_comp_over _ _
  let l := IsClosedImmersion.lift s s.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι s.ker).ge
  have : IsIso l := IsClosedImmersion.isIso_lift s s.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι s.ker).symm
  have hl : s.ker.subschemeι ≫ p = l := by
    rw [← IsClosedImmersion.lift_fac s s.ker.subschemeι
      (Scheme.IdealSheafData.ker_subschemeι s.ker).ge, Category.assoc, hs,
      Category.comp_id]
  have : IsIso (s.ker.subschemeι ≫ p) := hl ▸ inferInstance
  exact Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat p
    inferInstance inferInstance inferInstance

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
  exact Etale.ordinary_supported_kummer_uniqueBoundary
    (AffineSpace (ULift.{u} (Fin 1)) Y) P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) P.Coefficient
    P.diagonalExponent_annihilates
    (P.diagonalExponent_isUnit
      (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Spec (.of P.field.k)))
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y) (finiteReductionZeroCartier Y)

section EtaleOrientation
-- Reuse the category instances in the ordinary derived category throughout the adjunct.
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] PurityFiniteSetting.Ring PurityFiniteSetting.Coefficient

/-- The exceptional adjunct of an ordinary supported degree-two class.
This is the same direct-image comparison and exact Ext realization used by the affine
orientation, with the coefficient ring and immersion kept as parameters.
Source: blueprint Step 3, supported Kummer orientation
(blueprint: def-pur-finite-affine-orientation-comparison). -/
def finiteReductionSupportedOrientationAdjunct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    [CategoryTheory.HasExt.{u + 1}
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))]
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (κ : CategoryTheory.Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
        (Etale.ordinaryFiniteConstant A D)) M 2) :
    Etale.ordinaryFiniteUnit A D ⟶
      (Etale.rightDerivedUpperShriek A i).obj
        (((_root_.DerivedCategory.singleFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj M)⟦(2 : ℤ)⟧) :=
  ((Etale.rightDerivedUpperShriekAdjunction
    A i).homEquiv _ _)
      (((Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
          (ModuleCat.{u + 1} A) i).app
            (Etale.ordinaryFiniteUnit A D)).hom ≫
        Etale.supportedExactDerivedMap (Etale.lowerStar (ModuleCat.{u + 1} A) i)
          (Etale.ordinaryFiniteConstant A D) M κ)

/-- Ordinary affine-line orientation, as the exceptional adjunct of the supported
coordinate boundary. Source: blueprint Step 3; Stacks 03PL, 0A45
(blueprint: def-pur-finite-affine-orientation-comparison). -/
def finiteReductionEtaleOrientation (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [Y.Over (Spec (.of P.field.k))] :
    Etale.ordinaryFiniteUnit P.Coefficient Y ⟶
      (Etale.rightDerivedUpperShriek P.Coefficient
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)).obj
          ((Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates
            (AffineSpace (ULift.{u} (Fin 1)) Y))⟦(2 : ℤ)⟧) :=
  finiteReductionSupportedOrientationAdjunct P.Coefficient
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y)
    (Scheme.finiteEtaleTateLine (AffineSpace (ULift.{u} (Fin 1)) Y)
      P.diagonalExponent P.Coefficient P.diagonalExponent_annihilates)
    (P.existsUnique_finiteReductionOrientationClass Y).choose

end EtaleOrientation

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
      V.map ((Etale.rightDerivedUpperShriek P.Coefficient s).map
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
  P.finiteReductionLineChart (AffineSpace (ULift.{u} (Fin 1)) Y) ζ hζ

private theorem comparisonOfCharts
    {C : Type v} [Category C] {D : Type w} [Category D]
    (F : C ⥤ D) {L U : C} {L' U' : D} {I J : Type*}
    (c : I → (L ≅ U)) (d : J → (L' ≅ U')) (a : F.obj U ≅ U')
    (r : I → J → Prop) (i : I) (j : J) (hij : r i j)
    (h : ∀ i' j', r i' j' →
      F.map ((c i).inv ≫ (c i').hom) ≫ a.hom =
        a.hom ≫ (d j).inv ≫ (d j').hom) :
    ∃! e : F.obj L ≅ L', ∀ i' j', r i' j' →
      e.hom ≫ (d j').hom = F.map (c i').hom ≫ a.hom := by
  let e := F.mapIso (c i) ≪≫ a ≪≫ (d j).symm
  have he (i' : I) (j' : J) (hr : r i' j') :
      e.hom ≫ (d j').hom = F.map (c i').hom ≫ a.hom := by
    calc
      _ = F.map (c i).hom ≫ (a.hom ≫ (d j).inv ≫ (d j').hom) := by
        simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
      _ = F.map (c i).hom ≫ (F.map ((c i).inv ≫ (c i').hom) ≫ a.hom) := by
        rw [h i' j' hr]
      _ = _ := by
        simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Category.id_comp]
  refine ⟨e, he, ?_⟩
  intro t ht
  apply Iso.ext
  apply (cancel_mono (d j).hom).1
  exact (ht i j hij).trans (he i j hij).symm

section InputComparison
-- Match the category-instance proofs cached by the ordinary derived module category.
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] PurityFiniteSetting.Ring PurityFiniteSetting.Coefficient

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
  have hl : (P.coefficients.l : P.field.k) ≠ 0 := by
    let : Fintype P.field.k₀ := Fintype.ofFinite _
    have : Fact P.field.p.Prime := ⟨P.field.prime⟩
    have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (by
      rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq])
    have : CharP P.field.k P.field.p :=
      charP_of_injective_algebraMap' P.field.k₀ P.field.p
    exact CharP.cast_ne_zero_of_ne_of_prime _
      (Fact.out : P.coefficients.l.Prime) P.coefficients.different.symm
  have : NeZero (P.diagonalExponent : P.field.k) := ⟨by
    change ((P.coefficients.l ^ P.level : ℕ) : P.field.k) ≠ 0
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot P.field.k P.diagonalExponent
  let η := ζ ^ (P.coefficients.l ^ (P.level - m))
  have hη : IsPrimitiveRoot η (P.finiteReductionSetting m hm).diagonalExponent := by
    apply hζ.pow (NeZero.pos P.diagonalExponent)
    change P.coefficients.l ^ P.level =
      P.coefficients.l ^ (P.level - m) * P.coefficients.l ^ m
    rw [← pow_add, Nat.sub_add_cancel hmn]
  let T := AffineSpace (ULift.{u} (Fin 1)) Y
  let R := P.finiteReduction m hm hmn T
  let Q := P.finiteReductionSetting m hm
  let := P.finiteReductionUnitComparison_isIso m hm hmn T
  let a := (R.commShiftIso (2 : ℤ)).app (P.coefficientUnit T) ≪≫
    (shiftFunctor (Scheme.proEtaleDerivedCategory T Q.Ring) (2 : ℤ)).mapIso
      (asIso (P.finiteReductionUnitComparison m hm hmn T))
  let I := {z : P.field.k // IsPrimitiveRoot z P.diagonalExponent}
  let J := {z : P.field.k // IsPrimitiveRoot z Q.diagonalExponent}
  let c (z : I) := P.finiteReductionOrientationInputChart Y z.val z.property
  let d (z : J) := Q.finiteReductionOrientationInputChart Y z.val z.property
  let r (z : I) (w : J) := w.val = z.val ^ (P.coefficients.l ^ (P.level - m))
  obtain ⟨e, he, hu⟩ := comparisonOfCharts R c d a r ⟨ζ, hζ⟩ ⟨η, hη⟩ rfl
    (fun z w hr ↦ P.finiteReductionLineChart_scalars m hm hmn T a.hom
      ζ η z.val w.val hζ hη z.property w.property rfl hr)
  refine ⟨e, ?_, ?_⟩
  · intro z w hz hw hr
    exact he ⟨z, hz⟩ ⟨w, hw⟩ hr
  · intro t ht
    exact hu t (fun z w hr ↦ ht z.val w.val z.property w.property hr)

end InputComparison

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

set_option backward.isDefEq.respectTransparency true
private theorem exceptional_ctf (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos X
      ((P.compositionExceptional f).obj K) := by
  let := hasCompactification_of_finiteType_over_field P.field.k X Y f
  let c := HasCompactification.compactification f
  have h (r : ℕ) (hr : 1 ≤ r) :
      letI := Padic.finite_coefficientExtensionRing P.coefficients.l P.extension r hr
      ∀ L : (finiteTorConstructible P.coefficients.l P.extension r hr Y).FullSubcategory,
        finiteTorConstructible P.coefficients.l P.extension r hr X
          ((ProEtale.sfFiniteExceptional
            (Padic.coefficientExtensionRing P.coefficients.l P.extension r) c).obj L.obj) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hr)
    exact (FiniteExceptional.operations_preserve P.coefficients.l P.extension P.field
      P.coefficients.different f c n).2
  have hL := h P.level P.level_pos ⟨K, hK⟩
  exact hL

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
  let Q := P.finiteReductionSetting m hm
  let T := AffineSpace (ULift.{u} (Fin 1)) Y
  let s := AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y
  let K := P.finiteReductionOrientationInput Y
  let L := (P.compositionExceptional s).obj K
  have hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos T K :=
    P.finiteReductionLineInput_constructible T
  have hL := exceptional_ctf P s K hK
  let := P.finiteReductionCompactSupportComparison_isIso m hm hmn s L hL
  have hbij := finiteReduction_counit_bijective_public Q s
    ((P.finiteReduction m hm hmn Y).obj L)
    (P.finiteReduction_preserves_ctf m hm hmn Y L hL)
    ((P.finiteReduction m hm hmn T).obj K)
    (P.finiteReduction_preserves_ctf m hm hmn T K hK)
  let a := P.finiteReductionCompactSupportComparison m hm hmn s L
  let t := (P.finiteReduction m hm hmn T).map (P.smoothExceptionalCounit s K)
  obtain ⟨b, hb⟩ := hbij.2 (inv a ≫ t)
  dsimp only at hb
  have hb_norm : a ≫ ((Q.smoothCompactSupport s).map b ≫
      Q.smoothExceptionalCounit s ((P.finiteReduction m hm hmn T).obj K)) = t := by
    rw [hb]
    exact IsIso.hom_inv_id_assoc a t
  refine ⟨b, hb_norm, ?_⟩
  intro b' hb'
  apply hbij.1
  apply (cancel_epi a).1
  exact hb'.trans hb_norm.symm

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

end WeilConjectures.PurityFiniteSetting
