/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientCohomologyComparison
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientShiftedTateComparison

/-! # Coefficient-stage vanishing for smooth exceptional constants

This is the coefficient-level geometric input used by the native Weil-sheaf
vanishing theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures WeilConjectures.ConstantPurityFrobenius

attribute [local instance 1100] CategoryTheory.instOverClass

private theorem coefficient_smooth_purity_iso (P : PurityFiniteSetting.{u})
    (X₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (c₀ : Compactification X₀.hom)
    (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)
    (d : ℕ) [SmoothOfRelativeDimension d X₀.hom] :
    Nonempty (NativeCoefficientCohomology.twistedConstant P X₀ d ≅
      NativeCoefficientCohomology.exceptionalConstant P X₀ c₀ S) := by
  let D := P.field
  let l := P.coefficients.l
  let hl := P.coefficients.different
  let Ω := P.coefficients.Qbar
  let Y₀ := point D
  let f₀ := pointMap D X₀
  let : LocallyOfFiniteType Y₀.hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k₀))))
  let : QuasiCompact Y₀.hom := inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))
  let : IsSeparated Y₀.hom := inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k₀))))
  let : SmoothOfRelativeDimension d f₀.left :=
    inferInstanceAs (SmoothOfRelativeDimension d X₀.hom)
  let : IsSeparated f₀.left := inferInstanceAs (IsSeparated X₀.hom)
  let : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType X₀.hom)
  let : QuasiCompact f₀.left := inferInstanceAs (QuasiCompact X₀.hom)
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).1
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).2
  let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).1
  let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).2
  let : IsSeparated ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    MorphismProperty.baseChange_obj (P := @IsSeparated) _ X₀ inferInstance
  let : IsSeparated ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    MorphismProperty.baseChange_obj (P := @IsSeparated) _ Y₀ inferInstance
  let : (FrobeniusExchange.fiberMap D f₀).IsOver (Spec (.of D.k)) :=
    zlFiberMap_isOver D f₀
  let : IsSeparated (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).1
  let : LocallyOfFiniteType (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).2.1
  let : QuasiCompact (FrobeniusExchange.fiberMap D f₀) :=
    (FrobeniusExchange.fiberMap_properties D f₀).2.2
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension d) :=
    smoothOfRelativeDimension_isStableUnderBaseChange d
  let : SmoothOfRelativeDimension d (FrobeniusExchange.fiberMap D f₀) :=
    MorphismProperty.overPullbackMap (P := @SmoothOfRelativeDimension d)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  let K := unit D l hl Ω (D.geometricFiber Y₀).left
  let γ := @RationalSmoothPurityCanonical.commonIso P
    (D.geometricFiber X₀).left (D.geometricFiber Y₀).left inferInstance inferInstance
    (FrobeniusExchange.fiber_finiteType D X₀).1
    (FrobeniusExchange.fiber_finiteType D X₀).2
    (MorphismProperty.baseChange_obj (P := @IsSeparated) _ X₀ inferInstance)
    (FrobeniusExchange.fiber_finiteType D Y₀).1
    (FrobeniusExchange.fiber_finiteType D Y₀).2
    (MorphismProperty.baseChange_obj (P := @IsSeparated) _ Y₀ inferInstance)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y)
    (FrobeniusExchange.fiberMap D f₀) (zlFiberMap_isOver D f₀)
    (FrobeniusExchange.fiberMap_properties D f₀).1
    (FrobeniusExchange.fiberMap_properties D f₀).2.1
    (FrobeniusExchange.fiberMap_properties D f₀).2.2
    (FrobeniusExchange.geometricCompactification D f₀ c₀) S d inferInstance K
  refine ⟨Endofunctor.IsoAlgebra.isoMk γ ?_⟩
  simpa only [NativeCoefficientCohomology.twistedConstant,
    NativeCoefficientCohomology.exceptionalConstant, Endofunctor.IsoAlgebra.mk,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, γ, D, l, hl, Ω, Y₀, f₀, K,
    Category.assoc] using
    (constant_purity_frobenius_square P X₀ c₀ S d).2.2

namespace WeilConjectures.NativeCoefficientCohomology

variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (c₀ : Compactification X₀.hom)
  (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)
  [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)]

local instance smoothNativeStructureOver : X₀.hom.IsOver (Spec (.of P.field.k₀)) := by
  constructor
  dsimp only [autoParam]
  change X₀.hom ≫ 𝟙 _ = X₀.hom
  rw [Category.comp_id]

set_option linter.unusedVariables false in
/-- The coefficient exceptional constant has no cohomology outside `-2d`.

Source: current blueprint,
`cor-pur-adic-and-rational-smooth-dualizing-complexes`, smooth specialization.
(blueprint: lem-sf-weil-smooth-coefficient-exceptional-vanishing)

Proof: apply the coefficient-stage smooth-purity isomorphism to the structure
morphism and the coefficient unit.  The resulting exceptional object is
isomorphic to the coefficient constant Tate line shifted by `2d`; the standard
cohomology computation for a shifted single complex gives zero in every other
degree.  The same normalized comparison family is used in every degree and is
compatible with the native comparison family supplied by
`coefficient_cohomology_comparison`.
-/
theorem smooth_coefficient_exceptional_vanishing
    (d : ℕ) [SmoothOfRelativeDimension d X₀.hom] :
    ∃ C : ℤ → (Pairs P X₀ ⥤ WeilSheaf P.field.k₀ P.coefficients.l X₀.left),
      (∀ (J : WeilComplex P.field.k₀ P.coefficients.l
          (Spec (.of P.field.k₀)) ⥤ WeilComplex P.field.k₀ P.coefficients.l X₀.left)
        (adj : WeilComplex.derivedLowerShriek P.field.k₀ P.coefficients.l X₀.hom ⊣ J)
        (n : ℤ),
        Nonempty ((WeilComplex.homologySheaf n).obj
            (J.obj (WeilSheaf.toComplex.obj
              (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l
                (Spec (.of P.field.k₀))))) ≅
          (C n).obj (exceptionalConstant P X₀ c₀ S))) ∧
      (∀ n : ℤ, n ≠ -2 * (d : ℤ) →
        IsZero ((C n).obj (exceptionalConstant P X₀ c₀ S))) := by
  obtain ⟨C, hcomp, htate⟩ := coefficient_shifted_tate_comparison P X₀ c₀ S
  obtain ⟨e⟩ := coefficient_smooth_purity_iso P X₀ c₀ S d
  refine ⟨C, hcomp, ?_⟩
  intro n hn
  apply IsZero.of_iso (Y := (C n).obj (twistedConstant P X₀ d))
  · obtain ⟨t⟩ := htate d n
    exact (WeilSheaf.isZero_homologySheaf_shift_toComplex _ (by omega)).of_iso t
  · exact (C n).mapIso e.symm

end WeilConjectures.NativeCoefficientCohomology
