/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral

/-! # Derived reduction and restriction of scalars

Source: Stacks Project, Tags 07A6, 06YY, 03CZ, 09T5 and 0DVC;
blueprint `def-weil-derived-direct-image`, order 1468
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction).

The index n denotes exponent n+1. All constructions use the completed coefficient
sheaf, with no auxiliary finite-field datum or restriction on the characteristic of Y.
The derived adjunction is normalized by its unit on every K-flat representative.
-/

@[expose] public section

set_option autoImplicit false

universe t u

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

/-- Modules over the completed coefficient ring, without a finite-field convention.
Source: Stacks Tag 06YY
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable abbrev scalarReductionSource :=
  SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y))

/-- Modules over the constant finite quotient ring at exponent n+1.
Source: Stacks Tag 06YY
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable abbrev scalarReductionTarget (n : ℕ) :=
  SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n)

/-- The standard localization of completed-coefficient module complexes.
Source: Stacks Tag 05RU
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable instance scalarReductionSourceDerived :
    HasDerivedCategory (scalarReductionSource l E Y) := HasDerivedCategory.standard _

/-- The standard localization of finite-coefficient module complexes.
Source: Stacks Tag 05RU
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable instance scalarReductionTargetDerived (n : ℕ) :
    HasDerivedCategory (scalarReductionTarget l E Y n) := HasDerivedCategory.standard _

/-- The site fits in the chosen module universe via its standard small model.
Source: blueprint small-site convention
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable instance scalarReductionSiteSmall :
    EssentiallySmall.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt Y) :=
  essentiallySmallSelf _

variable (n : ℕ)

/-- Restriction along the coordinate projection of the completed ring sheaf.
Source: Stacks Tag 03CZ
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable abbrev scalarReductionRestriction :
    scalarReductionTarget l E Y n ⥤ scalarReductionSource l E Y :=
  SheafOfModules.restrictScalars
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (completedIntegralCommRingProjectionUnrestricted l E Y n))

/-- Restriction is exact, since it leaves underlying abelian sheaves unchanged.
Source: Stacks Tags 03DA and 03CZ
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction).
Proof: a kernel is the same sectionwise kernel with restricted action. A cokernel
is the sheafification of the same sectionwise abelian-group quotient in both
module categories; its action is precomposed with the coefficient projection.
Thus restriction preserves kernels and cokernels and is additive, hence exact. -/
theorem scalarReductionRestriction_exact :
    PreservesFiniteLimits (scalarReductionRestriction l E Y n) ∧
      PreservesFiniteColimits (scalarReductionRestriction l E Y n) := by
  sorry

/-- Finite-limit preservation supplied by exactness.
Source: Stacks Tag 03DA
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable instance scalarReductionRestrictionLimits :
    PreservesFiniteLimits (scalarReductionRestriction l E Y n) :=
  (scalarReductionRestriction_exact l E Y n).1

/-- Finite-colimit preservation supplied by exactness.
Source: Stacks Tag 03DA
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable instance scalarReductionRestrictionColimits :
    PreservesFiniteColimits (scalarReductionRestriction l E Y n) :=
  (scalarReductionRestriction_exact l E Y n).2

/-- Termwise exact restriction descended through localization.
Source: Stacks Tag 015F
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable def scalarReductionDerivedRestriction :=
  (scalarReductionRestriction l E Y n).mapDerivedCategory

set_option linter.defProp false in
/-- The canonical universal derived-change-of-rings witness for the limit projection.
Source: Stacks Tag 06YY
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable def scalarReductionExistence :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)))
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (O := completedIntegralCommRingSheafUnrestricted l E Y)
    (O' := integralCoefficientCommRingSheaf l E Y n)
    (completedIntegralCommRingProjectionUnrestricted l E Y n)

/-- Ordinary scalar extension, with the sectionwise tensor objects and maps fixed
by the derived-change-of-rings witness.
Source: Stacks Tag 06YY
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable def scalarReductionExtension :
    scalarReductionSource l E Y ⥤ scalarReductionTarget l E Y n :=
  (scalarReductionExistence l E Y n).choose

/-- Additivity of tensor extension.
Source: Stacks Tag 06YY
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable instance scalarReductionExtensionAdditive :
    (scalarReductionExtension l E Y n).Additive :=
  (scalarReductionExistence l E Y n).choose_spec.choose_spec.choose_spec.choose

set_option linter.defProp false in
/-- The universal derived pair, including the K-flat computation and exactness.
Source: Stacks Tag 06YY
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable def scalarReductionDerivedExistence :=
  (scalarReductionExistence l E Y n).choose_spec.choose_spec.choose_spec.choose_spec.2.2

/-- Derived tensor with the finite quotient over the completed coefficient ring.
Its universal property determines it up to unique compatible isomorphism.
Source: Stacks Tag 06YY
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable def scalarReductionDerivedExtension :
    DerivedCategory (scalarReductionSource l E Y) ⥤
      DerivedCategory (scalarReductionTarget l E Y n) :=
  (scalarReductionDerivedExistence l E Y n).choose

/-- The universal comparison on homotopy complexes, an isomorphism on K-flat ones.
Source: Stacks Tag 06YY
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction). -/
noncomputable def scalarReductionCounit :
    DerivedCategory.Qh ⋙ scalarReductionDerivedExtension l E Y n ⟶
      (scalarReductionExtension l E Y n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  (scalarReductionDerivedExistence l E Y n).choose_spec.choose

/-- The underived tensor/restriction adjunction with its sectionwise unit normalization.
Source: Stacks Tag 03CZ
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction).
Proof: send a tensor-linear map v to x ↦ v(1 tensor x), and send w to
s tensor x ↦ s w(x). Balancing and restriction compatibility descend both maps
through sheafification. Their composites are identities on tensor generators.
Consequently the unit is precisely the image of 1 tensor x in the sheafification. -/
theorem scalarReductionExtension_adjunction :
    ∃ adj : scalarReductionExtension l E Y n ⊣ scalarReductionRestriction l E Y n,
      ∀ (M : scalarReductionSource l E Y)
        (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) (x : M.val.obj U),
        (adj.unit.app M).val.app U x =
          (eqToHom ((scalarReductionExistence l E Y n).choose_spec.choose M).symm).val.app U
            (((PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
              (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
              (R := integralCoefficientSheaf l E Y n)
              (𝟙 (integralCoefficientSheaf l E Y n).obj)).unit.app
              (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)}
                (completedIntegralCommRingProjectionUnrestricted l E Y n) M)).app U
              ((ModuleCat.extendRestrictScalarsAdj
                ((completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U).hom).unit.app
                  (M.val.obj U) x)) := by
  sorry

/-- Derived scalar extension is left adjoint to exact restriction, and its unit is
induced by the completed coefficient projection on every K-flat representative.
Source: Stacks Tags 07A6, 06YY, 09T5 and 0DVC
(blueprint: lem-weil-derived-scalar-extension-restriction-adjunction).
Proof:
1. Apply the same-site tensor/restriction adjunction, whose unit is x ↦ 1 tensor x.
2. Restriction is exact: it changes only scalar actions and preserves the same kernels
and sheafified cokernels. Its right derived functor is therefore termwise restriction.
3. Derived change of rings along the actual limit projection supplies the universal
left derived tensor functor, computed on K-flat resolutions, with canonical counit.
4. Apply the derived-adjoint-functors theorem to these two functors. Its Hom
bijections are natural in both unbounded derived variables, without completeness,
constructibility, boundedness, flatness or characteristic assumptions.
5. On a K-flat complex P, the pre-derived adjunction sends its ordinary unit to the
identity. The left comparison is the K-flat counit isomorphism and the right comparison
is exact-functor factorization. This gives the displayed unit equation. Naturality
then gives the roof K ← P → Res(S tensor P) for any K-flat resolution P → K,
independently of the resolution. -/
theorem derivedScalarExtensionRestrictionAdjunction :
    ∃ adj : scalarReductionDerivedExtension l E Y n ⊣
        scalarReductionDerivedRestriction l E Y n,
      ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients
          (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
          (R := completedIntegralCommRingSheafUnrestricted l E Y) P →
        adj.unit.app (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
          (scalarReductionDerivedRestriction l E Y n).map
            ((scalarReductionCounit l E Y n).app
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
          (scalarReductionRestriction l E Y n).mapDerivedCategoryFactorsh.hom.app
            (((scalarReductionExtension l E Y n).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
        DerivedCategory.Qh.map
          (((Classical.choose (scalarReductionExtension_adjunction l E Y n)).mapHomotopyCategory
            (ComplexShape.up ℤ)).unit.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  sorry

end WeilConjectures
