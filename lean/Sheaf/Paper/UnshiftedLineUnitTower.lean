/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q112
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.IntegralTwistBaseChange
public import Sheaf.Paper.IntegralTwistDerivedScalarCanonical
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.CompletedLineTensorCoherence
public import Sheaf.Paper.ConstantCoefficientScalarNormalization
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

/-! # Unshifted coefficient-unit and Tate-line multiplication in a tower

Source: purity transport, coefficient-change Step 3; Stacks Tags 03EK, 06YY and 0G7E
(blueprint: lem-pur-unshifted-line-unit-tower).

The scalar functors, beta, associator and identity unitor are the recorded constructions.
The unit comparison below is specified first on sheaves and then by its K-flat counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurUnshiftedTate

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (S : Scheme.{u})

/-- The regular completed coefficient module, without a new coefficient construction.
Source: purity transport Step 3 (blueprint: lem-pur-unshifted-line-unit-tower). -/
abbrev regular : integralTowerModules l E S :=
  SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E S)

variable (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
  (ι : E →ₐ[Padic l] F)

/-- The coefficient multiplication isomorphism and its inverse are fixed on local tensors.
Source: Stacks 03EK; purity transport Step 3
(blueprint: lem-pur-unshifted-line-unit-tower).
Proof: the balanced map sends x tensor b to iota(x)b and commutes with restrictions.
Its inverse sends b to 1 tensor b. The balancing relation gives both inverse equations.
Sheafification extends the maps and local tensor generation proves uniqueness. -/
theorem multiplication_existsUnique :
    ∃! e : (completedOrdinaryScalarExtension l E F ι S).obj (regular l E S) ≅ regular l F S,
      (∀ (U : S.ProEtᵒᵖ)
        (x : (completedIntegralCommRingSheafUnrestricted l E S).obj.obj U)
        (b : (completedIntegralCommRingSheafUnrestricted l F S).obj.obj U),
        e.hom.val.app U (completedScalarTensorSection l E F ι S _ U b x) =
          (completedCoefficientMap l E F ι S).hom.app U x * b) ∧
      ∀ (U : S.ProEtᵒᵖ)
        (b : (completedIntegralCommRingSheafUnrestricted l F S).obj.obj U),
        e.inv.val.app U b = completedScalarTensorSection l E F ι S _ U b
          (@id ((completedIntegralCommRingSheafUnrestricted l E S).obj.obj U) 1) := by
  sorry

/-- The sheaf multiplication, determined by the preceding two formulas.
Source: Stacks 03EK (blueprint: lem-pur-unshifted-line-unit-tower). -/
def multiplication := (multiplication_existsUnique l E S F ι).exists.choose

/-- The degree-zero multiplication chain isomorphism, with the standard single comparison.
Source: Stacks 06YY (blueprint: lem-pur-unshifted-line-unit-tower). -/
def multiplicationComplex :
    (completedOrdinaryScalarComplex l E F ι S).obj (constantWeilIntegralComplex l E S) ≅
      constantWeilIntegralComplex l F S :=
  ((completedOrdinaryScalarExtension l E F ι S).mapCochainComplexSingleFunctor 0).app
      (regular l E S) ≪≫
    (CochainComplex.singleFunctor _ 0).mapIso (multiplication l E S F ι)

/-- The canonical K-flat resolving comparison followed by coefficient multiplication.
Source: Stacks 06YY (blueprint: lem-pur-unshifted-line-unit-tower). -/
def unitMap :
    (completedDerivedScalarExtension l E F ι S).obj (integralConstantCoefficientObject l E S) ⟶
      integralConstantCoefficientObject l F S :=
  completedScalarCounit l E F ι S (constantWeilIntegralComplex l E S) ≫
    DerivedCategory.Q.map (multiplicationComplex l E S F ι).hom

/-- The defining unit map is invertible on its flat degree-zero representative.
Source: Stacks 06YY and 0G7E (blueprint: lem-pur-unshifted-line-unit-tower).
Proof: the regular module is flat, so its degree-zero complex is K-flat. The universal
resolving counit is therefore invertible; its composite with multiplication is invertible. -/
theorem unitMap_isIso : IsIso (unitMap l E S F ι) := by
  sorry

/-- The specified ordinary coefficient-unit comparison u.
Source: purity transport Step 3 (blueprint: lem-pur-unshifted-line-unit-tower). -/
def unitIso := @asIso _ _ _ _ (unitMap l E S F ι) (unitMap_isIso l E S F ι)

variable [∀ x : S, Invertible (l : S.residueField x)]

/-- The degree-zero model R tensor J of the unshifted twisted unit.
Source: purity transport Step 3 (blueprint: lem-pur-unshifted-line-unit-tower). -/
abbrev lineModel (m : ℕ) := (integralSheafTwist l E S (m : ℤ)).obj (regular l E S)

/-- The twisted derived unit V, using the recorded exact tensor-by-line functor.
Source: purity transport Step 3 (blueprint: lem-pur-unshifted-line-unit-tower). -/
abbrev lineUnit (m : ℕ) :=
  (integralSheafTwist l E S (m : ℤ)).mapDerivedCategory.obj
    (integralConstantCoefficientObject l E S)

/-- The unit-tensor-line coordinate, identified with the line by the standard left unitor.
Source: Stacks 03EK (blueprint: lem-pur-unshifted-line-unit-tower). -/
def lineCoordinate (m : ℕ) : lineModel l E S m ≅ integralTwistLine l E S (m : ℤ) :=
  SheafOfModules.scalarTensorLeftUnitor
    (completedIntegralCommRingSheafUnrestricted l E S) (integralTwistLine l E S (m : ℤ))

/-- Ordinary line multiplication is specified on all local pure tensors.
Source: Stacks 03EK and the integral twist base-change formula
(blueprint: lem-pur-unshifted-line-unit-tower).
Proof: the termwise beta takes (x tensor z) tensor b to
(x tensor b) tensor b_ji(z tensor 1). Apply multiplication to its first factor.
This balanced map is an isomorphism: the line base-change map and multiplication are
isomorphisms. Local tensor generation, twice, gives uniqueness. -/
theorem lineMultiplication_existsUnique (m : ℕ) :
    ∃! e : (completedOrdinaryScalarExtension l E F ι S).obj (lineModel l E S m) ≅
        lineModel l F S m,
      ∀ (U : S.ProEtᵒᵖ)
        (x : (completedIntegralCommRingSheafUnrestricted l E S).obj.obj U)
        (z : (integralTwistLine l E S (m : ℤ)).val.obj U)
        (b : (completedIntegralCommRingSheafUnrestricted l F S).obj.obj U),
        (e.hom ≫ (lineCoordinate l F S m).hom).val.app U
          (completedScalarTensorSection l E F ι S _ U b
            (SheafOfModules.siteSheafTensorTmul
              (A := completedIntegralCommRingSheafUnrestricted l E S) _ _ U x z)) =
          ((completedCoefficientMap l E F ι S).hom.app U x * b) •
            (@id ((integralTwistLine l F S (m : ℤ)).val.obj U)
              ((twistScalarMaps l E S F ι (m : ℤ)).val.app U z)) := by
  sorry

/-- The canonical degree-zero line map, uniquely fixed by its section formula.
Source: purity transport Step 3 (blueprint: lem-pur-unshifted-line-unit-tower). -/
def lineMultiplication (m : ℕ) :=
  (lineMultiplication_existsUnique l E S F ι m).exists.choose

/-- Its chain map, using only the standard comparisons with degree-zero complexes.
Source: Stacks 06YY (blueprint: lem-pur-unshifted-line-unit-tower). -/
def lineMultiplicationComplex (m : ℕ) :
    (completedOrdinaryScalarComplex l E F ι S).obj
        (((integralSheafTwist l E S (m : ℤ)).mapHomologicalComplex (.up ℤ)).obj
          (constantWeilIntegralComplex l E S)) ≅
      ((integralSheafTwist l F S (m : ℤ)).mapHomologicalComplex (.up ℤ)).obj
        (constantWeilIntegralComplex l F S) :=
  (completedOrdinaryScalarComplex l E F ι S).mapIso
      (((integralSheafTwist l E S (m : ℤ)).mapCochainComplexSingleFunctor 0).app
        (regular l E S)) ≪≫
    ((completedOrdinaryScalarExtension l E F ι S).mapCochainComplexSingleFunctor 0).app
      (lineModel l E S m) ≪≫
    (CochainComplex.singleFunctor _ 0).mapIso (lineMultiplication l E S F ι m) ≪≫
    (((integralSheafTwist l F S (m : ℤ)).mapCochainComplexSingleFunctor 0).app
      (regular l F S)).symm

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The specified w is beta on U followed by u(m), with no arbitrary isomorphism chosen.
Source: purity transport Step 3 (blueprint: lem-pur-unshifted-line-unit-tower). -/
def lineIso (m : ℕ) :
    (completedDerivedScalarExtension l E F ι S).obj (lineUnit l E S m) ≅
      lineUnit l F S m :=
  (integralTwistOrdinaryBeta l E F ι S (m : ℤ)).app
      (constantWeilIntegralObject l E D hl S) ≪≫
    (integralSheafTwist l F S (m : ℤ)).mapDerivedCategory.mapIso (unitIso l E S F ι)

/-- The specified beta-composite is represented by exactly the degree-zero line map.
Source: purity transport Step 3 and the specified twist/scalar comparison
(blueprint: lem-pur-unshifted-line-unit-tower).
Proof: the flat degree-zero unit is a good K-flat representative. The defining counit
equation of integralTwistOrdinaryBeta gives its termwise pure-tensor map. Compose with
the resolving comparison and multiplication defining u. Naturality of the exact-tensor
localization comparison gives the displayed equation. The pure-tensor formula identifies
the resulting sheaf map with lineMultiplication, by uniqueness. -/
theorem lineIso_model (m : ℕ) :
    (lineIso l E S F ι D hl m).hom =
      (completedDerivedScalarExtension l E F ι S).map
        ((integralSheafTwist l E S (m : ℤ)).mapDerivedCategoryFactors.hom.app
          (constantWeilIntegralComplex l E S)) ≫
      completedScalarCounit l E F ι S
        (((integralSheafTwist l E S (m : ℤ)).mapHomologicalComplex (.up ℤ)).obj
          (constantWeilIntegralComplex l E S)) ≫
      DerivedCategory.Q.map (lineMultiplicationComplex l E S F ι m).hom ≫
      (integralSheafTwist l F S (m : ℤ)).mapDerivedCategoryFactors.inv.app
        (constantWeilIntegralComplex l F S) := by
  sorry

end WeilConjectures.PurUnshiftedTate

namespace WeilConjectures.PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})
  (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
  [FiniteDimensional (Padic P.coefficients.l) E]
  (F : Type u) [Field F] [Algebra (Padic P.coefficients.l) F]
  [FiniteDimensional (Padic P.coefficients.l) F]
  (G : Type u) [Field G] [Algebra (Padic P.coefficients.l) G]
  [FiniteDimensional (Padic P.coefficients.l) G]
  (ι : E →ₐ[Padic P.coefficients.l] F) (κ : F →ₐ[Padic P.coefficients.l] G)
  (S : Scheme.{u}) [S.Over (Spec (.of P.field.k))]

open PurUnshiftedTate

/-- All sheaf and derived tower equations, their section values and identity normalizations.
The residue inverses come from the structure map, rather than an additional hypothesis.
Source: purity transport Step 3; Stacks 03EK, 06YY and 0G7E
(blueprint: lem-pur-unshifted-line-unit-tower). -/
def unshiftedLineUnitTowerAssertions (m : ℕ) : Prop :=
  letI : ∀ x : S, Invertible (P.coefficients.l : S.residueField x) := fun x ↦
    (map_natCast (IsLocalRing.residue (S.presheaf.stalk x)) P.coefficients.l) ▸
      ((P.coefficientPrime_isUnit_stalk S (S ↘ Spec (.of P.field.k)) x).map
        (IsLocalRing.residue (S.presheaf.stalk x))).invertible
  ((CompletedLineTensor.associatorData P.coefficients.l E S F ι G κ).sheaf.hom.app
      (regular P.coefficients.l E S) ≫ (multiplication P.coefficients.l E S G (κ.comp ι)).hom =
    (completedOrdinaryScalarExtension P.coefficients.l F G κ S).map
      (multiplication P.coefficients.l E S F ι).hom ≫ (multiplication P.coefficients.l F S G κ).hom)
        ∧
  ((CompletedLineTensor.associatorData P.coefficients.l E S F ι G κ).sheaf.hom.app
      (lineModel P.coefficients.l E S m) ≫ (lineMultiplication P.coefficients.l E S G (κ.comp ι)
        m).hom =
    (completedOrdinaryScalarExtension P.coefficients.l F G κ S).map
      (lineMultiplication P.coefficients.l E S F ι m).hom ≫ (lineMultiplication P.coefficients.l F S
        G κ m).hom) ∧
  ((CompletedLineTensor.associatorData P.coefficients.l E S F ι G κ).derived.hom.app
      (integralConstantCoefficientObject P.coefficients.l E S) ≫ (unitIso P.coefficients.l E S G
        (κ.comp ι)).hom =
    (completedDerivedScalarExtension P.coefficients.l F G κ S).map
      (unitIso P.coefficients.l E S F ι).hom ≫ (unitIso P.coefficients.l F S G κ).hom) ∧
  ((CompletedLineTensor.associatorData P.coefficients.l E S F ι G κ).derived.hom.app
      (lineUnit P.coefficients.l E S m) ≫
      (lineIso P.coefficients.l E S G (κ.comp ι) P.field P.coefficients.different m).hom =
    (completedDerivedScalarExtension P.coefficients.l F G κ S).map
      (lineIso P.coefficients.l E S F ι P.field P.coefficients.different m).hom ≫
      (lineIso P.coefficients.l F S G κ P.field P.coefficients.different m).hom) ∧
  (∀ (U : S.ProEtᵒᵖ)
    (x : (completedIntegralCommRingSheafUnrestricted P.coefficients.l E S).obj.obj U)
    (b : (completedIntegralCommRingSheafUnrestricted P.coefficients.l F S).obj.obj U)
    (c : (completedIntegralCommRingSheafUnrestricted P.coefficients.l G S).obj.obj U),
    (((CompletedLineTensor.associatorData P.coefficients.l E S F ι G κ).sheaf.hom.app
          (regular P.coefficients.l E S) ≫ (multiplication P.coefficients.l E S G (κ.comp
            ι)).hom).val.app U
        (completedScalarTensorSection P.coefficients.l F G κ S _ U c
          (completedScalarTensorSection P.coefficients.l E F ι S _ U b x)) =
      (completedCoefficientMap P.coefficients.l E G (κ.comp ι) S).hom.app U x *
        (completedCoefficientMap P.coefficients.l F G κ S).hom.app U b * c) ∧
    (((completedOrdinaryScalarExtension P.coefficients.l F G κ S).map
          (multiplication P.coefficients.l E S F ι).hom ≫ (multiplication P.coefficients.l F S G
            κ).hom).val.app U
        (completedScalarTensorSection P.coefficients.l F G κ S _ U c
          (completedScalarTensorSection P.coefficients.l E F ι S _ U b x)) =
      (completedCoefficientMap P.coefficients.l E G (κ.comp ι) S).hom.app U x *
        (completedCoefficientMap P.coefficients.l F G κ S).hom.app U b * c)) ∧
  (∀ (U : S.ProEtᵒᵖ)
    (x : (completedIntegralCommRingSheafUnrestricted P.coefficients.l E S).obj.obj U)
    (z : (integralTwistLine P.coefficients.l E S (m : ℤ)).val.obj U)
    (b : (completedIntegralCommRingSheafUnrestricted P.coefficients.l F S).obj.obj U)
    (c : (completedIntegralCommRingSheafUnrestricted P.coefficients.l G S).obj.obj U),
    (((CompletedLineTensor.associatorData P.coefficients.l E S F ι G κ).sheaf.hom.app
          (lineModel P.coefficients.l E S m) ≫ (lineMultiplication P.coefficients.l E S G (κ.comp ι)
            m).hom ≫
          (lineCoordinate P.coefficients.l G S m).hom).val.app U
        (completedScalarTensorSection P.coefficients.l F G κ S _ U c
          (completedScalarTensorSection P.coefficients.l E F ι S _ U b
            (SheafOfModules.siteSheafTensorTmul
              (A := completedIntegralCommRingSheafUnrestricted P.coefficients.l E S) _ _ U x z))) =
      ((completedCoefficientMap P.coefficients.l E G (κ.comp ι) S).hom.app U x *
        (completedCoefficientMap P.coefficients.l F G κ S).hom.app U b * c) •
        (@id ((integralTwistLine P.coefficients.l G S (m : ℤ)).val.obj U)
          ((twistScalarMaps P.coefficients.l E S G (κ.comp ι) (m : ℤ)).val.app U z))) ∧
    (((completedOrdinaryScalarExtension P.coefficients.l F G κ S).map
          (lineMultiplication P.coefficients.l E S F ι m).hom ≫
          (lineMultiplication P.coefficients.l F S G κ m).hom ≫ (lineCoordinate P.coefficients.l G S
            m).hom).val.app U
        (completedScalarTensorSection P.coefficients.l F G κ S _ U c
          (completedScalarTensorSection P.coefficients.l E F ι S _ U b
            (SheafOfModules.siteSheafTensorTmul
              (A := completedIntegralCommRingSheafUnrestricted P.coefficients.l E S) _ _ U x z))) =
      ((completedCoefficientMap P.coefficients.l E G (κ.comp ι) S).hom.app U x *
        (completedCoefficientMap P.coefficients.l F G κ S).hom.app U b * c) •
        (@id ((integralTwistLine P.coefficients.l G S (m : ℤ)).val.obj U)
          ((twistScalarMaps P.coefficients.l F S G κ (m : ℤ)).val.app U
            ((twistScalarMaps P.coefficients.l E S F ι (m : ℤ)).val.app U z))))) ∧
  ((unitIso P.coefficients.l E S E (AlgHom.id (Padic P.coefficients.l) E)).hom =
    (CompletedLineTensor.ordinaryUnit P.coefficients.l E S).hom.app
      (integralConstantCoefficientObject P.coefficients.l E S)) ∧
  ((lineIso P.coefficients.l E S E (AlgHom.id (Padic P.coefficients.l) E) P.field
      P.coefficients.different m).hom =
    (CompletedLineTensor.ordinaryUnit P.coefficients.l E S).hom.app (lineUnit P.coefficients.l E S
      m)) ∧
  ((multiplicationComplex P.coefficients.l E S E
      (AlgHom.id (Padic P.coefficients.l) E)).hom =
    (completedScalarIdentityMultiplication P.coefficients.l E S).hom.app
      (constantWeilIntegralComplex P.coefficients.l E S)) ∧
  ((lineMultiplicationComplex P.coefficients.l E S E
      (AlgHom.id (Padic P.coefficients.l) E) m).hom =
    (completedScalarIdentityMultiplication P.coefficients.l E S).hom.app
      (((integralSheafTwist P.coefficients.l E S (m : ℤ)).mapHomologicalComplex (.up ℤ)).obj
        (constantWeilIntegralComplex P.coefficients.l E S))) ∧
  integralOperationsGoodComplex P.coefficients.l E S
    (((integralSheafTwist P.coefficients.l E S (m : ℤ)).mapHomologicalComplex (.up ℤ)).obj
      (constantWeilIntegralComplex P.coefficients.l E S)) ∧
  (∀ (Q : (integralOperationsGoodComplex P.coefficients.l E S).FullSubcategory),
    (Q.obj = constantWeilIntegralComplex P.coefficients.l E S ∨
      Q.obj = ((integralSheafTwist P.coefficients.l E S (m : ℤ)).mapHomologicalComplex (.up ℤ)).obj
        (constantWeilIntegralComplex P.coefficients.l E S)) →
    (completedScalarComparison P.coefficients.l E E (AlgHom.id (Padic P.coefficients.l) E) S).app
        (DerivedCategory.Q.obj Q.obj) ≫
      (integralScalarExtensionComparisonOfUniverses P.coefficients.l E E
        (AlgHom.id (Padic P.coefficients.l) E) S).hom.app Q =
    completedScalarCounit P.coefficients.l E E (AlgHom.id (Padic P.coefficients.l) E) S Q.obj ≫
      DerivedCategory.Q.map ((completedScalarIdentityMultiplication P.coefficients.l E S).hom.app
        Q.obj) ≫
      DerivedCategory.Q.map ((completedScalarIdentityUnit P.coefficients.l E S).app Q.obj))

/-- Coefficient multiplication and the specified beta-composite respect a coefficient tower.
Source: purity transport, coefficient-change Step 3; Stacks 03EK, 06YY, 0G7E
(blueprint: lem-pur-unshifted-line-unit-tower).

Proof:
1. Apply lem-pur-tate-unit-flat-model-domains with n=0. The unit and unit-tensor-line
   degree-zero representatives are flat-term K-flat. Derived-change-of-rings computes
   scalar extension on them, and change-of-rings K-flatness permits successive extension.
2. The bilinear sheaf tensor universal property extends coefficient multiplication.
   Balancing proves that b mapped to 1 tensor b is its inverse.
3. The specified integral twist/scalar beta has its actual termwise tensor formula.
   Composing with twisted multiplication gives exactly lineMultiplication and lineIso_model.
4. The ordinary associator takes ((x tensor b) tensor c) to x tensor iota(b)c.
   Its inverse inserts 1 in the middle. These are inverse by balancing and induce the
   published counit-normalized derived associator, with no signs in degree zero.
5. Both unit paths give iota20(x)*iota21(b)*c, since inclusions compose as ring maps.
   Local tensor generation gives equality of sheaf maps; localization gives derived equality.
6. The direct and successive line paths have the two displayed line factors. They agree
   by the tower clause of integral_twist_base_change. The bilinear universal property
   and derived localization give the sheaf and derived line tower equations.
7. Identity inclusions give multiplication unitors, also for m=0. The identity clause of
   finiteFreeCompletedScalarComparison gives the natural completion map after the ordinary
   unitor, rather than a strict identity extension. No step requires strict field inclusions,
   a positive twist, or a nonempty scheme.
-/
theorem unshifted_line_unit_tower
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))] (m : ℕ) :
    P.unshiftedLineUnitTowerAssertions E F G ι κ S m := by
  sorry

end WeilConjectures.PurityFiniteSetting
