/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.ULift
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.Algebra.Homology.SheafRingDerivedHomComparison
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral

/-!
# Scalar adjunction and coefficient-unit normalization

Source: blueprint main-20261015, Cartier proof paragraphs 4–5; Stacks Project,
Tags 03D7, 015F, 09T5, 0FND, 06YN and 06YU.
(blueprint: lem-sfb-scalar-adjunction-unit-coefficient-normalization).

The scalar-first tensor convention `r ⊗ x` is the paper's `x ⊗ r`.
The normalized Hom formulas specify the adjunction, including its comparison on complexes.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r wZ wR

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules.ScalarAdjunctionNormalization

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{r}]

/-- The constant integer ring sheaf, with its explicit size lift.
Source: Stacks 093I (blueprint: lem-sfb-scalar-adjunction-unit-coefficient-normalization). -/
noncomputable abbrev integers : Sheaf J CommRingCat.{r} :=
  (constantSheaf J CommRingCat.{r}).obj (CommRingCat.of (ULift.{r} ℤ))

/-- The constant residue ring sheaf, including the zero ring when `n = 1`.
Source: Stacks 093I (blueprint: lem-sfb-scalar-adjunction-unit-coefficient-normalization). -/
noncomputable abbrev residues (n : ℕ) : Sheaf J CommRingCat.{r} :=
  (constantSheaf J CommRingCat.{r}).obj (CommRingCat.of (ULift.{r} (ZMod n)))

/-- The actual constant coefficient quotient, not a chosen ring-sheaf map.
Source: Stacks 093I (blueprint: lem-sfb-scalar-adjunction-unit-coefficient-normalization). -/
noncomputable def quotient (n : ℕ) : integers J ⟶ residues J n :=
  (constantSheaf J CommRingCat.{r}).map
    (CommRingCat.ofHom (Int.castRingHom (ZMod n)).ulift)

variable [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

/-- Integer-module sheaves, using the recorded general ringed-site category.
Source: Stacks 03CY (blueprint: lem-sfb-scalar-adjunction-unit-coefficient-normalization). -/
abbrev IntegerModules := ringedSiteModules.{r}
  (derivedChangeRingIndependentCoefficients J (integers J))

/-- Residue-module sheaves, using the same category construction.
Source: Stacks 03CY (blueprint: lem-sfb-scalar-adjunction-unit-coefficient-normalization). -/
abbrev ResidueModules (n : ℕ) := ringedSiteModules.{r}
  (derivedChangeRingIndependentCoefficients J (residues J n))

/-- Restriction along the actual coefficient quotient.
Source: Stacks 03D7 (blueprint: lem-sfb-scalar-adjunction-unit-coefficient-normalization). -/
noncomputable abbrev restriction (n : ℕ) : ResidueModules J n ⥤ IntegerModules J :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map (quotient J n))

/-- The integer sheaf as its free rank-one module.
Source: Stacks 03CY (blueprint: lem-sfb-scalar-adjunction-unit-coefficient-normalization). -/
noncomputable abbrev integerUnit : IntegerModules J :=
  unit (derivedChangeRingIndependentCoefficients J (integers J))

/-- The residue sheaf as its free rank-one module.
Source: Stacks 03CY (blueprint: lem-sfb-scalar-adjunction-unit-coefficient-normalization). -/
noncomputable abbrev residueUnit (n : ℕ) : ResidueModules J n :=
  unit (derivedChangeRingIndependentCoefficients J (residues J n))

/-- The quotient as a module morphism: the linear map carrying `1` to `1`.
Source: Stacks 03D7 (blueprint: lem-sfb-scalar-adjunction-unit-coefficient-normalization). -/
noncomputable def coefficientQuotient (n : ℕ) :
    integerUnit J ⟶ (restriction J n).obj (residueUnit J n) :=
  ((restriction J n).obj (residueUnit J n)).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun U ↦ (1 : (residues J n).obj.obj U))
      (fun _ _ f ↦ by exact map_one ((residues J n).obj.map f).hom))

variable [EssentiallySmall.{r} C]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasDerivedCategory.{wZ} (IntegerModules J)]
  (n : ℕ) [HasDerivedCategory.{wR} (ResidueModules J n)]

/-- All normalizations for the prescribed universal scalar-extension pair. The exactness
fields provide the instances used to form the termwise derived restriction. No adjunction
or coefficient comparison is supplied as a hypothesis.
Source: Cartier proof paragraphs 4–5; Stacks 03D7, 015F, 0FND, 09T5 and 06YU
(blueprint: lem-sfb-scalar-adjunction-unit-coefficient-normalization). -/
structure Normalization (M : DerivedChangeOfRingsCochainModel (quotient J n)) where
  /-- Restriction preserves finite limits. -/
  [restriction_limits : PreservesFiniteLimits (restriction J n)]
  /-- Restriction preserves finite colimits. -/
  [restriction_colimits : PreservesFiniteColimits (restriction J n)]
  /-- The ordinary tensor/restriction adjunction. -/
  ordinary : M.E ⊣ restriction J n
  /-- Forward Hom formula, evaluated after the sheafification unit. -/
  ordinary_forward : ∀ (F : IntegerModules J) (T : ResidueModules J n)
    (f : M.E.obj F ⟶ T) (U : Cᵒᵖ) (x : F.val.obj U),
    ((ordinary.homEquiv F T) f).val.app U x =
      (eqToHom (M.obj_eq F).symm ≫ f).val.app U
        ((toSheafify J (changeOfRingsPresheaf (quotient J n) F).presheaf).app U
          ((1 : (residues J n).obj.obj U) ⊗ₜ[(integers J).obj.obj U,
            ((quotient J n).hom.app U).hom] x))
  /-- Inverse Hom formula on the generating presheaf pure tensors. -/
  ordinary_inverse : ∀ (F : IntegerModules J) (T : ResidueModules J n)
    (g : F ⟶ (restriction J n).obj T) (U : Cᵒᵖ)
    (x : F.val.obj U) (a : (residues J n).obj.obj U),
    (eqToHom (M.obj_eq F).symm ≫ (ordinary.homEquiv F T).symm g).val.app U
        ((toSheafify J (changeOfRingsPresheaf (quotient J n) F).presheaf).app U
          (a ⊗ₜ[(integers J).obj.obj U, ((quotient J n).hom.app U).hom] x)) =
      @SMul.smul ((residues J n).obj.obj U) (T.val.obj U) inferInstance a (g.val.app U x)
  /-- Exact restriction is its right derived functor, with the canonical factorization. -/
  restriction_rightDerived : (restriction J n).mapDerivedCategory.IsRightDerivedFunctor
    (restriction J n).mapDerivedCategoryFactors.inv
    (HomologicalComplex.quasiIso (ResidueModules J n) (.up ℤ))
  /-- The derived adjunction, fixed by the compatibility formula below. -/
  derived : M.T ⊣ (restriction J n).mapDerivedCategory
  /-- The canonical formula of derived-adjunction compatibility, on complexes. -/
  derived_hom : ∀ (P : CochainComplex (IntegerModules J) ℤ)
    (N : CochainComplex (ResidueModules J n) ℤ)
    (f : (M.E.mapHomologicalComplex (.up ℤ)).obj P ⟶ N),
    derived.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)
        (M.ε.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
          ((ordinary.mapHomologicalComplex (.up ℤ)).homEquiv P N f) ≫
        (restriction J n).mapDerivedCategoryFactors.inv.app N
  /-- The resolution comparison carries the derived unit to `x ↦ x ⊗ 1`. -/
  kflat_unit : ∀ (P : CochainComplex (IntegerModules J) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := integers J) P →
    derived.unit.app (DerivedCategory.Q.obj P) ≫
        (restriction J n).mapDerivedCategory.map (M.ε.app P) ≫
        (restriction J n).mapDerivedCategoryFactors.hom.app
          ((M.E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((ordinary.mapHomologicalComplex (.up ℤ)).unit.app P)
  /-- Compatibility with every integer shift, for the shift structure induced by adjunction. -/
  unit_shift : ∀ k : ℤ, Adjunction.CommShift.CompatibilityUnit derived
    (Adjunction.LeftAdjointCommShift.iso derived k)
    ((restriction J n).mapDerivedCategory.commShiftIso k)
  /-- The degree-zero integer unit is K-flat. -/
  integer_kflat : CochainComplex.IsKFlatIndependentCoefficients (R := integers J)
    ((CochainComplex.singleFunctor (IntegerModules J) 0).obj (integerUnit J))
  /-- Existence and uniqueness use the actual coefficient quotient as adjunct. -/
  coefficient : ∃! e : M.T.obj ((DerivedCategory.singleFunctor _ 0).obj (integerUnit J)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (residueUnit J n),
    derived.unit.app ((DerivedCategory.singleFunctor _ 0).obj (integerUnit J)) ≫
        (restriction J n).mapDerivedCategory.map e.hom ≫
        ((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app (residueUnit J n) =
      (DerivedCategory.singleFunctor _ 0).map (coefficientQuotient J n)
  /-- Unique ordinary reduction and its normalized derived-category identity. -/
  reduction : ∀
    (e : M.T.obj ((DerivedCategory.singleFunctor _ 0).obj (integerUnit J)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (residueUnit J n)),
    derived.unit.app ((DerivedCategory.singleFunctor _ 0).obj (integerUnit J)) ≫
        (restriction J n).mapDerivedCategory.map e.hom ≫
        ((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app (residueUnit J n) =
      (DerivedCategory.singleFunctor _ 0).map (coefficientQuotient J n) →
    ∀ (F : IntegerModules J) (T : ResidueModules J n)
      (p : F ⟶ (restriction J n).obj T) (hp₀ : (n • 𝟙 F) ≫ p = 0),
    IsColimit (CokernelCofork.ofπ p hp₀) →
    ∀ (a : M.T.obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
        (DerivedCategory.singleFunctor _ 0).obj T),
    derived.unit.app ((DerivedCategory.singleFunctor _ 0).obj F) ≫
        (restriction J n).mapDerivedCategory.map a.hom ≫
        ((restriction J n).mapDerivedCategorySingleFunctor 0).hom.app T =
      (DerivedCategory.singleFunctor _ 0).map p →
    ∀ s : integerUnit J ⟶ F,
      (∃! t : residueUnit J n ⟶ T,
        coefficientQuotient J n ≫ (restriction J n).map t = s ≫ p) ∧
      ∀ t : residueUnit J n ⟶ T,
        coefficientQuotient J n ≫ (restriction J n).map t = s ≫ p →
        (DerivedCategory.singleFunctor _ 0).map t =
          e.inv ≫ M.T.map ((DerivedCategory.singleFunctor _ 0).map s) ≫ a.hom

/-- The normalized scalar adjunction, including the coefficient-unit comparison and
reduction identity, exists for every prescribed K-flat universal model.
Source: Cartier proof paragraphs 4–5, live V2 steps 1 and 9; Stacks 03D7, 015F,
0FND, 09T5, 06YN, 06YU
(blueprint: lem-sfb-scalar-adjunction-unit-coefficient-normalization).

Proof:
1. Use `lem-pur-sheaf-ring-coefficient-ordinary-adjunction`. Its balanced sheafified tensor
   formulas are inverse, and restriction preserves kernels and sheafified cokernels.
2. By `lem-weil-pbc-exact-functor-derived-functor`, termwise restriction is its derived
   functor. K-flat resolutions (`lem-pc-kflat-resolution`) make the extension denominator
   pro-systems essentially constant; restriction makes the ind-systems constant.
   Descend the ordinary adjunction using `lem-weil-pbc-termwise-adjunction-homotopy`.
   Apply `new-derived-adjunction-compatibility` and the identity-denominator formula of
   `lem-pc-pre-derived-adjoint-functors-general`. The Hom comparison of
   `lem-pur-sheaf-ring-derived-hom-comparison` has the same unit on K-flat representatives,
   hence everywhere by naturality and K-flat resolution, so it is this same adjunction.
3. Put `f = id` on `E(P)` in this formula. Its transpose is the ordinary tensor unit;
   `M.computes` makes the resolution comparison invertible when P is K-flat.
4. Exact restriction commutes with every integer shift. Transfer its shift structure to
   the left adjoint, using `lem-weil-pbc-adjunction-shift-compatibility-unique` dually;
   the unit compatibility is precisely `unit_shift`.
5. The tensor universal property (`lem-pc-sites-sheaf-tensor-bilinear-universal`) identifies
   total tensor with Z[0] with the original complex. Thus Z[0] is K-flat.
6. The inverse sheaf maps `z ⊗ r ↦ q(z)r` and `r ↦ 1 ⊗ r` identify E(Z) with R. Compose
   with the K-flat comparison of `lem-pur-derived-change-of-rings` to obtain e. Step 3
   identifies its adjunct with the actual quotient.
7. Injectivity of the derived Hom correspondence proves uniqueness of e.
8. Transpose `p s` in the ordinary adjunction and use E(Z) ≅ R. This gives the unique
   residue-linear reduction, without any assertion of sectionwise surjectivity of p.
9. Naturality of the derived unit identifies the adjuncts of `Lq(s) ≫ a` and `e ≫ t[0]`.
   They are both `s[0] ≫ p[0]`. Injectivity of the Hom bijection, followed by e inverse,
   gives the displayed derived reduction identity, with the canonical single comparisons.
No flatness of R over Z is used. -/
theorem scalarAdjunctionUnitCoefficientNormalization [HasTerminal C] (hn : 1 ≤ n)
    (M : DerivedChangeOfRingsCochainModel (quotient J n)) :
    Nonempty (Normalization J n M) := by
  sorry

end SheafOfModules.ScalarAdjunctionNormalization
