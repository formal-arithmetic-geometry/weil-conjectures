/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.CategoryTheory.ConstantCoefficientScalarExtension
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # The constant prime-power resolution on a small site

Source: Stacks Project, Modules on Sites, Tags 03EI and 03EP; Cohomology on Sites,
Tag 06YQ; main-20261015 blueprint, lem-pur-finite-kummer-level.proof.md
(blueprint: lem-pur-constant-two-term-resolution).
The coefficient sheaves are discrete constant sheaves, formed by module sheafification.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 1024

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory


namespace SheafOfModules.ConstantPrimePower

variable {S : Type u} [SmallCategory S] (J : GrothendieckTopology S)
  (l : ℕ) [Fact l.Prime]

/-- A universe lift of the ordinary coefficient ring. Source: Stacks, Tag 03EI,
constant-coefficient application (blueprint: lem-pur-constant-two-term-resolution). -/
abbrev Coeff := ULift.{u} (PadicInt l)

/-- Modules over the discrete constant coefficient ring. Source: Stacks, Tag 03EI
(blueprint: lem-pur-constant-two-term-resolution). -/
abbrev Modules := ringedSiteModules.{u} (constantCoefficientRing J (Coeff.{u} l))

/-- The constant coefficient module, obtained by the recorded constant module functor.
Source: Stacks, Tag 03EI (blueprint: lem-pur-constant-two-term-resolution). -/
abbrev freeModule : Modules J l :=
  (constantCoefficientModule J (Coeff.{u} l)).obj
    (ModuleCat.of (Coeff.{u} l) (Coeff.{u} l))

/-- The ordinary reduction homomorphism, lifted without changing its elements.
Source: Mathlib `PadicInt.toZModPow`; Stacks, Tag 03EI
(blueprint: lem-pur-constant-two-term-resolution). -/
def reductionRingHom (n : ℕ) : Coeff.{u} l →+* ULift.{u} (ZMod (l ^ n)) :=
  (PadicInt.toZModPow n).ulift

/-- The ordinary finite quotient as a module over the lifted coefficient ring.
Source: Stacks, Tag 03EI (blueprint: lem-pur-constant-two-term-resolution). -/
abbrev quotientModule (n : ℕ) : ModuleCat.{u} (Coeff.{u} l) :=
  (ModuleCat.restrictScalars (reductionRingHom.{u} l n)).obj
    (ModuleCat.of (ULift.{u} (ZMod (l ^ n))) (ULift.{u} (ZMod (l ^ n))))

/-- The ordinary quotient map as a linear map into its restricted-scalars module.
Source: Stacks, Tag 03EI (blueprint: lem-pur-constant-two-term-resolution). -/
def reductionLinear (n : ℕ) :
    ModuleCat.of (Coeff.{u} l) (Coeff.{u} l) ⟶ quotientModule.{u} l n :=
  ModuleCat.ofHom (X := ModuleCat.of (Coeff.{u} l) (Coeff.{u} l))
    (Y := quotientModule.{u} l n)
    { toFun := reductionRingHom l n
      map_add' := (reductionRingHom l n).map_add
      map_smul' := (reductionRingHom l n).map_mul }

/-- The constant finite quotient with its canonical constant-ring action.
Source: Stacks, Tag 03EI (blueprint: lem-pur-constant-two-term-resolution). -/
abbrev quotientSheaf (n : ℕ) : Modules J l :=
  (constantCoefficientModule J (Coeff.{u} l)).obj (quotientModule l n)

/-- Sheafification of the coefficient quotient map, retaining its specified normalization.
Source: Stacks, Tag 03EI (blueprint: lem-pur-constant-two-term-resolution). -/
abbrev quotientMap (n : ℕ) : freeModule J l ⟶ quotientSheaf J l n :=
  (constantCoefficientModule J (Coeff.{u} l)).map (reductionLinear l n)

/-- The image of a constant coefficient in the constant free module sheaf.
Source: Stacks, Tag 03EI (blueprint: lem-pur-constant-two-term-resolution). -/
def constantSection (U : Sᵒᵖ) (a : Coeff.{u} l) : (freeModule J l).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{u}
    (R := constantCoefficientRing J (Coeff.{u} l)) (J := J)
    (constantCoefficientUnit J (Coeff.{u} l))).unit.app
      ((strictPerfectConstantPresheaf (C := S) (Coeff.{u} l)).obj
        (ModuleCat.of (Coeff.{u} l) (Coeff.{u} l)))).app U) a

/-- The single complex in degree zero, using Mathlib's cochain convention.
Source: Stacks, Tag 0115 (blueprint: lem-pur-constant-two-term-resolution). -/
abbrev single (L : Modules J l) : CochainComplex (Modules J l) ℤ :=
  (CochainComplex.singleFunctor (Modules J l) 0).obj L

/-- The total tensor with a degree-zero left factor; this is the recorded signed total tensor.
Source: Stacks, Tag 06YN (blueprint: lem-pur-constant-two-term-resolution). -/
def total (L : Modules J l) (K : CochainComplex (Modules J l) ℤ) :
    CochainComplex (Modules J l) ℤ :=
  letI := monoidalCategory ((constantSheaf J CommRingCat.{u}).obj
    (CommRingCat.of (Coeff.{u} l)))
  CochainComplex.mapBifunctor (single J l L) K (curriedTensor _)

/-- Inclusion of the `(0,0)` summand, expressed using the explicit sheaf tensor product.
Source: Stacks, Tag 06YN and Section 03EK
(blueprint: lem-pur-constant-two-term-resolution). -/
def zeroSummand (L : Modules J l) (K : CochainComplex (Modules J l) ℤ) :
    (siteSheafTensorRight (K.X 0)).obj ((single J l L).X 0) ⟶ (total J l L K).X 0 :=
  letI := monoidalCategory ((constantSheaf J CommRingCat.{u}).obj
    (CommRingCat.of (Coeff.{u} l)))
  (siteSheafTensorRightIso _ (K.X 0)).hom.app _ ≫
    HomologicalComplex.ιMapBifunctor (single J l L) K (curriedTensor _) (.up ℤ)
      0 0 0 (zero_add 0)

/-- Two-term constant resolution and its tensor augmentation.
Source: Stacks, Tags 03EI, 03EP, 06YQ; main-20261015 blueprint,
lem-pur-finite-kummer-level.proof.md (blueprint: lem-pur-constant-two-term-resolution).

Proof:
1. The ordinary coefficient resolution of `lem-weil-pbc-standard-quotients-perfect` is exact.
   Sheafify the constant module sequence by
   `lem-weil-pbc-site-r-module-presheaf-sheafification-exact`, giving kernel zero and
   cokernel the constant quotient, with the specified quotient map.
2. The tensor unitor of `lem-pc-sheaf-modules-tensor-closed` makes the coefficient unit flat;
   zero is flat as well. The two-term complex is bounded above, hence K-flat by
   `lem-pc-bounded-above-flat-kflat-site`.
3. Its only possible cohomology sheaves are the kernel in degree -1 and cokernel in degree 0.
   The quotient augmentation induces the cokernel identification, hence is a quasi-isomorphism.
4. By `lem-weil-pbc-independent-sheaf-tensor-colimits`, tensor preserves the quotient cokernel.
   The unitor takes `id tensor l^n` to multiplication by `l^n` on L. The induced quotient
   isomorphism sends `x tensor a-bar` to `a[x]`; its inverse sends `[x]` to `x tensor 1`.
   This identification requires no injectivity on L.
5. The total tensor has just the two terms L, with differential multiplication by `l^n`
   and positive sign. Under the assumed injectivity its degree -1 cohomology vanishes,
   and the normalized augmentation induces the quotient isomorphism on degree 0.
   The summand equation fixes the canonical augmentation, rather than an arbitrary map. -/
theorem constant_two_term_resolution (n : ℕ) (hn : 1 ≤ n) :
    ∃ (K : CochainComplex (Modules J l) ℤ)
      (em : K.X (-1) ≅ freeModule J l) (e0 : K.X 0 ≅ freeModule J l),
      (∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i)) ∧
      K.d (-1) 0 = em.hom ≫ ((l ^ n) • 𝟙 (freeModule J l)) ≫ e0.inv ∧
      (∀ i : ℤ, IsFlatOnSite
        (J := J)
        (R := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of (Coeff.{u} l)))
        (K.X i)) ∧
      CochainComplex.IsKFlatIndependentCoefficients K ∧
      (∃ ε : K ⟶ single J l (quotientSheaf J l n),
        ε.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom =
          e0.hom ≫ quotientMap J l n ∧ QuasiIso ε) ∧
      (∀ L : Modules J l,
        ∃ φ : (siteSheafTensorRight (quotientSheaf J l n)).obj L ≅
            cokernel ((l ^ n) • 𝟙 L),
          (∀ (U : Sᵒᵖ) (x : L.val.obj U) (a : Coeff.{u} l),
            φ.hom.val.app U (siteSheafTensorTmul L (quotientSheaf J l n) U x
              ((quotientMap J l n).val.app U
                (constantSection J l U a))) =
              (cokernel.π ((l ^ n) • 𝟙 L)).val.app U
                (((constantCoefficientUnit J (Coeff.{u} l)).app U a) • x)) ∧
          (Mono ((l ^ n) • 𝟙 L) →
            ∃ α : total J l L K ⟶
                single J l ((siteSheafTensorRight (quotientSheaf J l n)).obj L),
              zeroSummand J l L K ≫ α.f 0 ≫
                  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).hom =
                (siteSheafTensorRight (K.X 0)).map
                    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom ≫
                  siteSheafTensorSecondMap L (e0.hom ≫ quotientMap J l n) ∧
              QuasiIso α)) := by
  sorry

end SheafOfModules.ConstantPrimePower
