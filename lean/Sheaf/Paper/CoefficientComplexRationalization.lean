/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.Paper.IntegralScalarExtensionWellDefined
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Flat.TorsionFree
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Rationalization of coefficient-module complexes

Source: blueprint main-20261015, `def-weil-finite-coefficient-point`, final paragraph;
Stacks Tags 0539, 00HD, 00CX, 015F and 04VG
(blueprint: lem-weil-coefficient-complex-rationalization).

The aliases below use Mathlib's coefficient-first convention for the ordinary tensor.
They allow arbitrary module sizes above the coefficient size. All maps are specified
on generators before localization; no resolution or boundedness is involved.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- Ordinary integral scalar tensor, using the existing restricted field inclusion.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable abbrev coefficientComplexIntegralTensor :=
  ModuleCat.extendScalars.{u, u, max u v} (integralScalarIntegerInclusion l E L ι)

/-- Ordinary fraction-field tensor, with the recorded valuation subring.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable abbrev coefficientComplexRationalize :=
  ModuleCat.extendScalars.{u, u, max u v} (Padic.coefficientExtensionIntegers l E).subtype

/-- Ordinary field scalar tensor along the specified coefficient inclusion.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable abbrev coefficientComplexFieldTensor :=
  ModuleCat.extendScalars.{u, u, max u v} ι.toRingHom

private theorem coefficientTensorAdditive {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : (ModuleCat.extendScalars.{u, u, max u v} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive

attribute [local instance] coefficientTensorAdditive

private theorem coefficientTensorLimits {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max u v} f) := by
  let : Algebra R S := f.toAlgebra
  let : Module.Flat R S := hf
  have hex : ∀ C : ShortComplex (ModuleCat.{max u v} R), C.Exact →
      (C.map (ModuleCat.extendScalars f)).Exact := by
    intro C hC
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC ⊢
    exact Module.Flat.lTensor_exact S hC
  have h := ((Functor.exact_tfae (ModuleCat.extendScalars.{u, u, max u v} f)).out 1 3).mp
    hex
  exact h.1

private theorem coefficientIntegerFlat {S : Type u} [CommRing S] [IsDomain S]
    (f : Padic.coefficientExtensionIntegers l E →+* S) (hf : Function.Injective f) :
    f.Flat := by
  let : Algebra (Padic.coefficientExtensionIntegers l E) S := f.toAlgebra
  let : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l E) :=
    (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.2.2.2.2.2.2.2.1
  let : Module.IsTorsionFree (Padic.coefficientExtensionIntegers l E) S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hf
  exact inferInstanceAs (Module.Flat (Padic.coefficientExtensionIntegers l E) S)

/-- Exactness of all four coefficient tensors, without finiteness conditions on modules.
Source: blueprint coefficient-point paragraph; Stacks 0539 and 00HD
(blueprint: lem-weil-coefficient-complex-rationalization).
Proof: O_E and O_L are valuation rings, with fraction fields E and L. Their inclusions
make O_L and E torsion-free over O_E, and L torsion-free over O_L and over E.
Apply lem-trf-valuation-torsionfree-flat to each, then lem-weil-pbc-flat-tensor-exact.
Surjectivity follows by lifting pure tensors. Tensor maps add on generators. Exactness
and additivity preserve kernels, cokernels, zero objects and finite biproducts, hence
finite limits and colimits. This is steps 1 and 2 of the node's proof.
-/
theorem coefficientComplexTensors_exact :
    ((coefficientComplexIntegralTensor.{u, v} l E L ι).Additive ∧
      PreservesFiniteLimits (coefficientComplexIntegralTensor.{u, v} l E L ι) ∧
      PreservesFiniteColimits (coefficientComplexIntegralTensor.{u, v} l E L ι)) ∧
    ((coefficientComplexRationalize.{u, v} l E).Additive ∧
      PreservesFiniteLimits (coefficientComplexRationalize.{u, v} l E) ∧
      PreservesFiniteColimits (coefficientComplexRationalize.{u, v} l E)) ∧
    ((coefficientComplexRationalize.{u, v} l L).Additive ∧
      PreservesFiniteLimits (coefficientComplexRationalize.{u, v} l L) ∧
      PreservesFiniteColimits (coefficientComplexRationalize.{u, v} l L)) ∧
    ((coefficientComplexFieldTensor.{u, v} l E L ι).Additive ∧
      PreservesFiniteLimits (coefficientComplexFieldTensor.{u, v} l E L ι) ∧
      PreservesFiniteColimits (coefficientComplexFieldTensor.{u, v} l E L ι)) := by
  have hι : Function.Injective (integralScalarIntegerInclusion l E L ι) := by
    intro a b h
    apply Subtype.ext
    exact ι.injective (congrArg Subtype.val h)
  have hB := coefficientTensorLimits.{u, v} _ (coefficientIntegerFlat l E _ hι)
  have hE := coefficientTensorLimits.{u, v} _
    (coefficientIntegerFlat l E _ (Padic.coefficientExtensionIntegers l E).subtype_injective)
  have hL := coefficientTensorLimits.{u, v} _
    (coefficientIntegerFlat l L _ (Padic.coefficientExtensionIntegers l L).subtype_injective)
  have hfield : ι.toRingHom.Flat := by
    let : Algebra E L := ι.toRingHom.toAlgebra
    exact inferInstanceAs (Module.Flat E L)
  have hF := coefficientTensorLimits.{u, v} _ hfield
  exact ⟨⟨inferInstance, hB, inferInstance⟩, ⟨inferInstance, hE, inferInstance⟩,
    ⟨inferInstance, hL, inferInstance⟩, ⟨inferInstance, hF, inferInstance⟩⟩

/-- Additivity from exact coefficient tensoring. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexIntegralAdditive :
    (coefficientComplexIntegralTensor.{u, v} l E L ι).Additive :=
  (coefficientComplexTensors_exact.{u, v} l E L ι).1.1

/-- Kernel preservation. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexIntegralLimits :
    PreservesFiniteLimits (coefficientComplexIntegralTensor.{u, v} l E L ι) :=
  (coefficientComplexTensors_exact.{u, v} l E L ι).1.2.1

/-- Cokernel preservation. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexIntegralColimits :
    PreservesFiniteColimits (coefficientComplexIntegralTensor.{u, v} l E L ι) :=
  (coefficientComplexTensors_exact.{u, v} l E L ι).1.2.2

/-- Additivity of rationalization. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexRationalAdditive :
    (coefficientComplexRationalize.{u, v} l E).Additive :=
  (coefficientComplexTensors_exact.{u, v} l E E (AlgHom.id (Padic l) E)).2.1.1

/-- Kernel preservation by rationalization. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexRationalLimits :
    PreservesFiniteLimits (coefficientComplexRationalize.{u, v} l E) :=
  (coefficientComplexTensors_exact.{u, v} l E E (AlgHom.id (Padic l) E)).2.1.2.1

/-- Cokernel preservation by rationalization. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexRationalColimits :
    PreservesFiniteColimits (coefficientComplexRationalize.{u, v} l E) :=
  (coefficientComplexTensors_exact.{u, v} l E E (AlgHom.id (Padic l) E)).2.1.2.2

/-- Additivity of field extension. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexFieldAdditive :
    (coefficientComplexFieldTensor.{u, v} l E L ι).Additive :=
  (coefficientComplexTensors_exact.{u, v} l E L ι).2.2.2.1

/-- Kernel preservation by field extension. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexFieldLimits :
    PreservesFiniteLimits (coefficientComplexFieldTensor.{u, v} l E L ι) :=
  (coefficientComplexTensors_exact.{u, v} l E L ι).2.2.2.2.1

/-- Cokernel preservation by field extension. Source: Stacks 00HD
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexFieldColimits :
    PreservesFiniteColimits (coefficientComplexFieldTensor.{u, v} l E L ι) :=
  (coefficientComplexTensors_exact.{u, v} l E L ι).2.2.2.2.2

/-- The standard localization, at arbitrary coefficient-module size.
Source: Stacks 05RU (blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable instance coefficientComplexModuleDerived (R : Type u) [Ring R] :
    HasDerivedCategory (ModuleCat.{max u v} R) := HasDerivedCategory.standard _

private theorem scalarComp_hom_tmul {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (P : ModuleCat.{max u v} R) (b : T) (n : P) :
    (ModuleCat.extendScalarsComp f g).hom.app P (b ⊗ₜ[R, g.comp f] n) =
      b ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n) := by
  have h := ModuleCat.extendScalarsComp_hom_app_one_tmul f g P n
  change ((ModuleCat.extendScalarsComp f g).hom.app P).hom _ = _ at h
  change ((ModuleCat.extendScalarsComp f g).hom.app P).hom _ = _
  calc
    _ = ((ModuleCat.extendScalarsComp f g).hom.app P).hom
        (b • ((1 : T) ⊗ₜ[R, g.comp f] n)) := by
          rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
    _ = b • ((ModuleCat.extendScalarsComp f g).hom.app P).hom
        ((1 : T) ⊗ₜ[R, g.comp f] n) := map_smul _ _ _
    _ = _ := by
      rw [h]
      change (b * 1) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n) = _
      rw [mul_one]

private theorem scalarComp_inv_tmul {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (P : ModuleCat.{max u v} R) (a : S) (b : T) (n : P) :
    (ModuleCat.extendScalarsComp f g).inv.app P
      (b ⊗ₜ[S, g] (a ⊗ₜ[R, f] n)) =
      (b * g a) ⊗ₜ[R, g.comp f] n := by
  apply (ConcreteCategory.bijective_of_isIso
    ((ModuleCat.extendScalarsComp f g).hom.app P)).1
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id_app, ModuleCat.id_apply,
    scalarComp_hom_tmul]
  let : Algebra S T := g.toAlgebra
  rw [show a ⊗ₜ[R, f] n = a • ((1 : S) ⊗ₜ[R, f] n) from
    (ModuleCat.ExtendScalars.smul_tmul f a 1 n).trans (by rw [mul_one]) |>.symm]
  erw [← TensorProduct.smul_tmul]
  change (g a * b) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n) = _
  rw [mul_comm]

private theorem scalarDouble_hom_ext {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (P : ModuleCat.{max u v} R) (X : ModuleCat.{max u v} T)
    (α β : (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj P) ⟶ X)
    (h : ∀ n : P, α ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n)) =
      β ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n))) : α = β := by
  apply ((ModuleCat.extendRestrictScalarsAdj g).homEquiv _ _).injective
  apply ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro n
  exact h n

private theorem scalarTriple_hom_ext {R S T U : Type u}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : S →+* T) (k : T →+* U)
    (P : ModuleCat.{max u v} R) (X : ModuleCat.{max u v} U)
    (α β : (ModuleCat.extendScalars k).obj
      ((ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj P)) ⟶ X)
    (h : ∀ n : P, α ((1 : U) ⊗ₜ[T, k] ((1 : T) ⊗ₜ[S, g]
        ((1 : S) ⊗ₜ[R, f] n))) =
      β ((1 : U) ⊗ₜ[T, k] ((1 : T) ⊗ₜ[S, g] ((1 : S) ⊗ₜ[R, f] n)))) :
    α = β := by
  apply ((ModuleCat.extendRestrictScalarsAdj k).homEquiv _ _).injective
  apply scalarDouble_hom_ext
  intro n
  exact h n

private noncomputable def coefficientModuleBeta :
    coefficientComplexIntegralTensor.{u, v} l E L ι ⋙
        coefficientComplexRationalize.{u, v} l L ≅
      coefficientComplexRationalize.{u, v} l E ⋙
        coefficientComplexFieldTensor.{u, v} l E L ι :=
  (ModuleCat.extendScalarsComp (integralScalarIntegerInclusion l E L ι)
    (Padic.coefficientExtensionIntegers l L).subtype).symm ≪≫
  ModuleCat.extendScalarsComp (Padic.coefficientExtensionIntegers l E).subtype ι.toRingHom

/-- The uniquely normalized ordinary module comparison.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization).
Proof: for C = O_L or E identify (C tensor N) tensor L with L tensor N by
multiplying the two coefficient factors. The inverse inserts 1 as the inner factor.
Both maps are additive and balanced twice, are L-linear, and their composites are the
identity on pure tensors. Compose the inverse E-comparison with the O_L-comparison.
The formula determines the result by tensor generation and commutes with all module
maps. This is steps 3 and 4 of the node's proof; no element of N is divided.
-/
theorem coefficientComplexBeta_existsUnique :
    ∃! β : coefficientComplexIntegralTensor.{u, v} l E L ι ⋙
        coefficientComplexRationalize.{u, v} l L ≅
      coefficientComplexRationalize.{u, v} l E ⋙
        coefficientComplexFieldTensor.{u, v} l E L ι,
      ∀ (P : ModuleCat.{max u v} (Padic.coefficientExtensionIntegers l E))
        (a : Padic.coefficientExtensionIntegers l L) (b : L) (n : P),
        β.hom.app P
          (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
            (Padic.coefficientExtensionIntegers l L).subtype]
            (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              integralScalarIntegerInclusion l E L ι] n)) =
          (b * (a : L)) ⊗ₜ[E, ι.toRingHom]
            ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              (Padic.coefficientExtensionIntegers l E).subtype] n) := by
  have hformula : ∀ (P : ModuleCat.{max u v}
        (Padic.coefficientExtensionIntegers l E))
      (a : Padic.coefficientExtensionIntegers l L) (b : L) (n : P),
      (coefficientModuleBeta.{u, v} l E L ι).hom.app P
        (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
          (Padic.coefficientExtensionIntegers l L).subtype]
          (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
            integralScalarIntegerInclusion l E L ι] n)) =
        (b * (a : L)) ⊗ₜ[E, ι.toRingHom]
          ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
            (Padic.coefficientExtensionIntegers l E).subtype] n) := by
    intro P a b n
    dsimp only [coefficientModuleBeta, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    rw [ModuleCat.comp_apply, scalarComp_inv_tmul]
    exact scalarComp_hom_tmul _ _ P (b * (a : L)) n
  refine ⟨coefficientModuleBeta.{u, v} l E L ι, hformula, ?_⟩
  intro β hβ
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply scalarDouble_hom_ext
  intro n
  exact (hβ P 1 1 n).trans (hformula P 1 1 n).symm

/-- The comparison selected by its unique generator formula.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable def coefficientComplexBeta :=
  (coefficientComplexBeta_existsUnique.{u, v} l E L ι).exists.choose

private theorem coefficientBeta_formula
    (P : ModuleCat.{max u v} (Padic.coefficientExtensionIntegers l E))
    (a : Padic.coefficientExtensionIntegers l L) (b : L) (n : P) :
    (coefficientComplexBeta.{u, v} l E L ι).hom.app P
      (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
        (Padic.coefficientExtensionIntegers l L).subtype]
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion l E L ι] n)) =
      (b * (a : L)) ⊗ₜ[E, ι.toRingHom]
        ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          (Padic.coefficientExtensionIntegers l E).subtype] n) :=
  (coefficientComplexBeta_existsUnique.{u, v} l E L ι).exists.choose_spec P a b n

/-- The degreewise comparison on unbounded cochain complexes.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable def coefficientComplexChainBeta :=
  NatIso.mapHomologicalComplex (coefficientComplexBeta.{u, v} l E L ι) (ComplexShape.up ℤ)

/-- The comparison after localization, using the canonical exact-functor factorizations.
Source: blueprint coefficient-point paragraph; Stacks 015F and 04VG
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable def coefficientComplexDerivedBeta :=
  (Functor.mapDerivedCategoryCompIso (coefficientComplexIntegralTensor.{u, v} l E L ι)
    (coefficientComplexRationalize.{u, v} l L)).symm ≪≫
  Functor.mapDerivedCategoryNatIso (coefficientComplexBeta.{u, v} l E L ι) ≪≫
  Functor.mapDerivedCategoryCompIso (coefficientComplexRationalize.{u, v} l E)
    (coefficientComplexFieldTensor.{u, v} l E L ι)

/-- Restriction of the identity field inclusion is the identity integer map.
Source: blueprint coefficient-point paragraph, identity clause
(blueprint: lem-weil-coefficient-complex-rationalization).
Proof: both ring maps send an integer to itself; subtype extensionality and ring-map
extensionality give equality. This is the coefficient-map part of proof step 5. -/
theorem coefficientComplexIntegerIdentity :
    integralScalarIntegerInclusion l E E (AlgHom.id (Padic l) E) =
      RingHom.id (Padic.coefficientExtensionIntegers l E) := by
  ext x
  rfl

/-- Multiplication identification for the integral identity tensor.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable def coefficientComplexIntegralUnit :
    coefficientComplexIntegralTensor.{u, v} l E E (AlgHom.id (Padic l) E) ≅
      𝟭 (ModuleCat.{max u v} (Padic.coefficientExtensionIntegers l E)) :=
  eqToIso (congrArg (ModuleCat.extendScalars.{u, u, max u v})
    (coefficientComplexIntegerIdentity l E)) ≪≫
  ModuleCat.extendScalarsId (Padic.coefficientExtensionIntegers l E)

variable (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (κ : L →ₐ[Padic l] M)

/-- Restriction of a composite inclusion is the composite integer map.
Source: blueprint coefficient-point paragraph, tower clause
(blueprint: lem-weil-coefficient-complex-rationalization).
Proof: both maps send an integer a to kappa(iota(a)). Subtype extensionality and
ring-map extensionality give equality. This is the coefficient-map part of step 7. -/
theorem coefficientComplexIntegerComp :
    (integralScalarIntegerInclusion l L M κ).comp
      (integralScalarIntegerInclusion l E L ι) =
    integralScalarIntegerInclusion l E M (κ.comp ι) := by
  ext x
  rfl

/-- The integral tensor associator is Mathlib's scalar associator, with the actual
composite integer inclusion. Its forward map multiplies the coefficient factors.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable def coefficientComplexIntegralAssoc :
    coefficientComplexIntegralTensor.{u, v} l E L ι ⋙
      coefficientComplexIntegralTensor.{u, v} l L M κ ≅
    coefficientComplexIntegralTensor.{u, v} l E M (κ.comp ι) :=
  (ModuleCat.extendScalarsComp (integralScalarIntegerInclusion l E L ι)
    (integralScalarIntegerInclusion l L M κ)).symm ≪≫
  eqToIso (congrArg (ModuleCat.extendScalars.{u, u, max u v})
    (coefficientComplexIntegerComp l E L ι M κ))

/-- The field multiplication identification.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable def coefficientComplexFieldUnit :
    coefficientComplexFieldTensor.{u, v} l E E (AlgHom.id (Padic l) E) ≅
      𝟭 (ModuleCat.{max u v} E) :=
  ModuleCat.extendScalarsId E

/-- The field associator, multiplying the two scalar factors.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable def coefficientComplexFieldAssoc :
    coefficientComplexFieldTensor.{u, v} l E L ι ⋙
      coefficientComplexFieldTensor.{u, v} l L M κ ≅
    coefficientComplexFieldTensor.{u, v} l E M (κ.comp ι) :=
  (ModuleCat.extendScalarsComp ι.toRingHom κ.toRingHom).symm

/-- Integral multiplication identification descended to the localization.
Source: Stacks 015F, 04VG (blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable def coefficientComplexDerivedIntegralUnit :=
  Functor.mapDerivedCategoryNatIso (coefficientComplexIntegralUnit.{u, v} l E) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Field multiplication identification descended to the localization.
Source: Stacks 015F, 04VG (blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable def coefficientComplexDerivedFieldUnit :=
  Functor.mapDerivedCategoryNatIso (coefficientComplexFieldUnit.{u, v} l E) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The integral associator descended with its composite factorization isomorphism.
Source: Stacks 015F, 04VG (blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable def coefficientComplexDerivedIntegralAssoc :=
  (Functor.mapDerivedCategoryCompIso (coefficientComplexIntegralTensor.{u, v} l E L ι)
    (coefficientComplexIntegralTensor.{u, v} l L M κ)).symm ≪≫
  Functor.mapDerivedCategoryNatIso (coefficientComplexIntegralAssoc.{u, v} l E L ι M κ)

/-- The field associator descended with its composite factorization isomorphism.
Source: Stacks 015F, 04VG (blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable def coefficientComplexDerivedFieldAssoc :=
  (Functor.mapDerivedCategoryCompIso (coefficientComplexFieldTensor.{u, v} l E L ι)
    (coefficientComplexFieldTensor.{u, v} l L M κ)).symm ≪≫
  Functor.mapDerivedCategoryNatIso (coefficientComplexFieldAssoc.{u, v} l E L ι M κ)

end WeilConjectures

namespace WeilConjectures

/-- Factorization for a composite of two exact ordinary coefficient tensors.
Source: Stacks 015F, 04VG (blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable def coefficientComplexDerivedFactors
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} S)
    (G : ModuleCat.{max u v} S ⥤ ModuleCat.{max u v} T)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    (F ⋙ G).mapDerivedCategoryFactors

end WeilConjectures

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The specified generator formula for a natural isomorphism of cochain functors.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
def coefficientComplexChainFormula
    (β : (coefficientComplexIntegralTensor.{u, v} l E L ι ⋙
        coefficientComplexRationalize.{u, v} l L).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (coefficientComplexRationalize.{u, v} l E ⋙
        coefficientComplexFieldTensor.{u, v} l E L ι).mapHomologicalComplex
          (ComplexShape.up ℤ)) : Prop :=
  ∀ (N : CochainComplex (ModuleCat.{max u v} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (r : ℤ) (n : N.X r) (a : Padic.coefficientExtensionIntegers l L) (b : L),
    ((β.hom.app N).f r)
      (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
        (Padic.coefficientExtensionIntegers l L).subtype]
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion l E L ι] n)) =
      (b * (a : L)) ⊗ₜ[E, ι.toRingHom]
        ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          (Padic.coefficientExtensionIntegers l E).subtype] n)

/-- The full chain comparison and its uniquely specified descent.
Source: blueprint coefficient-point paragraph; Stacks 00CX, 015F and 04VG
(blueprint: lem-weil-coefficient-complex-rationalization).
Proof: steps 3--4 construct the mutually inverse balanced maps on modules, with the
stated formulas. An element x of E is an actual field element, including a/s for any
nonzero integer s: equality of fractions as'=a's gives the same x and hence the same
image. The same applies to b in L in either formula. Step 5 applies these maps in each
degree; naturality for the differentials gives the chain-map equations. Generators in
each degree prove uniqueness for any natural chain isomorphism with this formula.
Step 6 applies lem-weil-pbc-exact-functor-derived-factorization to all four functors,
using their exactness above and the abelian module categories. Thus they preserve
quasi-isomorphisms without boundedness hypotheses. Apply parts (2) and (3) of
lem-weil-pbc-localization-universal-property to descend beta. The canonical composite
factorizations give exactly the last displayed equation. Naturality is for every
morphism of the localization, including inverses of quasi-isomorphisms.
-/
theorem coefficientComplexComparison_spec :
    coefficientComplexChainFormula.{u, v} l E L ι
      (coefficientComplexChainBeta.{u, v} l E L ι) ∧
    (∀ β, coefficientComplexChainFormula.{u, v} l E L ι β →
      β = coefficientComplexChainBeta.{u, v} l E L ι) ∧
    (∀ (N : CochainComplex (ModuleCat.{max u v}
          (Padic.coefficientExtensionIntegers l E)) ℤ)
        (r : ℤ) (n : N.X r) (x : E) (b : L),
      (((coefficientComplexChainBeta.{u, v} l E L ι).inv.app N).f r)
        (b ⊗ₜ[E, ι.toRingHom]
          (x ⊗ₜ[Padic.coefficientExtensionIntegers l E,
            (Padic.coefficientExtensionIntegers l E).subtype] n)) =
        (b * ι x) ⊗ₜ[Padic.coefficientExtensionIntegers l L,
          (Padic.coefficientExtensionIntegers l L).subtype]
          ((1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[
            Padic.coefficientExtensionIntegers l E,
            integralScalarIntegerInclusion l E L ι] n)) ∧
    HomologicalComplex.preservesQuasiIso
      ((coefficientComplexIntegralTensor.{u, v} l E L ι).mapHomologicalComplex
        (ComplexShape.up ℤ)) ∧
    HomologicalComplex.preservesQuasiIso
      ((coefficientComplexRationalize.{u, v} l E).mapHomologicalComplex (ComplexShape.up ℤ)) ∧
    HomologicalComplex.preservesQuasiIso
      ((coefficientComplexRationalize.{u, v} l L).mapHomologicalComplex (ComplexShape.up ℤ)) ∧
    HomologicalComplex.preservesQuasiIso
      ((coefficientComplexFieldTensor.{u, v} l E L ι).mapHomologicalComplex
        (ComplexShape.up ℤ)) ∧
    (∀ N : CochainComplex (ModuleCat.{max u v}
        (Padic.coefficientExtensionIntegers l E)) ℤ,
      (coefficientComplexDerivedBeta.{u, v} l E L ι).hom.app (DerivedCategory.Q.obj N) ≫
        (coefficientComplexDerivedFactors (coefficientComplexRationalize.{u, v} l E)
          (coefficientComplexFieldTensor.{u, v} l E L ι)).hom.app N =
      (coefficientComplexDerivedFactors (coefficientComplexIntegralTensor.{u, v} l E L ι)
          (coefficientComplexRationalize.{u, v} l L)).hom.app N ≫
        DerivedCategory.Q.map ((coefficientComplexChainBeta.{u, v} l E L ι).hom.app N)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N r n a b
    exact coefficientBeta_formula l E L ι (N.X r) a b n
  · intro β hβ
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply HomologicalComplex.hom_ext
    intro r
    apply scalarDouble_hom_ext
    intro n
    exact (hβ N r n 1 1).trans
      (coefficientBeta_formula l E L ι (N.X r) 1 1 n).symm
  · intro N r n x b
    apply (ConcreteCategory.bijective_of_isIso
      ((coefficientComplexBeta.{u, v} l E L ι).hom.app (N.X r))).1
    change (coefficientComplexBeta.{u, v} l E L ι).hom.app (N.X r)
      ((coefficientComplexBeta.{u, v} l E L ι).inv.app (N.X r) _) = _
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id_app, ModuleCat.id_apply,
      coefficientBeta_formula, Subring.coe_one, mul_one]
    let : Algebra E L := ι.toRingHom.toAlgebra
    rw [show x ⊗ₜ[Padic.coefficientExtensionIntegers l E,
        (Padic.coefficientExtensionIntegers l E).subtype] n =
        x • ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          (Padic.coefficientExtensionIntegers l E).subtype] n) from
      (ModuleCat.ExtendScalars.smul_tmul _ x 1 n).trans (by rw [mul_one]) |>.symm]
    erw [← TensorProduct.smul_tmul]
    change (ι x * b) ⊗ₜ[E, ι.toRingHom] _ = _
    rw [mul_comm]
  · exact Functor.preservesQuasiIso_mapHomologicalComplex _ _
  · exact Functor.preservesQuasiIso_mapHomologicalComplex _ _
  · exact Functor.preservesQuasiIso_mapHomologicalComplex _ _
  · exact Functor.preservesQuasiIso_mapHomologicalComplex _ _
  · intro N
    simp only [coefficientComplexDerivedBeta, coefficientComplexDerivedFactors,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [Functor.mapDerivedCategoryNatIso_fac]
    rfl

end WeilConjectures

namespace WeilConjectures

private theorem deriveCoefficientTower
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category D₀] [Category D₁] [Category D₂]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian D₀] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₂ ⥤ D₂)
    (Q : C₀ ⥤ D₀) (R : C₁ ⥤ D₁) (V : D₀ ⥤ D₁) (W : D₁ ⥤ D₂)
    (I : C₀ ⥤ C₂) (J : D₀ ⥤ D₂)
    [F.Additive] [G.Additive] [H.Additive] [Q.Additive] [R.Additive]
    [V.Additive] [W.Additive] [I.Additive] [J.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (a : F ⋙ G ≅ I) (b : I ⋙ H ≅ Q ⋙ J) (c : G ⋙ H ≅ R ⋙ W)
    (d : F ⋙ R ≅ Q ⋙ V) (e : V ⋙ W ≅ J)
    (h : Functor.isoWhiskerRight a H ≪≫ b =
      Functor.isoWhiskerLeft F c ≪≫ Functor.isoWhiskerRight d W ≪≫
        Functor.isoWhiskerLeft Q e) (K : DerivedCategory C₀) :
    H.mapDerivedCategory.map
        (((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
          Functor.mapDerivedCategoryNatIso a).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso b).hom.app K =
      (Functor.mapDerivedCategorySquareIso c).hom.app (F.mapDerivedCategory.obj K) ≫
        W.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso d).hom.app K) ≫
        ((Functor.mapDerivedCategoryCompIso V W).symm ≪≫
          Functor.mapDerivedCategoryNatIso e).hom.app (Q.mapDerivedCategory.obj K) := by
  have hm := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom) h
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hm
  have ha := Functor.mapDerivedCategoryNatIso_isoWhiskerRight a H
  have hc := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F c
  have hd := Functor.mapDerivedCategoryNatIso_isoWhiskerRight d W
  have he := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft Q e
  have hF := Functor.mapDerivedCategoryCompIso_assoc F G H
  have hR := Functor.mapDerivedCategoryCompIso_assoc F R W
  have hQ := Functor.mapDerivedCategoryCompIso_assoc Q V W
  have ht :
      Functor.whiskerRight
        ((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
          Functor.mapDerivedCategoryNatIso a).hom H.mapDerivedCategory ≫
        (Functor.mapDerivedCategorySquareIso b).hom =
      Functor.whiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategorySquareIso c).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategorySquareIso d).hom
          W.mapDerivedCategory ≫
        Functor.whiskerLeft Q.mapDerivedCategory
          ((Functor.mapDerivedCategoryCompIso V W).symm ≪≫
            Functor.mapDerivedCategoryNatIso e).hom := by
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso (F ⋙ G) H).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategoryCompIso F G).hom
        H.mapDerivedCategory)).mp
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
    simp only [← Functor.whiskerRight_comp_assoc, Iso.hom_inv_id_assoc]
    rw [← reassoc_of% ha, Iso.hom_inv_id_assoc]
    rw [← reassoc_of% hF]
    simp only [← Functor.whiskerLeft_comp_assoc, Iso.hom_inv_id_assoc]
    simp only [Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
    rw [← reassoc_of% hc, reassoc_of% hR]
    simp only [← Functor.whiskerRight_comp_assoc, Iso.hom_inv_id_assoc]
    simp only [Functor.whiskerRight_comp, Category.assoc]
    rw [← reassoc_of% hd, ← reassoc_of% hQ]
    simp only [← Functor.whiskerLeft_comp_assoc, Iso.hom_inv_id,
      Functor.whiskerLeft_id', Category.id_comp]
    rw [← he, reassoc_of% hm]
  exact congr_app ht K

private theorem deriveCoefficientUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (A : C ⥤ C) (Q : C ⥤ D) (V : D ⥤ D)
    [A.Additive] [Q.Additive] [V.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (a : A ≅ 𝟭 C) (v : V ≅ 𝟭 D) (β : A ⋙ Q ≅ Q ⋙ V)
    (h : β ≪≫ Functor.isoWhiskerLeft Q v = Functor.isoWhiskerRight a Q)
    (K : DerivedCategory C) :
    (Functor.mapDerivedCategorySquareIso β).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso v ≪≫
          Functor.mapDerivedCategoryIdIso D).hom.app (Q.mapDerivedCategory.obj K) =
      Q.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso a ≪≫
          Functor.mapDerivedCategoryIdIso C).hom.app K) := by
  have hm := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom) h
  rw [Functor.mapDerivedCategoryNatIso_trans] at hm
  have hwl := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft Q v
  have hwr := Functor.mapDerivedCategoryNatIso_isoWhiskerRight a Q
  have hur := Functor.mapDerivedCategoryCompIso_comp_id Q
  have hul := Functor.mapDerivedCategoryCompIso_id_comp Q
  have heq :
      (Functor.mapDerivedCategorySquareIso β).hom ≫
        Functor.whiskerLeft Q.mapDerivedCategory
          (Functor.mapDerivedCategoryNatIso v ≪≫
            Functor.mapDerivedCategoryIdIso D).hom =
      Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso a ≪≫
          Functor.mapDerivedCategoryIdIso C).hom Q.mapDerivedCategory := by
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
    rw [← cancel_epi (Functor.mapDerivedCategoryCompIso A Q).hom,
      Iso.hom_inv_id_assoc]
    rw [← reassoc_of% hwl, hur]
    erw [Category.comp_id]
    rw [hm, ← reassoc_of% hwr, hul]
    erw [Category.comp_id]
  exact congr_app heq K

private theorem scalarTransport_tmul {R S : Type u} [CommRing R] [CommRing S]
    (f g : R →+* S) (h : f = g) (P : ModuleCat.{max u v} R) (s : S) (n : P) :
    (eqToIso (congrArg (ModuleCat.extendScalars.{u, u, max u v}) h)).hom.app P
      (s ⊗ₜ[R, f] n) = s ⊗ₜ[R, g] n := by
  subst g
  rfl

private theorem coefficientModuleUnit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (P : ModuleCat.{max u v} (Padic.coefficientExtensionIntegers l E)) :
    (coefficientComplexBeta.{u, v} l E E (AlgHom.id (Padic l) E)).hom.app P ≫
      (coefficientComplexFieldUnit.{u, v} l E).hom.app
        ((coefficientComplexRationalize.{u, v} l E).obj P) =
    (coefficientComplexRationalize.{u, v} l E).map
      ((coefficientComplexIntegralUnit.{u, v} l E).hom.app P) := by
  refine scalarDouble_hom_ext (integralScalarIntegerInclusion l E E
    (AlgHom.id (Padic l) E)) (Padic.coefficientExtensionIntegers l E).subtype
    P _ _ _ (fun n ↦ ?_)
  erw [ModuleCat.comp_apply,
    coefficientBeta_formula l E E (AlgHom.id (Padic l) E) P 1 1 n]
  simp only [Subring.coe_one, mul_one]
  erw [ModuleCat.extendScalarsId_hom_app_one_tmul]
  erw [ModuleCat.ExtendScalars.map_tmul]
  apply congrArg (fun x : P ↦ (1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
    (Padic.coefficientExtensionIntegers l E).subtype] x)
  dsimp only [coefficientComplexIntegralUnit, Iso.trans_hom, NatTrans.comp_app]
  erw [ModuleCat.comp_apply, scalarTransport_tmul,
    ModuleCat.extendScalarsId_hom_app_one_tmul]
  exact coefficientComplexIntegerIdentity l E

private theorem coefficientModuleTower
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (κ : L →ₐ[Padic l] M)
    (P : ModuleCat.{max u v} (Padic.coefficientExtensionIntegers l E)) :
    (coefficientComplexRationalize.{u, v} l M).map
      ((coefficientComplexIntegralAssoc.{u, v} l E L ι M κ).hom.app P) ≫
      (coefficientComplexBeta.{u, v} l E M (κ.comp ι)).hom.app P =
    (coefficientComplexBeta.{u, v} l L M κ).hom.app
        ((coefficientComplexIntegralTensor.{u, v} l E L ι).obj P) ≫
      (coefficientComplexFieldTensor.{u, v} l L M κ).map
        ((coefficientComplexBeta.{u, v} l E L ι).hom.app P) ≫
      (coefficientComplexFieldAssoc.{u, v} l E L ι M κ).hom.app
        ((coefficientComplexRationalize.{u, v} l E).obj P) := by
  apply scalarTriple_hom_ext
  intro n
  simp only [ModuleCat.comp_apply]
  change (coefficientComplexBeta.{u, v} l E M (κ.comp ι)).hom.app P
      ((1 : M) ⊗ₜ[Padic.coefficientExtensionIntegers l M,
        (Padic.coefficientExtensionIntegers l M).subtype]
        ((ModuleCat.extendScalarsComp (integralScalarIntegerInclusion l E L ι)
          (integralScalarIntegerInclusion l L M κ)).inv.app P
          ((1 : Padic.coefficientExtensionIntegers l M) ⊗ₜ[
            Padic.coefficientExtensionIntegers l L, integralScalarIntegerInclusion l L M κ]
            ((1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[
              Padic.coefficientExtensionIntegers l E,
              integralScalarIntegerInclusion l E L ι] n)))) = _
  erw [scalarComp_inv_tmul]
  simp only [map_one, mul_one]
  erw [coefficientBeta_formula, coefficientBeta_formula]
  simp only [Subring.coe_one, mul_one]
  erw [ModuleCat.ExtendScalars.map_tmul, coefficientBeta_formula]
  simp only [Subring.coe_one, mul_one, coefficientComplexFieldAssoc, Iso.symm_hom]
  erw [scalarComp_inv_tmul]
  simp only [map_one, mul_one]

/-- Identity and mixed integral/field tower coherence, both before and after localization.
Source: blueprint main-20261015, `def-weil-finite-coefficient-point`, final paragraph;
Stacks 00CX and 04VG (blueprint: lem-weil-coefficient-complex-rationalization).
Proof: step 5 identifies both sides of beta at E=E with rationalization by multiplication;
both send b tensor (a tensor n) to ba tensor n. This gives the first equality.
For step 7, on d tensor (c tensor (a tensor n)), the integral-association route gives
(d*c)*a tensor (1 tensor n), with inclusions into M understood. The beta/beta/field-
association route gives d*(c*a) tensor (1 tensor n). Associativity in M gives equality.
The calculation is degreewise and works for unbounded N, without dividing n. The field
coefficients are arbitrary, including fractions; tensor balancing and equality in M
make the calculation independent of every fraction presentation. Pure tensors generate,
so the chain maps are equal. Step 8 applies parts (2) and (3) of
lem-weil-pbc-localization-universal-property: the canonical factorizations used in each
of the definitions restrict the derived paths to these chain paths. Full faithfulness
of restriction along Q makes the derived paths equal. This also descends the unit law.
All components are natural transformations, so the assertions cover arbitrary derived
morphisms and not only images of chain morphisms. Exactness, chain uniqueness, the
forward and inverse formulas, and the descent characterization are the other declarations
`coefficientComplexTensors_exact` and `coefficientComplexComparison_spec` of this node.
-/
theorem coefficientComplexRationalization
    (l : ℕ) [Fact l.Prime]
    (Q : Type u) [Field Q] [Algebra (Padic l) Q] [IsAlgClosure (Padic l) Q]
    (E L M : Padic.FiniteCoefficientFields l Q) (hEL : E ≤ L) (hLM : L ≤ M)
    (N : CochainComplex
      (ModuleCat.{max u v} (Padic.coefficientExtensionIntegers l E.val)) ℤ)
    (K : DerivedCategory
      (ModuleCat.{max u v} (Padic.coefficientExtensionIntegers l E.val))) :
    ((coefficientComplexChainBeta.{u, v} l E.val E.val (AlgHom.id (Padic l) E.val)).hom.app N ≫
        (NatIso.mapHomologicalComplex (coefficientComplexFieldUnit.{u, v} l E.val)
          (ComplexShape.up ℤ)).hom.app
          (((coefficientComplexRationalize.{u, v} l E.val).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) =
      ((coefficientComplexRationalize.{u, v} l E.val).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        ((NatIso.mapHomologicalComplex (coefficientComplexIntegralUnit.{u, v} l E.val)
          (ComplexShape.up ℤ)).hom.app N)) ∧
    (((coefficientComplexRationalize.{u, v} l M.val).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        ((NatIso.mapHomologicalComplex
          (coefficientComplexIntegralAssoc.{u, v} l E.val L.val (IntermediateField.inclusion hEL)
            M.val (IntermediateField.inclusion hLM)) (ComplexShape.up ℤ)).hom.app N) ≫
        (coefficientComplexChainBeta.{u, v} l E.val M.val
          ((IntermediateField.inclusion hLM).comp (IntermediateField.inclusion hEL))).hom.app N =
      (coefficientComplexChainBeta.{u, v} l L.val M.val
        (IntermediateField.inclusion hLM)).hom.app
        (((coefficientComplexIntegralTensor.{u, v} l E.val L.val
          (IntermediateField.inclusion hEL)).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
      ((coefficientComplexFieldTensor.{u, v} l L.val M.val
        (IntermediateField.inclusion hLM)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((coefficientComplexChainBeta.{u, v} l E.val L.val
          (IntermediateField.inclusion hEL)).hom.app N) ≫
      (NatIso.mapHomologicalComplex
        (coefficientComplexFieldAssoc.{u, v} l E.val L.val (IntermediateField.inclusion hEL)
          M.val (IntermediateField.inclusion hLM)) (ComplexShape.up ℤ)).hom.app
        (((coefficientComplexRationalize.{u, v} l E.val).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)) ∧
    ((coefficientComplexDerivedBeta.{u, v} l E.val E.val (AlgHom.id (Padic l) E.val)).hom.app K ≫
        (coefficientComplexDerivedFieldUnit.{u, v} l E.val).hom.app
          ((coefficientComplexRationalize.{u, v} l E.val).mapDerivedCategory.obj K) =
      (coefficientComplexRationalize.{u, v} l E.val).mapDerivedCategory.map
        ((coefficientComplexDerivedIntegralUnit.{u, v} l E.val).hom.app K)) ∧
    ((coefficientComplexRationalize.{u, v} l M.val).mapDerivedCategory.map
        ((coefficientComplexDerivedIntegralAssoc.{u, v} l E.val L.val
          (IntermediateField.inclusion hEL) M.val (IntermediateField.inclusion hLM)).hom.app K) ≫
        (coefficientComplexDerivedBeta.{u, v} l E.val M.val
          ((IntermediateField.inclusion hLM).comp (IntermediateField.inclusion hEL))).hom.app K =
      (coefficientComplexDerivedBeta.{u, v} l L.val M.val
        (IntermediateField.inclusion hLM)).hom.app
        ((coefficientComplexIntegralTensor.{u, v} l E.val L.val
          (IntermediateField.inclusion hEL)).mapDerivedCategory.obj K) ≫
      (coefficientComplexFieldTensor.{u, v} l L.val M.val
        (IntermediateField.inclusion hLM)).mapDerivedCategory.map
        ((coefficientComplexDerivedBeta.{u, v} l E.val L.val
          (IntermediateField.inclusion hEL)).hom.app K) ≫
      (coefficientComplexDerivedFieldAssoc.{u, v} l E.val L.val
        (IntermediateField.inclusion hEL) M.val (IntermediateField.inclusion hLM)).hom.app
        ((coefficientComplexRationalize.{u, v} l E.val).mapDerivedCategory.obj K)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply HomologicalComplex.hom_ext
    intro r
    exact coefficientModuleUnit l E.val (N.X r)
  · apply HomologicalComplex.hom_ext
    intro r
    exact coefficientModuleTower l E.val L.val (IntermediateField.inclusion hEL)
      M.val (IntermediateField.inclusion hLM) (N.X r)
  · apply deriveCoefficientUnit
    apply Iso.ext
    apply NatTrans.ext
    funext P
    exact coefficientModuleUnit l E.val P
  · apply deriveCoefficientTower
    apply Iso.ext
    apply NatTrans.ext
    funext P
    exact coefficientModuleTower l E.val L.val (IntermediateField.inclusion hEL)
      M.val (IntermediateField.inclusion hLM) P

end WeilConjectures
