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
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.LinearAlgebra.TensorProduct.Basic

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
  sorry

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
  sorry

/-- The comparison selected by its unique generator formula.
Source: blueprint coefficient-point paragraph; Stacks 00CX
(blueprint: lem-weil-coefficient-complex-rationalization). -/
noncomputable def coefficientComplexBeta :=
  (coefficientComplexBeta_existsUnique.{u, v} l E L ι).exists.choose

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
  sorry

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
  sorry

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
  sorry

end WeilConjectures

namespace WeilConjectures

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
  sorry

end WeilConjectures
