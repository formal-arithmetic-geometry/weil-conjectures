/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Sheaf.Paper.PointSectionsFiniteness
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.PointFdQbarCategory
public import Mathlib.Algebra.Category.ModuleCat.Ulift

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Flat.Localization

/-!
# The four coefficient fibre functors at the geometric point

Source: Weil blueprint, `def-weil-finite-coefficient-point`, order 1509
(blueprint: def-weil-finite-coefficient-point).

Evaluation is the recorded final-object sections functor. Integral coefficients act
through the constant-to-completion map. Rationalization tensors sections with the
fraction field. The small point target is connected to the section universe by the
fully faithful module universe lift, restricted to bounded finite-dimensional objects.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The chosen geometric base field is algebraically closed.
Source: blueprint global finite-field datum, order 411
(blueprint: def-weil-finite-coefficient-point). -/
noncomputable instance pointFibreBaseIsAlgClosed : IsAlgClosed D.k :=
  IsAlgClosure.isAlgClosed D.k₀

/-- The fully faithful change of coefficient and module size, with the same scalar action.
Source: blueprint order 1509, point targets
(blueprint: def-weil-finite-coefficient-point). -/
noncomputable abbrev pointFibreModuleLift (F : Type u) [Field F] :
    ModuleCat.{u} F ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} F) :=
  ModuleCat.uliftFunctor.{u + 1, u} F ⋙
    ModuleCat.restrictScalars.{u + 1, u + 1, u}
      (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).toRingHom

/-- Exactness and additivity of the carrier lift with its coefficient transport.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point).
Proof: carrier lift preserves kernels and cokernels by the module equivalence on
underlying elements. Restriction along the coefficient ring equivalence preserves
all limits and colimits; both operations add morphisms pointwise. -/
theorem pointFibreModuleLift_exact (F : Type u) [Field F] :
    (pointFibreModuleLift F).Additive ∧
      PreservesFiniteLimits (pointFibreModuleLift F) ∧
      PreservesFiniteColimits (pointFibreModuleLift F) := by
  let h₁ : PreservesFiniteLimits (ModuleCat.uliftFunctor.{u + 1, u} F) := inferInstance
  let h₂ : PreservesFiniteColimits (ModuleCat.uliftFunctor.{u + 1, u} F) := inferInstance
  let h₃ : PreservesFiniteLimits
      (ModuleCat.restrictScalars.{u + 1, u + 1, u}
        (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).toRingHom) := inferInstance
  let h₄ : PreservesFiniteColimits
      (ModuleCat.restrictScalars.{u + 1, u + 1, u}
        (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).toRingHom) := inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Additivity of the explicit universe lift.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable instance pointFibreModuleLiftAdditive (F : Type u) [Field F] :
    (pointFibreModuleLift F).Additive := (pointFibreModuleLift_exact F).1

/-- Preservation of kernels by the explicit universe lift.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable instance pointFibreModuleLiftLimits (F : Type u) [Field F] :
    PreservesFiniteLimits (pointFibreModuleLift F) := (pointFibreModuleLift_exact F).2.1

/-- Preservation of cokernels by the explicit universe lift.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable instance pointFibreModuleLiftColimits (F : Type u) [Field F] :
    PreservesFiniteColimits (pointFibreModuleLift F) := (pointFibreModuleLift_exact F).2.2

/-- Universe lift preserves the bounded finite-dimensional predicate.
Source: blueprint order 1509, target categories
(blueprint: def-weil-finite-coefficient-point).
Proof: exact universe lift commutes with homology. Its module equivalence identifies
cohomology spaces and preserves their dimensions and the same finite support. -/
theorem pointFibreModuleLift_mem (F : Type u) [Field F]
    (K : (DerivedCategory.pointFiniteDimensional F).FullSubcategory) :
    DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} F)
      ((pointFibreModuleLift F).mapDerivedCategory.obj K.obj) := by
  sorry

/-- The actual universe lift on the point's bounded finite-dimensional target.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointFibreSizeLift (F : Type u) [Field F] :
    (DerivedCategory.pointFiniteDimensional F).FullSubcategory ⥤
      (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} F)).FullSubcategory :=
  (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} F)).lift
    ((DerivedCategory.pointFiniteDimensional F).ι ⋙ (pointFibreModuleLift F).mapDerivedCategory)
    (pointFibreModuleLift_mem F)

/-- The restricted universe lift is an equivalence, rather than an extra size assumption.
Source: blueprint order 1509, work in a universe containing the point categories
(blueprint: def-weil-finite-coefficient-point).
Proof: over a field every complex is isomorphic in the derived category to its graded
cohomology with zero differential. Bounded finite-dimensional cohomology therefore has
a bounded representative of finite-dimensional spaces, all of which are small. This
proves essential surjectivity. Maps between these representatives are their graded
linear maps; the universe lift is fully faithful on those maps. -/
theorem pointFibreSizeLift_equivalence (F : Type u) [Field F] :
    (pointFibreSizeLift F).IsEquivalence := by
  sorry

/-- The inverse of the specified universe lift, determined by its equivalence counit.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointFibreSizeDescent (F : Type u) [Field F] :
    (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} F)).FullSubcategory ⥤
      (DerivedCategory.pointFiniteDimensional F).FullSubcategory :=
  letI := pointFibreSizeLift_equivalence F
  (pointFibreSizeLift F).asEquivalence.inverse

/-- Exactness of evaluation after restriction along constant sections.
Source: blueprint order 1509, evaluation paragraph
(blueprint: def-weil-finite-coefficient-point).
Proof: point_proEtale_sections_exact makes evaluation at the final object exact.
Restriction of scalars preserves kernels and cokernels on underlying groups, hence
the composite preserves finite limits and finite colimits. -/
theorem pointFibreFinite_exact (A : Type u) [CommRing A] :
    PreservesFiniteLimits (pointFiniteSections D.k A) ∧
      PreservesFiniteColimits (pointFiniteSections D.k A) := by
  let A' := (constantSheaf.{u, u + 1, u + 1, u + 2}
    (Scheme.ProEt.topology (Spec (.of D.k))) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1, u} A))
  let : IsAlgClosed D.k := pointFibreBaseIsAlgClosed D
  let : PreservesFiniteLimits (pointModuleSections D.k A') :=
    ((point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2 A').1
  let : PreservesFiniteColimits (pointModuleSections D.k A') :=
    ((point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2 A').2.1
  change
    PreservesFiniteLimits
        (pointModuleSections D.k A' ⋙
          ModuleCat.restrictScalars (pointConstantSectionMap D.k A)) ∧
      PreservesFiniteColimits
        (pointModuleSections D.k A' ⋙
          ModuleCat.restrictScalars (pointConstantSectionMap D.k A))
  exact ⟨inferInstance, inferInstance⟩

/-- Kernel preservation for exact point sections.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable instance pointFibreFiniteLimits (A : Type u) [CommRing A] :
    PreservesFiniteLimits (pointFiniteSections D.k A) :=
  (pointFibreFinite_exact D A).1

/-- Cokernel preservation for exact point sections.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable instance pointFibreFiniteColimits (A : Type u) [CommRing A] :
    PreservesFiniteColimits (pointFiniteSections D.k A) :=
  (pointFibreFinite_exact D A).2

/-- Exact integral evaluation and flat fraction-field tensor in the recorded lift.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point).
Proof: evaluation is exact by point_proEtale_sections_exact; restriction along the
constant-section map is exact on underlying groups. The coefficient field is the
localization of its integer ring at the uniformizer, hence flat. ULift transports
these rings and tensor without altering the actions, kernels or cokernels. -/
theorem pointFibreIntegral_exact :
    PreservesFiniteLimits (pointIntegralSections l E D.k) ∧
      PreservesFiniteColimits (pointIntegralSections l E D.k) := by
  let : IsAlgClosed D.k := pointFibreBaseIsAlgClosed D
  let A := completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))
  let : PreservesFiniteLimits (pointModuleSections D.k A) :=
    ((point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2 A).1
  let : PreservesFiniteColimits (pointModuleSections D.k A) :=
    ((point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2 A).2.1
  change
    PreservesFiniteLimits
        (pointModuleSections D.k A ⋙
          ModuleCat.restrictScalars (pointIntegralSectionMap l E D.k)) ∧
      PreservesFiniteColimits
        (pointModuleSections D.k A ⋙
          ModuleCat.restrictScalars (pointIntegralSectionMap l E D.k))
  exact ⟨inferInstance, inferInstance⟩

/-- Flatness of the lifted fraction-field coefficient map.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point).
Proof: E is the localization of O_E at its uniformizer. Localization is flat,
so tensor preserves kernels; its adjunction preserves cokernels. -/
theorem pointFibreFraction_exact :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)) := by
  have hloc : IsLocalization.Away (Padic.coefficientExtensionUniformizer l E) E :=
    (Padic.coefficientExtension_localization_uniformizer.{u, u} l E).1
  have hflat : (algebraMap (Padic.coefficientExtensionIntegers l E) E).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat E (Submonoid.powers (Padic.coefficientExtensionUniformizer l E)))
  have hf : (pointIntegralToField l E).Flat :=
    ((RingHom.Flat.of_bijective
      (ULift.ringEquiv : ULift.{u + 1, u}
        (Padic.coefficientExtensionIntegers l E) ≃+*
          Padic.coefficientExtensionIntegers l E).bijective).comp hflat).comp
      (RingHom.Flat.of_bijective
        (ULift.ringEquiv : ULift.{u + 1, u} E ≃+* E).symm.bijective)
  refine ⟨ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf, ?_⟩
  let := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (pointIntegralToField l E)).leftAdjoint_preservesColimits
  infer_instance

/-- Kernel preservation for completed-coefficient evaluation.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable instance pointFibreIntegralLimits :
    PreservesFiniteLimits (pointIntegralSections l E D.k) :=
  (pointFibreIntegral_exact D l E).1

/-- Cokernel preservation for completed-coefficient evaluation.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable instance pointFibreIntegralColimits :
    PreservesFiniteColimits (pointIntegralSections l E D.k) :=
  (pointFibreIntegral_exact D l E).2

/-- Kernel preservation for the fraction-field tensor.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable instance pointFibreFractionLimits :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)) := (pointFibreFraction_exact l E).1

/-- Cokernel preservation for the fraction-field tensor.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable instance pointFibreFractionColimits :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)) := (pointFibreFraction_exact l E).2

/-- Integral derived sections with the recorded canonical coefficient action.
Source: blueprint order 1509, clause 2
(blueprint: def-weil-finite-coefficient-point). -/
noncomputable abbrev pointFibreIntegralAmbient :=
  (pointIntegralSections l E D.k).mapDerivedCategory

/-- Rational derived sections, tensoring with E after exact integral evaluation.
Source: blueprint order 1509, clause 3
(blueprint: def-weil-finite-coefficient-point). -/
noncomputable abbrev pointFibreRationalAmbient :
    DerivedCategory (scalarReductionSource.{u, u} l E (Spec (.of D.k))) ⥤
      DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} E)) :=
  pointFibreIntegralAmbient D l E ⋙
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)).mapDerivedCategory

include hl in
/-- The three section functors land in the recorded point targets.
Source: blueprint order 1509, clauses 1--3
(blueprint: def-weil-finite-coefficient-point).
Proof: represent the derived object by a cochain complex. Exact evaluation and flat
fraction-field tensor have the mapDerivedCategoryFactors comparison with termwise
sections. Apply all three clauses of lem-weil-point-sections-finiteness. Transport
along these isomorphisms and the canonical ULift coefficient equivalences. This
preserves finite support, finiteness, finite generation and derived completeness. -/
theorem pointFibre_sections_mem (n : ℕ) (hn : 1 ≤ n) :
    (∀ K : (intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k))).FullSubcategory,
      DerivedCategory.pointFiniteCohomology
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
        ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).mapDerivedCategory.obj
          K.obj)) ∧
    (∀ K : sfIntegralConstructibleCategory l E (Spec (.of D.k)),
      DerivedCategory.pointFgComplete
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
        (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})
        ((pointFibreIntegralAmbient D l E).obj K.obj) ∧
      DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)
        ((pointFibreRationalAmbient D l E).obj K.obj)) := by
  sorry

/-- Clause 1: exact final-object sections on finite-torsion constructible complexes.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointFiniteFibre (n : ℕ) (hn : 1 ≤ n) :
    (intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k))).FullSubcategory ⥤
      (DerivedCategory.pointFiniteCohomology
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))).FullSubcategory :=
  (DerivedCategory.pointFiniteCohomology
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))).lift
      ((intrinsicFiniteTorsionConstructible l E n hn (Spec (.of D.k))).ι ⋙
        (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).mapDerivedCategory)
      (pointFibre_sections_mem D l hl E n hn).1

/-- Clause 2: sections of completed integral modules, with their actual O_E action.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointIntegralFibre :
    sfIntegralConstructibleCategory l E (Spec (.of D.k)) ⥤
      (DerivedCategory.pointFgComplete
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
        (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})).FullSubcategory :=
  (DerivedCategory.pointFgComplete
    (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
    (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})).lift
      ((sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ pointFibreIntegralAmbient D l E)
      (fun K ↦ ((pointFibre_sections_mem D l hl E 1 (by decide)).2 K).1)

/-- O_E-linearity of the integral fibre on every derived morphism.
Source: blueprint order 1509, clause 2 (blueprint: def-weil-finite-coefficient-point).
Proof: the constant-to-completion map defines the source and section-module actions.
Evaluation is linear on chain maps. The equality survives localization on roofs, since
composition and inversion of quasi-isomorphisms commute with the coefficient action. -/
theorem pointIntegralFibre_linear
    (K M : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (a : Padic.coefficientExtensionIntegers l E) (f : K ⟶ M) :
    ((pointIntegralFibre D l hl E).map (a • f)).hom =
      ULift.up a • ((pointIntegralFibre D l hl E).map f).hom := by
  sorry

/-- Integral sections tensored with E, followed by the canonical descent of module size.
Source: blueprint order 1509, clause 3
(blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointIntegralRationalFibre :
    sfIntegralConstructibleCategory l E (Spec (.of D.k)) ⥤
      (DerivedCategory.pointFiniteDimensional E).FullSubcategory :=
  (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).lift
    ((sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙ pointFibreRationalAmbient D l E)
    (fun K ↦ ((pointFibre_sections_mem D l hl E 1 (by decide)).2 K).2) ⋙
      pointFibreSizeDescent E

/-- The unique extension to the raw rational Hom tensor groups, fixed on all pure tensors.
Source: blueprint order 1509, clause 3
(blueprint: def-weil-finite-coefficient-point).
Proof: exact sections are O_E-linear, and tensor with E converts integral scalar action
into multiplication in E. Extend each Hom map by the tensor universal property, using
the canonical localization-field equivalence. Identities and composition hold on pure
tensors and then by additivity. Objects and every pure-tensor image are specified, so
the tensor generators and functor extensionality prove uniqueness. -/
theorem pointRationalFibre_existsUnique :
    ∃! F : sfRationalConstructibleCategory l E (Spec (.of D.k)) ⥤
        (DerivedCategory.pointFiniteDimensional E).FullSubcategory,
      (∀ K, F.obj K = (pointIntegralRationalFibre D l hl E).obj K.obj) ∧
      (∀ (K M : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
        (f : K ⟶ M) (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        HEq (F.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K ⟶
            (sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj M)).hom
          ((sfRationalCoefficientEquiv l E a) •
            ((pointIntegralRationalFibre D l hl E).map f).hom)) := by
  sorry

/-- Clause 3: the rational point fibre, with the specified tensor-Hom action.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointRationalFibre :
    sfRationalConstructibleCategory l E (Spec (.of D.k)) ⥤
      (DerivedCategory.pointFiniteDimensional E).FullSubcategory :=
  (pointRationalFibre_existsUnique D l hl E).exists.choose

/-- The inverse coefficient-ring identification, without changing the module carrier.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable abbrev pointFibreCoefficientDown (F : Type u) [Field F] :
    ModuleCat.{u + 1} (ULift.{u + 1, u} F) ⥤ ModuleCat.{u + 1} F :=
  ModuleCat.restrictScalars.{u + 1, u, u + 1}
    (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).symm.toRingHom

/-- Coefficient identification is exact.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point).
Proof: the inverse coefficient identification is an equivalence, acting identically
on underlying additive groups and on maps. It preserves kernels and cokernels. -/
theorem pointFibreCoefficientDown_exact (F : Type u) [Field F] :
    PreservesFiniteLimits (pointFibreCoefficientDown F) ∧
      PreservesFiniteColimits (pointFibreCoefficientDown F) := by
  exact ⟨inferInstance, inferInstance⟩

/-- Exactness at kernels for coefficient identification.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable instance pointFibreCoefficientDownLimits (F : Type u) [Field F] :
    PreservesFiniteLimits (pointFibreCoefficientDown F) :=
  (pointFibreCoefficientDown_exact F).1

/-- Exactness at cokernels for coefficient identification.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable instance pointFibreCoefficientDownColimits (F : Type u) [Field F] :
    PreservesFiniteColimits (pointFibreCoefficientDown F) :=
  (pointFibreCoefficientDown_exact F).2

/-- Cancelling the coefficient lift is uniquely fixed on every module element.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point).
Proof: both carriers are ULift M. Send up x to up x; the two coefficient actions
are equal since the inverse ring identifications cancel. This is a linear
bijection natural in M. Every carrier element is up x, giving uniqueness. -/
theorem pointFibreLiftDown_existsUnique (F : Type u) [Field F] :
    ∃! e : pointFibreModuleLift F ⋙ pointFibreCoefficientDown F ≅
        ModuleCat.uliftFunctor.{u + 1, u} F,
      ∀ (M : ModuleCat.{u} F) (x : M), e.hom.app M (ULift.up x) = ULift.up x := by
  let e : pointFibreModuleLift F ⋙ pointFibreCoefficientDown F ≅
      ModuleCat.uliftFunctor.{u + 1, u} F :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        ((ModuleCat.restrictScalarsComp' _ _ _
          (ULift.ringEquiv : ULift.{u + 1, u} F ≃+* F).toRingHom_comp_symm_toRingHom.symm).symm
          ≪≫ ModuleCat.restrictScalarsId F) ≪≫
      Functor.rightUnitor _
  refine ⟨e, ?_, ?_⟩
  · intro M x
    rfl
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x⟩ := x
    exact he' M x

/-- The normalized cancellation of the two coefficient identifications in D(F).
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointFibreLiftDownIso (F : Type u) [Field F] :
    (pointFibreModuleLift F).mapDerivedCategory ⋙
        (pointFibreCoefficientDown F).mapDerivedCategory ≅
      (ModuleCat.uliftFunctor.{u + 1, u} F).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointFibreLiftDown_existsUnique F).exists.choose

/-- The rational coefficient transport is fixed by its formula on all pure tensors.
Source: blueprint order 1509, clause 3 (blueprint: def-weil-finite-coefficient-point).
Proof: the underlying integral section module is the same in both encodings.
The balanced map sends up a tensor n to a tensor n, and its inverse lifts a.
These formulas respect balancing because both constant coefficient maps are the
same after ULift. They are inverse, natural linear maps. Pure tensors generate,
so the natural isomorphism is unique. -/
theorem pointFibreRationalDown_existsUnique :
    ∃! e : pointIntegralSections l E D.k ⋙
        ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E) ⋙
        pointFibreCoefficientDown E ≅
      pointCompletedSections D.k l E ⋙ pointModuleRationalization l E,
      ∀ (M : scalarReductionSource.{u, u} l E (Spec (.of D.k)))
        (a : E) (x : (pointIntegralSections l E D.k).obj M),
        e.hom.app M (ULift.up a ⊗ₜ[ULift.{u + 1, u}
          (Padic.coefficientExtensionIntegers l E), pointIntegralToField l E] x) =
            a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
              (@id ((pointCompletedSections D.k l E).obj M) x) := by
  sorry

/-- The canonical identification of the two rational section encodings.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointFibreRationalDownIso :
    pointFibreRationalAmbient D l E ⋙
        (pointFibreCoefficientDown E).mapDerivedCategory ≅
      pointCompletedDerivedSections D.k l E ⋙ pointModuleDerivedRationalization l E :=
  letI := pointCompletedSectionsAdditive D.k l E
  letI := pointCompletedSectionsLimits D.k l E
  letI := pointCompletedSectionsColimits D.k l E
  letI := pointModuleRationalizationAdditive l E
  letI := pointModuleRationalizationLimits l E
  letI := pointModuleRationalizationColimits l E
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointFibreRationalDown_existsUnique D l E).exists.choose ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The common-lift rational object before descending its size.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointFibreRationalLarge
    (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).FullSubcategory :=
  ⟨(pointFibreRationalAmbient D l E).obj K.obj,
    ((pointFibre_sections_mem D l hl E 1 (by decide)).2 K).2⟩

/-- The specified size-descent counit identifies the small fibre with actual sections.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointIntegralRationalNormalization
    (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.obj
        ((pointIntegralRationalFibre D l hl E).obj K).obj ≅
      (pointModuleDerivedRationalization l E).obj
        ((pointCompletedDerivedSections D.k l E).obj K.obj) :=
  letI := pointFibreSizeLift_equivalence E
  (pointFibreLiftDownIso E).symm.app ((pointIntegralRationalFibre D l hl E).obj K).obj ≪≫
    (pointFibreCoefficientDown E).mapDerivedCategory.mapIso
      ((DerivedCategory.pointFiniteDimensional (ULift.{u + 1, u} E)).ι.mapIso
        ((pointFibreSizeLift E).asEquivalence.counitIso.app
          (pointFibreRationalLarge D l hl E K))) ≪≫
    (pointFibreRationalDownIso D l E).app K.obj

/-- The object identity fixed by rationalization's defining universal property.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointRationalFibreObjIso
    (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (pointRationalFibre D l hl E).obj K ≅ (pointIntegralRationalFibre D l hl E).obj K.obj :=
  eqToIso ((pointRationalFibre_existsUnique D l hl E).exists.choose_spec.1 K)

/-- Rational normalization with the specified raw-localization object equality inserted.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointRationalNormalization
    (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.obj
        ((pointRationalFibre D l hl E).obj K).obj ≅
      (pointModuleDerivedRationalization l E).obj
        ((pointCompletedDerivedSections D.k l E).obj K.obj.obj) :=
  (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory.mapIso
    ((DerivedCategory.pointFiniteDimensional E).ι.mapIso (pointRationalFibreObjIso D l hl E K)) ≪≫
      pointIntegralRationalNormalization D l hl E K.obj

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Scalar tensor commutes with carrier lift by the prescribed pure-tensor map.
Source: blueprint order 1509, clause 4 (blueprint: def-weil-finite-coefficient-point).
Proof: send up (a tensor x) to a tensor up x. Balancing is unchanged and the
inverse sends a tensor up x to up (a tensor x). The formulas commute with all
module maps. Pure tensors generate, giving uniqueness. -/
theorem pointFibreTensorLift_existsUnique :
    ∃! e : ModuleCat.extendScalars.{u, u, u} ι.toRingHom ⋙
        ModuleCat.uliftFunctor.{u + 1, u} L ≅
      ModuleCat.uliftFunctor.{u + 1, u} E ⋙
        ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom,
      ∀ (M : ModuleCat.{u} E) (a : L) (x : M),
        e.hom.app M (ULift.up (a ⊗ₜ[E, ι.toRingHom] x)) =
          a ⊗ₜ[E, ι.toRingHom] ULift.up x := by
  sorry

/-- The canonical tensor/lift comparison descended through localization.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointFibreTensorLiftIso :
    DerivedCategory.fieldDerivedScalarExtension ι.toRingHom ⋙
        (ModuleCat.uliftFunctor.{u + 1, u} L).mapDerivedCategory ≅
      (ModuleCat.uliftFunctor.{u + 1, u} E).mapDerivedCategory ⋙
        pointCoefficientFieldDerivedTensor l E L ι :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointFibreTensorLift_existsUnique l E L ι).exists.choose ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The rational scalar comparison is uniquely fixed by the recorded sections comparison.
Source: blueprint order 1509, clause 4 (blueprint: def-weil-finite-coefficient-point).
Proof: use pointRationalSectionsScalarExtensionIso on each integral object, with
pointIntegralConstructible_iff supplying its legacy predicate. Conjugate by the
specified size-descent counits and tensor/lift comparison. Full faithfulness of
size lift gives unique small components. Naturality holds on integral maps by the
recorded sections comparison; on arbitrary rational maps it follows by tensor
linearity and generation by pure tensors. Thus the components give a unique natural
isomorphism. Its unit and tower coherences are exactly those of the recorded phi,
since fully faithful lift detects equality. The redundant characteristic parameter
of scalar extension is fixed to zero, as in the general common-stage category. -/
theorem pointRationalFibreScalar_existsUnique :
    ∃! e : sfRationalScalarExtension l E (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙ pointRationalFibre D l hl L ≅
      pointRationalFibre D l hl E ⋙ DerivedCategory.pointFdScalarExtension ι.toRingHom,
      ∀ K : sfIntegralConstructibleCategory l E (Spec (.of D.k)),
        HEq
          ((ModuleCat.uliftFunctor.{u + 1, u} L).mapDerivedCategory.map
              ((e.hom.app ((sfRationalConstructibleLocalization l E
                (Spec (.of D.k))).obj K)).hom) ≫
            (pointFibreTensorLiftIso l E L ι).hom.app
              ((pointRationalFibre D l hl E).obj
                ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K)).obj ≫
            (pointCoefficientFieldDerivedTensor l E L ι).map
              (pointRationalNormalization D l hl E
                ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K)).hom)
          ((pointIntegralRationalNormalization D l hl L
              ((sfConstructibleIntegralScalarExtension 0 l
                (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι (Spec (.of D.k))).obj K)).hom ≫
            (pointRationalSectionsScalarExtensionIso l E L ι D hl K.obj
              ((pointIntegralConstructible_iff l E D hl K.obj).mpr K.property)).hom) := by
  sorry

/-- The normalized rational scalar comparison used on common-stage representatives.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointRationalFibreScalarIso :=
  (pointRationalFibreScalar_existsUnique D l hl E L ι).exists.choose

/-- The tensor tower comparison restricted to the recorded finite-dimensional targets.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointFibreFdTensorTower {F G H : Type u}
    [Field F] [Field G] [Field H] (f : F →+* G) (g : G →+* H) :
    DerivedCategory.pointFdScalarExtension f ⋙ DerivedCategory.pointFdScalarExtension g ≅
      DerivedCategory.pointFdScalarExtension (g.comp f) :=
  ((DerivedCategory.pointFiniteDimensional H).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (DerivedCategory.pointFiniteDimensional F).ι
      (DerivedCategory.fieldScalarTower f g))

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The point fibre at a finite stage, with the recorded Shrink coefficient identification.
Source: blueprint order 1509, clause 4 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointStageFibre (F : Padic.FiniteCoefficientFields l Ω) :
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω (Spec (.of D.k)) F ⥤
      (DerivedCategory.pointFiniteDimensional F.val).FullSubcategory :=
  pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) ⋙
    DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] F.val).toRingHom

/-- The small coefficient models give the same inclusion square as the actual subfields.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point).
Proof: coefficientInclusion is defined by conjugating the actual inclusion with the
Shrink algebra equivalences. Cancelling the equivalence with its inverse gives the
equality of ring maps, including repeated fields and identity inclusions. -/
theorem pointStageCoefficientSquare (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) :
    (Shrink.algEquiv ℚ_[l] G.val).toRingHom.comp
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h).toRingHom =
      (IntermediateField.inclusion h).toRingHom.comp
        (Shrink.algEquiv ℚ_[l] F.val).toRingHom := by
  have : IsAlgClosure ℚ_[l] Ω := inferInstance
  ext x
  simp [AlgebraicallyClosedCoefficients.coefficientInclusion]

/-- The coefficient-square comparison, made from the canonical tensor tower isomorphisms.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointStageTensorSquare
    (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) :
    DerivedCategory.pointFdScalarExtension
        (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h).toRingHom ⋙
        DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] G.val).toRingHom ≅
      DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] F.val).toRingHom ⋙
        DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom :=
  pointFibreFdTensorTower _ _ ≪≫
    eqToIso (congrArg DerivedCategory.pointFdScalarExtension
      (pointStageCoefficientSquare l Ω F G h)) ≪≫
    (pointFibreFdTensorTower _ _).symm

/-- The finite-stage sections comparison with both recorded coefficient transports.
Its inverse is the beta used to send common-stage representatives to the target.
Source: blueprint order 1509, clause 4 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointStageFibreScalarIso
    (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) :
    GeneralAlgebraicallyClosedCoefficients.stageTransition l Ω (Spec (.of D.k)) F G h ⋙
        pointStageFibre D l hl Ω G ≅
      pointStageFibre D l hl Ω F ⋙
        DerivedCategory.pointFdScalarExtension (IntermediateField.inclusion h).toRingHom :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
          (eqToIso ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
            l Ω (Spec (.of D.k))).exists.choose_spec.1 F G h))
          (pointRationalFibre D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G)) ≪≫
        pointRationalFibreScalarIso D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω G)
          (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F G h))
      (DerivedCategory.pointFdScalarExtension (Shrink.algEquiv ℚ_[l] G.val).toRingHom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pointStageTensorSquare l Ω F G h) ≪≫
    (Functor.associator _ _ _).symm

/-- The algebraically closed fibre keeps the finite coefficient stage of its object.
Source: blueprint order 1509, clause 4 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointQbarFibreObj
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    DerivedCategory.PointFdQbar l Ω :=
  ⟨A.stage, (pointStageFibre D l hl Ω A.stage).obj A.obj⟩

/-- The image of a common-stage representative: conjugate its fibre by phi and phi inverse.
Source: blueprint order 1509, clause 4 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointQbarFibreRepresentative
    (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (F : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ F) (hB : B.stage ≤ F)
    (f : A.toStage hA ⟶ B.toStage hB) :
    pointQbarFibreObj D l hl Ω A ⟶ pointQbarFibreObj D l hl Ω B :=
  (DerivedCategory.pointFdQbarStageComp l Ω hA).inv.app
      ((pointStageFibre D l hl Ω A.stage).obj A.obj) ≫
    (DerivedCategory.pointFdQbarStage l Ω F).map
      ((pointStageFibreScalarIso D l hl Ω A.stage F hA).inv.app A.obj ≫
        (pointStageFibre D l hl Ω F).map f ≫
          (pointStageFibreScalarIso D l hl Ω B.stage F hB).hom.app B.obj) ≫
    (DerivedCategory.pointFdQbarStageComp l Ω hB).hom.app
      ((pointStageFibre D l hl Ω B.stage).obj B.obj)

/-- The common-stage formula uniquely defines the fourth fibre functor.
Source: blueprint order 1509, clause 4 (blueprint: def-weil-finite-coefficient-point).
Proof: use the displayed object map. Every source morphism has a common-stage
representative by the recorded common-stage calculus. Send it to
pointQbarFibreRepresentative. The scalar-extension coherence of the recorded
sections comparison, and the canonical tensor towers and Shrink square, identify
the two images after any enlargement of the common field. Thus equivalent
representatives give equal maps. At a common stage, the two middle phi factors
cancel in a composite; functoriality of the rational fibre proves composition.
For the identity the inverse phi factors cancel. The object formula and the map
formula on all representatives determine the functor uniquely. -/
theorem pointQbarFibre_existsUnique :
    ∃! F : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)) ⥤
        DerivedCategory.PointFdQbar l Ω,
      (∀ A, F.obj A = pointQbarFibreObj D l hl Ω A) ∧
      (∀ (A B : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
        (G : Padic.FiniteCoefficientFields l Ω) (hA : A.stage ≤ G) (hB : B.stage ≤ G)
        (f : A.toStage hA ⟶ B.toStage hB),
        HEq (F.map (StageSystem.PairCategory.mkHom G hA hB f))
          (pointQbarFibreRepresentative D l hl Ω A B G hA hB f)) := by
  sorry

/-- Clause 4: stagewise sections, with the prescribed action on every common-stage morphism.
Together with pointFiniteFibre, pointIntegralFibre and pointRationalFibre, this is the
four-stage geometric-point fibre. Equivalence is a separate node, not assumed here.
Source: blueprint order 1509 (blueprint: def-weil-finite-coefficient-point). -/
noncomputable def pointQbarFibre :
    generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)) ⥤
      DerivedCategory.PointFdQbar l Ω :=
  (pointQbarFibre_existsUnique D l hl Ω).exists.choose

end WeilConjectures
