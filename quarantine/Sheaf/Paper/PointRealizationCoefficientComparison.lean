/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.CondensedERealization
public import Sheaf.Paper.CondensedPointSupertrace
public import Sheaf.Paper.FdCoefficientComparison
public import Sheaf.Paper.FiniteCoefficientPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-!
# Point realization and condensed coefficient extension

Source: Weil blueprint, main-20261015, sec-zeta-weil/sk-thm-rationality,
first sentence of the proof (blueprint: lem-zl-point-realization-coefficient-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped TensorProduct CategoryTheory.Obj

namespace WeilConjectures.PointRealizationComparison

/-- The existing Grothendieck-derived model of a module category, at its Hom universe.
Source: rationality point comparison, coefficient-size convention
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance moduleDerived (B : Type u) [CommRing B] :
    HasDerivedCategory.{u} (ModuleCat.{u} B) :=
  HasDerivedCategory.ofIsGrothendieckAbelian.{u} (ModuleCat.{u} B)

/-- The recorded small pro-etale site at the fixed coefficient size. This adapter
fixes the otherwise unused coefficient-size parameter of the generic site instance.
Source: rationality point comparison, coefficient convention
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance (priority := 3000) siteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _

/-- The same finite extension in the scheme universe, without identifying universes.
Source: rationality proof, point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev FieldModel (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l) :=
  ULift.{u} E.val

/-- The canonical lift of vector spaces, with coefficient action transported by `down`.
Source: rationality proof, point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev moduleLift (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l) :
    ModuleCat.{0} E.val ⥤ ModuleCat.{u} (FieldModel.{u} l E) :=
  ModuleCat.uliftFunctor.{u, 0} E.val ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : FieldModel.{u} l E ≃+* E.val).toRingHom

/-- The inherited norm on the lifted coefficient field.
Source: rationality point comparison, coefficient convention
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance fieldModelNormed (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) : NormedField (FieldModel.{u} l E) :=
  NormedField.induced _ E.val
    (ULift.ringEquiv : FieldModel.{u} l E ≃+* E.val).toRingHom ULift.down_injective

/-- Its original Q_l normed algebra structure.
Source: rationality point comparison, coefficient convention
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance fieldModelNormedAlgebra (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) : NormedAlgebra ℚ_[l] (FieldModel.{u} l E) where
  toAlgebra := inferInstance
  norm_smul_le a x := norm_smul_le a x.down

/-- Lifting the field does not change its finite degree or the finite-dimensional
cohomology predicate. Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison).
Proof: ULift.moduleEquiv is a Q_l-linear equivalence. Exact lift and scalar restriction
commute with homology, preserve finite support and preserve finite dimensions. -/
theorem fieldModel_finite (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :
    FiniteDimensional ℚ_[l] (FieldModel.{u} l E) := by
  sorry

attribute [instance] fieldModel_finite

/-- Lifting bounded finite-dimensional cohomology changes only its presentation.
Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison).
Proof: exact universe lift and restriction along down commute with homology. The
same finite support works, and the lifted bases are finite bases over the lifted field. -/
theorem fdLift_mem (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory) :
    DerivedCategory.pointFiniteDimensional (FieldModel.{u} l E)
      ((moduleLift.{u} l E).mapDerivedCategory.{0, u}.obj C.obj) := by
  sorry

/-- The canonical coefficient/carrier lift on finite-dimensional derived objects.
Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def fdLift (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l) :=
  (DerivedCategory.pointFiniteDimensional (FieldModel.{u} l E)).lift
    ((DerivedCategory.pointFiniteDimensional E.val).ι ⋙
      (moduleLift.{u} l E).mapDerivedCategory.{0, u})
    (fdLift_mem.{u} l E)

/-- The canonical lift is an equivalence on this full subcategory.
Source: rationality point comparison, finite-dimensional representatives
(blueprint: lem-zl-point-realization-coefficient-comparison).
Proof: every bounded finite-dimensional object has a bounded finite-dimensional
representative. Choose finite bases and descend its matrices to the original field.
This gives essential surjectivity; the same matrix description of derived maps gives
full faithfulness, with the original lifted maps. -/
theorem fdLift_equivalence (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) : (fdLift.{u} l E).IsEquivalence := by
  sorry

/-- Descent is the inverse of the specified lift, with its equivalence unit and counit.
Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def fdEquivalence (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l) :=
  letI := fdLift_equivalence.{u} l E
  (fdLift.{u} l E).asEquivalence

/-- The original condensed coefficient functions lifted coefficientwise.
Source: rationality point comparison, E_s^c identification
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def liftRingMap (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l) :
    Profinite.continuousMapRingSheaf E.val ⟶
      Profinite.continuousCoefficientRingSheaf (FieldModel.{u} l E) :=
  ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((ULift.ringEquiv : FieldModel.{u} l E ≃+* E.val).symm.toRingHom.compLeftContinuous
            S.unop continuous_uliftUp).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- Pull back this coefficient identification by the existing point inverse image.
Source: rationality point comparison, pulled-back coefficients
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def coefficientLift (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :=
  coefficientMap
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (liftRingMap l E)) T

/-- The specified coefficient lift is a ring-object isomorphism, and restriction is exact.
Source: rationality point comparison, coefficient-size identification
(blueprint: lem-zl-point-realization-coefficient-comparison).
Proof: apply down to continuous functions to invert up. Both maps preserve pointwise
one and multiplication, and pullback is strong monoidal. Restriction along a ring
isomorphism is an equivalence acting identically on the underlying additive sheaves. -/
theorem coefficientLift_properties (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :
    IsMonHom (coefficientLift T l E) ∧ IsIso (coefficientLift T l E) := by
  sorry

/-- Ring-linearity of the canonical lifted coefficient map.
Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance coefficientLiftMon (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) : IsMonHom (coefficientLift T l E) :=
  (coefficientLift_properties T l E).1

/-- Restriction along the canonical coefficient identification.
Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev coefficientRestriction (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :=
  Mod.comap (D := Sheaf (ProEt.topology T) Ab.{u + 1}) (coefficientLift T l E)

/-- The canonical coefficient restriction preserves both kernels and cokernels.
Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison).
Proof: the inverse down map gives the inverse restriction. Both change only scalar
actions, leaving underlying additive sheaves, kernels and cokernels unchanged. -/
theorem coefficientRestriction_exact (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :
    PreservesFiniteLimits (coefficientRestriction T l E) ∧
      PreservesFiniteColimits (coefficientRestriction T l E) := by
  sorry

/-- Kernel preservation for the coefficient identification.
Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance coefficientRestrictionLimits (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :
    PreservesFiniteLimits (coefficientRestriction T l E) :=
  (coefficientRestriction_exact T l E).1

/-- Cokernel preservation for the coefficient identification.
Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance coefficientRestrictionColimits (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :
    PreservesFiniteColimits (coefficientRestriction T l E) :=
  (coefficientRestriction_exact T l E).2

/-- The existing projection-normalized transport of completed integral coefficients.
Source: integral stratified-perfect characterization, detailed-category clause
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev moduleTransport (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :=
  fdCoefficientTransport l (FieldModel.{u} l E) T

/-- Retain additivity of the existing completed-ring coefficient transport.
Source: rationality point comparison, integral category identification
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance moduleTransportAdditive (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) : (moduleTransport T l E).Additive :=
  fdCoefficientTransportAdditive l (FieldModel.{u} l E) T

/-- Exactness of the recorded completed-ring transport at kernels.
Source: integral detailed coefficient comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance moduleTransportLimits (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :
    PreservesFiniteLimits (moduleTransport T l E) :=
  (integralDetailedCoefficientRestriction_exact T l (FieldModel.{u} l E)).1

/-- Exactness of the same recorded transport at cokernels.
Source: integral detailed coefficient comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance moduleTransportColimits (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) :
    PreservesFiniteColimits (moduleTransport T l E) :=
  (integralDetailedCoefficientRestriction_exact T l (FieldModel.{u} l E)).2

/-- Equality of the integral full subcategories, expressed through their existing
coefficient presentations. The rational comparison is fixed on objects and every pure
Hom tensor, rather than an arbitrary equivalence.
Source: rationality point comparison, domain-identification sentence
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
structure RawComparison (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) where
  integral : sfIntegralConstructibleCategory l (FieldModel.{u} l E) T ≌
    CondensedERealization.Integral l (FieldModel.{u} l E) T
  integral_identity : integral.functor ⋙
      ObjectProperty.ι
      (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l (FieldModel.{u} l E))) =
    (sfIntegralConstructible l (FieldModel.{u} l E) T).ι ⋙
      integralDetailedTransport T l (FieldModel.{u} l E)
  rational : sfRationalConstructibleCategory l (FieldModel.{u} l E) T ≌
    CondensedERealization.Rational l (FieldModel.{u} l E) T
  objects : ∀ K, rational.functor.obj K = ⟨integral.functor.obj K.obj⟩
  tensors : ∀ (K H : sfIntegralConstructibleCategory l (FieldModel.{u} l E) T)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l (FieldModel.{u} l E)))
    (f : K ⟶ H),
    HEq (rational.functor.map
      (fdRawTensor (Padic.coefficientExtensionUniformizer l (FieldModel.{u} l E)) a f))
      (fdRawTensor (pbcUniformizer l (FieldModel.{u} l E))
        ((pbcRationalCoefficientEquiv l (FieldModel.{u} l E)).symm
          (sfRationalCoefficientEquiv l (FieldModel.{u} l E) a)) (integral.functor.map f))

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : PadicAlgCl.FiniteIntermediateField l)

/-- The point as the specified affine spectrum.
Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev point := Spec (.of D.k)

/-- The same raw rational adic domain, with the coefficient field size made explicit.
Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev Adic := sfRationalConstructibleCategory l (FieldModel.{u} l E) (point D)

/-- The actual rational fibre followed by the inverse of the canonical size lift.
Source: rationality point comparison, Fib_s
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def fibre : Adic D l E ⥤ (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory :=
  pointRationalFibre D l hl (FieldModel.{u} l E) ⋙ (fdEquivalence.{u} l E).inverse

variable (r : CondensedERealization.At l (FieldModel.{u} l E) (point D))

/-- The actual normalized coefficient map from completed integral to continuous E.
Source: rationality point comparison, termwise calculation
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev integralToField := r.integralIso.hom ≫ r.inclusion

/-- The sectionwise encoding equivalence already specified by J_s.
Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev encoding := CondensedERealization.moduleEncoding l (FieldModel.{u} l E)
  (point D) r.sectionIso

/-- Additivity is the instance carried by the recorded realization datum.
Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance encodingAdditive : (encoding D l E r).functor.Additive := r.encodingAdditive

/-- The inverse encoding carries the recorded inverse additive structure.
Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance encodingInverseAdditive : (encoding D l E r).inverse.Additive :=
  r.encodingInverseAdditive

/-- Decode the same modules, then identify the lifted coefficient with E_s^c.
Source: rationality point comparison
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev decode := (encoding D l E r).inverse ⋙ coefficientRestriction (point D) l E

/-- Cache additivity of the prescribed inverse encoding and scalar restriction.
Source: rationality point comparison, encoding
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance decodeAdditive : (decode D l E r).Additive :=
  Functor.instAdditiveComp (encoding D l E r).inverse (coefficientRestriction (point D) l E)

/-- J_s on the actual raw rational domain. The inserted encoding and its inverse
are the existing coefficient equivalence, with its actual unit and counit.
Source: rationality point comparison, beta's left side
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def realization (c : RawComparison (point D) l E) :=
  c.rational.functor ⋙ r.realization.functor ⋙
    (boundedConstructible (CondensedERealization.Coefficient (FieldModel.{u} l E)
      (point D))).ι ⋙ (encoding D l E r).mapDerivedCategory.functor ⋙
    (encoding D l E r).mapDerivedCategory.inverse ⋙
    (coefficientRestriction (point D) l E).mapDerivedCategory

/-- The specified T^s_{E,Omega}, applied after the specified J_s.
Source: rationality point comparison, beta's left side
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def extendedRealization (c : RawComparison (point D) l E) :=
  realization D l E r c ⋙ derivedExtendScalarsToPadicAlgCl (point D) l E

/-- The existing ordinary tensor along the specified E-to-Omega coefficient map.
Source: rationality point comparison, termwise tensor
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev omegaExtension :
    Mod (Sheaf (ProEt.topology (point D)) Ab.{u + 1})
      (padicSubfieldRingObj (point D) l E) ⥤ PointCondensedModules D.k l :=
  Mod.extendScalars.{u + 1, u + 2}
    (C := Sheaf (ProEt.topology (point D)) Ab.{u + 1})
    (padicSubfieldRingObjToPadicAlgCl (point D) l E)

/-- Zero preservation of the specified ordinary coefficient extension, using its
existing additive structure directly rather than searching through tensor instances.
Source: rationality point comparison, termwise coefficient extension
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance (priority := 3000) omegaExtensionZero :
    (omegaExtension D l E).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (omegaExtension D l E)

/-- The ordinary tensor generators before the final coefficient extension.
Source: rationality point comparison, basis normalization
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev preOrdinary := moduleTransport (point D) l E ⋙ pbcExtend (integralToField D l E r) ⋙
  decode D l E r

/-- Cache additivity of the specified three-stage integral realization.
Source: rationality point comparison, ordinary tensor calculation
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance preOrdinaryAdditive : (preOrdinary D l E r).Additive :=
  Functor.instAdditiveComp (moduleTransport (point D) l E)
    (pbcExtend (integralToField D l E r) ⋙ decode D l E r)

/-- The actual ordinary tensor calculation on an integral module.
Source: rationality point comparison, termwise calculation
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev ordinary :
    scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D) ⥤
      PointCondensedModules D.k l :=
  preOrdinary D l E r ⋙ omegaExtension D l E

/-- Additivity of the termwise comparison functor, using the existing tensor functor.
Source: rationality point comparison, ordinary tensor calculation
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance ordinaryAdditive : (ordinary D l E r).Additive :=
  Functor.instAdditiveComp (preOrdinary D l E r) (omegaExtension D l E)

/-- Zero preservation of the actual composite tensor functor, supplied by its
specified additive structure. This avoids unfolding the coefficient tensor construction.
Source: rationality point comparison, termwise tensor complex
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance (priority := 3000) ordinaryZero : (ordinary D l E r).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
    (ordinary D l E r) (ordinaryAdditive D l E r)

/-- The termwise tensor complex, with no derived representative chosen.
Source: rationality point comparison, termwise calculation
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev ordinaryComplex
    (P : CochainComplex (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) ℤ) :=
  ((ordinary D l E r).mapHomologicalComplex (.up ℤ)).obj P

/-- The existing fourfold graded tensor colimit condition, with indices exposed so
instance inference uses preservation of each particular coproduct directly.
Source: rationality point comparison, termwise scalar extension
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance (priority := 3000) omegaGradedTensorFour :
    ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ
      (Mod (Sheaf (ProEt.topology (point D)) Ab.{u + 1})
        (padicSubfieldRingObj (point D) l E))),
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ :=
  fun _ _ _ _ _ _ ↦ inferInstance

/-- The existing threefold graded tensor colimit condition, using preservation of
individual coproducts after exposing the degree indices.
Source: rationality point comparison, termwise scalar extension
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance (priority := 3000) omegaGradedTensorLeft :
    ∀ (X₁ X₂ X₃ : GradedObject ℤ
      (Mod (Sheaf (ProEt.topology (point D)) Ab.{u + 1})
        (padicSubfieldRingObj (point D) l E))),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ :=
  fun _ _ _ _ _ ↦ inferInstance

/-- The existing threefold graded tensor colimit condition, using preservation of
individual coproducts after exposing the degree indices.
Source: rationality point comparison, termwise scalar extension
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance (priority := 3000) omegaGradedTensorRight :
    ∀ (X₁ X₂ X₃ : GradedObject ℤ
      (Mod (Sheaf (ProEt.topology (point D)) Ab.{u + 1})
        (padicSubfieldRingObj (point D) l E))),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ :=
  fun _ _ _ _ _ ↦ inferInstance

/-- Left tensoring on the source module sheaf category preserves ℤ-indexed colimits,
inherited from the closed module tensor; exposed for the derived scalar-extension counit.
Source: rationality point comparison, termwise scalar extension
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance (priority := 3000) omegaTensorLeft
    (X : Mod (Sheaf (ProEt.topology (point D)) Ab.{u + 1})
      (padicSubfieldRingObj (point D) l E)) :
    PreservesColimitsOfShape ℤ ((curriedTensor _).obj X) := by
  infer_instance

/-- Right tensoring on the source module sheaf category preserves ℤ-indexed colimits,
inherited from the closed module tensor; exposed for the derived scalar-extension counit.
Source: rationality point comparison, termwise scalar extension
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance (priority := 3000) omegaTensorRight
    (X : Mod (Sheaf (ProEt.topology (point D)) Ab.{u + 1})
      (padicSubfieldRingObj (point D) l E)) :
    PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj X) := by
  infer_instance

/-- The existing functorial flat resolutions of abelian sheaves on the point,
exposed for the derived scalar-extension counit.
Source: rationality point comparison, termwise scalar extension
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance (priority := 3000) omegaBaseFlatResolution :
    Abelian.HasFunctorialFlatResolution
      (Sheaf (ProEt.topology (point D)) Ab.{u + 1}) := by
  infer_instance

/-- The existing functorial flat resolutions of module sheaves on the point,
exposed for the derived scalar-extension counit.
Source: rationality point comparison, termwise scalar extension
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance (priority := 3000) omegaModuleFlatResolution :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (ProEt.topology (point D)) Ab.{u + 1})
        (padicSubfieldRingObj (point D) l E)) := by
  infer_instance

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The universal left-derived counit on actual cochain representatives.
Source: rationality point comparison, termwise calculation
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def extensionCounit
    (P : CochainComplex
      (Mod (Sheaf (ProEt.topology (point D)) Ab.{u + 1})
        (padicSubfieldRingObj (point D) l E)) ℤ) :
    (derivedExtendScalarsToPadicAlgCl (point D) l E).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((omegaExtension D l E).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  (derivedExtendScalarsToPadicAlgCl (point D) l E).map
      ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (omegaExtension D l E).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map
      (((omegaExtension D l E).mapHomotopyCategoryFactors
        (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((omegaExtension D l E).mapHomologicalComplex
        (.up ℤ)).obj P)

/-- The quotient-normalized identification of an integral object's ambient image.
Source: rationality point comparison, identification of the integral categories
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def integralObjectIso (c : RawComparison (point D) l E)
    (K : sfIntegralConstructibleCategory l (FieldModel.{u} l E) (point D)) :
    (c.integral.functor.obj K).obj ≅
      (integralDetailedTransport (point D) l (FieldModel.{u} l E)).obj K.obj :=
  eqToIso (congrArg (fun F ↦ F.obj K) c.integral_identity)

/-- The actual map from J_s of an integral representative to its ordinary tensor
complex. All factors are the specified realization comparison or universal counits.
Source: rationality point comparison, termwise normalization
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def modelCounit (c : RawComparison (point D) l E)
    (P : CochainComplex (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) ℤ)
    (hP : sfIntegralConstructible l (FieldModel.{u} l E) (point D) (DerivedCategory.Q.obj P)) :
    (extendedRealization D l E r c).obj
        ((sfRationalConstructibleLocalization l (FieldModel.{u} l E) (point D)).obj
          ⟨DerivedCategory.Q.obj P, hP⟩) ⟶
      DerivedCategory.Q.obj (ordinaryComplex D l E r P) :=
  (derivedExtendScalarsToPadicAlgCl (point D) l E).map
    ((coefficientRestriction (point D) l E).mapDerivedCategory.map
      ((encoding D l E r).mapDerivedCategory.inverse.map
        (((r.realization.functor ⋙
            (boundedConstructible (CondensedERealization.Coefficient (FieldModel.{u} l E)
              (point D))).ι ⋙ (encoding D l E r).mapDerivedCategory.functor).map
            (eqToHom (c.objects
              ((sfRationalConstructibleLocalization l (FieldModel.{u} l E) (point D)).obj
                ⟨DerivedCategory.Q.obj P, hP⟩)))) ≫
          r.scalarExtension.hom.app (c.integral.functor.obj ⟨DerivedCategory.Q.obj P, hP⟩) ≫
          (pbcDerivedExtend (integralToField D l E r)).map
            ((integralObjectIso D l E c ⟨DerivedCategory.Q.obj P, hP⟩).hom) ≫
          (pbcDerivedExtend (integralToField D l E r)).map
            ((moduleTransport (point D) l E).mapDerivedCategoryFactors.hom.app P) ≫
          pbcComplexCounit (integralToField D l E r)
            (((moduleTransport (point D) l E).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (encoding D l E r).inverse.mapDerivedCategoryFactors.hom.app
          (((pbcExtend (integralToField D l E r)).mapHomologicalComplex (.up ℤ)).obj
            (((moduleTransport (point D) l E).mapHomologicalComplex (.up ℤ)).obj P))) ≫
      (coefficientRestriction (point D) l E).mapDerivedCategoryFactors.hom.app
        (((encoding D l E r).inverse.mapHomologicalComplex (.up ℤ)).obj
          (((pbcExtend (integralToField D l E r)).mapHomologicalComplex (.up ℤ)).obj
            (((moduleTransport (point D) l E).mapHomologicalComplex (.up ℤ)).obj P)))) ≫
    extensionCounit D l E
      (((preOrdinary D l E r).mapHomologicalComplex (.up ℤ)).obj P)

/-- Termwise sections of the completed complex, then ordinary fraction-field tensor.
Source: rationality point comparison, point-equivalence normalization
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev sectionComplex
    (P : CochainComplex (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) ℤ) :=
  ((pointModuleRationalization l (FieldModel.{u} l E)).mapHomologicalComplex (.up ℤ)).obj
    (((pointCompletedSections D.k l (FieldModel.{u} l E)).mapHomologicalComplex (.up ℤ)).obj P)

/-- The source's specified fibre normalization followed by the exact termwise-section
comparisons. This pins the point-equivalence identification, including its unit.
Source: rationality point comparison, choice of the point representative
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def sectionComparison
    (P : CochainComplex (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) ℤ)
    (hP : sfIntegralConstructible l (FieldModel.{u} l E) (point D) (DerivedCategory.Q.obj P)) :=
  pointRationalNormalization D l hl (FieldModel.{u} l E)
      ((sfRationalConstructibleLocalization l (FieldModel.{u} l E) (point D)).obj
        ⟨DerivedCategory.Q.obj P, hP⟩) ≪≫
    (pointModuleDerivedRationalization l (FieldModel.{u} l E)).mapIso
      ((pointCompletedSections D.k l
        (FieldModel.{u} l E)).mapDerivedCategoryFactors.{u + 2, u + 2}.app P) ≪≫
    (pointModuleRationalization l (FieldModel.{u} l E)).mapDerivedCategoryFactors.{u + 2, u + 2}.app
      (((pointCompletedSections D.k l (FieldModel.{u} l E)).mapHomologicalComplex (.up ℤ)).obj P)

/-- The complex of vector spaces in the section universe, with both canonical lifts.
Source: rationality point comparison, point-equivalence normalization
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev frameLift (F : PointSupertraceFrame E.val) :=
  ((ModuleCat.uliftFunctor.{u + 1, u} (FieldModel.{u} l E)).mapHomologicalComplex (.up ℤ)).obj
    (((moduleLift.{u} l E).mapHomologicalComplex (.up ℤ)).obj F.complex)

/-- The existing coefficient module, used as the source finite-free basis object.
Source: rationality point comparison, integral lattice representative
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev integralUnit := SheafOfModules.unit
  (completedIntegralCoefficientSheafUnrestricted l (FieldModel.{u} l E) (point D))

/-- Finite biproducts in the existing abelian completed-module category.
Source: rationality point comparison, finite-free representatives
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
instance integralBiproducts : HasFiniteBiproducts
    (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- One in the reconstructed ring of sections of the specified U_s ring object.
Source: rationality point comparison, unit
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def unitSection (V : (point D).ProEtᵒᵖ) :=
  (1 : (InternalAbelianSheafModule.sectionRingSheaf
    (ProEt.topology (point D)) (padicAlgClRingObj (point D) l)).obj.obj V)

/-- A finite-free basis section of the actual completed coefficient sheaf.
Source: rationality point comparison, integral lattice representative
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def basisSection
    (P : CochainComplex (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) ℤ)
    (F : PointSupertraceFrame E.val)
    (b : ∀ i : ℤ, P.X i ≅ ⨁ (fun _ : Fin (F.rank i) ↦ integralUnit D l E))
    (i : ℤ) (a : Fin (F.rank i)) (V : (point D).ProEtᵒᵖ) :=
  ((biproduct.ι
    (C := scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D))
    (fun _ : Fin (F.rank i) ↦ integralUnit D l E) a ≫ (b i).inv).val.app V)
    (1 : (completedIntegralCoefficientSheafUnrestricted l (FieldModel.{u} l E)
      (point D)).obj.obj V)

/-- The corresponding actual sheaf tensor generator after J_s and T, before deriving.
Source: rationality point comparison, termwise identity matrix
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def tensorBasisSection
    (P : CochainComplex (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) ℤ)
    (F : PointSupertraceFrame E.val)
    (b : ∀ i : ℤ, P.X i ≅ ⨁ (fun _ : Fin (F.rank i) ↦ integralUnit D l E))
    (i : ℤ) (a : Fin (F.rank i)) (V : (point D).ProEtᵒᵖ) :=
  ((Mod.extendUnit.{u + 1, u + 2}
    (C := Sheaf (ProEt.topology (point D)) Ab.{u + 1})
    (padicSubfieldRingObjToPadicAlgCl (point D) l E)
    ((preOrdinary D l E r).obj (P.X i))).hom.hom.app V)
      (((encoding D l E r).counitIso.inv.app
        ((pbcExtend (integralToField D l E r)).obj
          ((moduleTransport (point D) l E).obj (P.X i)))).val.app V
        (pbcTensorSection (integralToField D l E r)
          ((moduleTransport (point D) l E).obj (P.X i)) V 1
          (basisSection D l E P F b i a V)))

/-- The canonical exact carrier lift from the field universe to the section universe.
Source: rationality point comparison, point-fibre normalization
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev largeLift :=
  (ModuleCat.uliftFunctor.{u + 1, u} (FieldModel.{u} l E)).mapDerivedCategory.{u, u + 2}

/-- The exact lift's specified comparison on cochain representatives.
Source: rationality point comparison, point-fibre normalization
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev largeLiftFactors :=
  (ModuleCat.uliftFunctor.{u + 1, u}
    (FieldModel.{u} l E)).mapDerivedCategoryFactors.{u, u + 2}

/-- The finite-free section comparison sends each lattice basis vector to its original
vector-space basis vector. This includes zero ranks and every cochain degree.
Source: rationality point comparison, point-equivalence normalization
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def SectionNormalized
    (P : CochainComplex (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) ℤ)
    (F : PointSupertraceFrame E.val)
    (b : ∀ i : ℤ, P.X i ≅ ⨁ (fun _ : Fin (F.rank i) ↦ integralUnit D l E))
    (v : sectionComplex D l E P ≅ frameLift l E F) : Prop :=
  ∀ (i : ℤ) (a : Fin (F.rank i)), (v.hom.f i).hom
    ((1 : FieldModel.{u} l E) ⊗ₜ[Padic.coefficientExtensionIntegers l (FieldModel.{u} l E)]
      basisSection D l E P F b i a (op (Scheme.ProEt.mk (𝟙 (point D))))) =
        ULift.up (ULift.up (F.basis i a))

variable [R : CondensedPointRealizationData D.k l E]
  [S : CondensedPointScalarData D.k l E] [M : CondensedPointMatrixData D.k l E]

/-- The specified right side rho(Fib_s N), in the ambient category via its full inclusion.
Source: rationality point comparison, beta's right side
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def matrixRealization := fibre D l hl E ⋙ R.rho ⋙
  (boundedConstructible (padicAlgClRingObj (point D) l)).ι

/-- The chain comparison is the identity on the displayed basis generators over U_s.
It therefore identifies differentials and chain maps with their original matrices.
Source: rationality point comparison, finite-matrix normalization
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def MatrixNormalized
    (P : CochainComplex (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) ℤ)
    (F : PointSupertraceFrame E.val)
    (b : ∀ i : ℤ, P.X i ≅ ⨁ (fun _ : Fin (F.rank i) ↦ integralUnit D l E))
    (t : ordinaryComplex D l E r P ≅ M.model F) : Prop :=
  ∀ (i : ℤ) (a : Fin (F.rank i)) (V : (point D).ProEtᵒᵖ),
    ((t.hom.f i).hom.hom.app V) (tensorBasisSection D l E r P F b i a V) =
      ((biproduct.ι (fun _ : Fin (F.rank i) ↦ 𝟙_ (PointCondensedModules D.k l)) a ≫
        (M.termIso F i).inv).hom.hom.app V)
          (unitSection D l V)

/-- The small point-equivalence identification obtained from a specified large one.
Source: rationality point comparison, unit of the point equivalence
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def smallFrameIso (N : Adic D l E) (F : PointSupertraceFrame E.val)
    (v : (pointRationalFibre D l hl (FieldModel.{u} l E)).obj N ≅
      (fdLift.{u} l E).obj ⟨DerivedCategory.Q.{0}.obj F.complex, M.frame_mem F⟩) :=
  (fdEquivalence.{u} l E).inverse.mapIso v ≪≫
    (fdEquivalence.{u} l E).unitIso.symm.app
      ⟨DerivedCategory.Q.{0}.obj F.complex, M.frame_mem F⟩

/-- Exact finite-matrix normalization of beta. The left comparison is the actual
universal derived-extension counit. The right comparison is pinned by actual sections
and the existing point-fibre normalization. Thus neither arrow is arbitrary.
Source: rationality point comparison, all normalization clauses
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def Normalized (c : RawComparison (point D) l E)
    (β : extendedRealization D l E r c ≅ matrixRealization D l hl E) : Prop :=
  ∀ (P : CochainComplex (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) ℤ)
    (hP : sfIntegralConstructible l (FieldModel.{u} l E) (point D) (DerivedCategory.Q.obj P))
    (F : PointSupertraceFrame E.val)
    (b : ∀ i : ℤ, P.X i ≅ ⨁ (fun _ : Fin (F.rank i) ↦ integralUnit D l E))
    (v : sectionComplex D l E P ≅ frameLift l E F),
    SectionNormalized D l E P F b v →
    ∀ (w : (pointRationalFibre D l hl (FieldModel.{u} l E)).obj
        ((sfRationalConstructibleLocalization l (FieldModel.{u} l E) (point D)).obj
          ⟨DerivedCategory.Q.obj P, hP⟩) ≅
        (fdLift.{u} l E).obj ⟨DerivedCategory.Q.{0}.obj F.complex, M.frame_mem F⟩),
    (largeLift l E).map w.hom.hom ≫
      (largeLift l E).map
        ((moduleLift.{u} l E).mapDerivedCategoryFactors.{0, u}.hom.app F.complex) ≫
        (largeLiftFactors l E).hom.app
          (((moduleLift.{u} l E).mapHomologicalComplex (.up ℤ)).obj F.complex) =
      (sectionComparison D l hl E P hP).hom ≫ DerivedCategory.Q.map v.hom →
    ∃ t : ordinaryComplex D l E r P ≅ M.model F,
      MatrixNormalized D l E r P F b t ∧
      β.hom.app ((sfRationalConstructibleLocalization l (FieldModel.{u} l E) (point D)).obj
          ⟨DerivedCategory.Q.obj P, hP⟩) ≫
        (R.rho.map (smallFrameIso D l hl E
          ((sfRationalConstructibleLocalization l (FieldModel.{u} l E) (point D)).obj
            ⟨DerivedCategory.Q.obj P, hP⟩) F w).hom).hom ≫
          (M.modelIso F).hom =
        modelCounit D l E r c P hP ≫ DerivedCategory.Q.map t.hom

/-- The canonical raw rational shift of a cochain representative.
Source: rationality point comparison, shifts
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def rawRepresentativeShift
    (P : CochainComplex (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) ℤ)
    (hP : sfIntegralConstructible l (FieldModel.{u} l E) (point D) (DerivedCategory.Q.obj P))
    (n : ℤ)
    (hPn : sfIntegralConstructible l (FieldModel.{u} l E) (point D)
      (DerivedCategory.Q.obj (P⟦n⟧))) :
    (sfRationalConstructibleLocalization l (FieldModel.{u} l E) (point D)).obj
        ⟨DerivedCategory.Q.obj (P⟦n⟧), hPn⟩ ⟶
      ((sfRationalConstructibleLocalization l (FieldModel.{u} l E) (point D)).obj
        ⟨DerivedCategory.Q.obj P, hP⟩)⟦n⟧ :=
  (sfRationalConstructibleLocalization l (FieldModel.{u} l E) (point D)).map
      (ObjectProperty.homMk
        (X := ⟨DerivedCategory.Q.obj (P⟦n⟧), hPn⟩)
        (Y := (shiftFunctor
          (sfIntegralConstructibleCategory l (FieldModel.{u} l E) (point D)) n).obj
            ⟨DerivedCategory.Q.obj P, hP⟩)
        ((DerivedCategory.Q.commShiftIso n).hom.app P ≫
          (((sfIntegralConstructible l (FieldModel.{u} l E)
            (point D)).ι.commShiftIso n).inv.app ⟨DerivedCategory.Q.obj P, hP⟩))) ≫
    ((sfRationalConstructibleLocalization l (FieldModel.{u} l E) (point D)).commShiftIso
      n).hom.app ⟨DerivedCategory.Q.obj P, hP⟩

/-- Termwise tensor commutes with shifts by the canonical complex and quotient maps.
Source: rationality point comparison, shifts
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def ordinaryShiftComparison
    (P : CochainComplex (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) ℤ)
    (n : ℤ) :
    DerivedCategory.Q.obj (ordinaryComplex D l E r (P⟦n⟧)) ⟶
      (DerivedCategory.Q.obj (ordinaryComplex D l E r P))⟦n⟧ :=
  DerivedCategory.Q.map
      ((((ordinary D l E r).mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app P) ≫
    (DerivedCategory.Q.commShiftIso n).hom.app (ordinaryComplex D l E r P)

/-- The source's canonical coefficient/carrier lift into the section universe.
Source: rationality point comparison, fibre shifts
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
abbrev liftedSource := (DerivedCategory.pointFiniteDimensional E.val).ι ⋙
  (moduleLift.{u} l E).mapDerivedCategory.{0, u} ⋙
  (largeLift l E)

/-- The specified fibre normalization, including the size-equivalence counit.
Source: rationality point comparison, fibre shifts
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def liftedSectionComparison
    (P : CochainComplex (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) ℤ)
    (hP : sfIntegralConstructible l (FieldModel.{u} l E) (point D) (DerivedCategory.Q.obj P)) :=
  (largeLift l E).mapIso
      ((DerivedCategory.pointFiniteDimensional (FieldModel.{u} l E)).ι.mapIso
        ((fdEquivalence.{u} l E).counitIso.app
          ((pointRationalFibre D l hl (FieldModel.{u} l E)).obj
            ((sfRationalConstructibleLocalization l (FieldModel.{u} l E) (point D)).obj
              ⟨DerivedCategory.Q.obj P, hP⟩)))) ≪≫
    sectionComparison D l hl E P hP

/-- The fibre shift is fixed by the actual sections and termwise complex shifts.
Source: rationality point comparison, shifts
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def FibreShiftNormalized (f : (fibre D l hl E).CommShift ℤ) : Prop :=
  letI := f
  ∀ (P : CochainComplex (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) ℤ)
    (hP : sfIntegralConstructible l (FieldModel.{u} l E) (point D) (DerivedCategory.Q.obj P))
    (n : ℤ)
    (hPn : sfIntegralConstructible l (FieldModel.{u} l E) (point D)
      (DerivedCategory.Q.obj (P⟦n⟧))),
    (liftedSource l E).map ((fibre D l hl E).map
        (rawRepresentativeShift D l E P hP n hPn) ≫
      ((fibre D l hl E).commShiftIso n).hom.app
        ((sfRationalConstructibleLocalization l (FieldModel.{u} l E) (point D)).obj
          ⟨DerivedCategory.Q.obj P, hP⟩)) ≫
      ((liftedSource l E).commShiftIso n).hom.app
        ((fibre D l hl E).obj
          ((sfRationalConstructibleLocalization l (FieldModel.{u} l E) (point D)).obj
            ⟨DerivedCategory.Q.obj P, hP⟩)) ≫
      (shiftFunctor _ n).map (liftedSectionComparison D l hl E P hP).hom =
    (liftedSectionComparison D l hl E (P⟦n⟧) hPn).hom ≫
      DerivedCategory.Q.map
        (((((pointCompletedSections D.k l (FieldModel.{u} l E)) ⋙
          pointModuleRationalization l (FieldModel.{u} l E)).mapHomologicalComplex
            (.up ℤ)).commShiftIso n).hom.app P) ≫
      (DerivedCategory.Q.commShiftIso n).hom.app (sectionComplex D l E P)

/-- Shift compatibility, with the left shift fixed on actual tensor representatives.
The right shift is the composite of the normalized fibre shift and rho's specified shift.
Source: rationality point comparison, shifts
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def ShiftCompatible (c : RawComparison (point D) l E)
    (β : extendedRealization D l E r c ≅ matrixRealization D l hl E)
    (a : (extendedRealization D l E r c).CommShift ℤ)
    (f : (fibre D l hl E).CommShift ℤ) : Prop :=
  letI := a
  letI := f
  letI : (matrixRealization D l hl E).CommShift ℤ :=
    inferInstanceAs (((fibre D l hl E) ⋙ R.rho ⋙
      (boundedConstructible (padicAlgClRingObj (point D) l)).ι).CommShift ℤ)
  FibreShiftNormalized D l hl E f ∧ NatTrans.CommShift β.hom ℤ ∧
    ∀ (P : CochainComplex (scalarReductionSource.{u, u} l (FieldModel.{u} l E) (point D)) ℤ)
      (hP : sfIntegralConstructible l (FieldModel.{u} l E) (point D) (DerivedCategory.Q.obj P))
      (n : ℤ)
      (hPn : sfIntegralConstructible l (FieldModel.{u} l E) (point D)
        (DerivedCategory.Q.obj (P⟦n⟧))),
      (extendedRealization D l E r c).map (rawRepresentativeShift D l E P hP n hPn) ≫
        ((extendedRealization D l E r c).commShiftIso n).hom.app
          ((sfRationalConstructibleLocalization l (FieldModel.{u} l E) (point D)).obj
            ⟨DerivedCategory.Q.obj P, hP⟩) ≫
        (shiftFunctor _ n).map (modelCounit D l E r c P hP) =
      modelCounit D l E r c (P⟦n⟧) hPn ≫ ordinaryShiftComparison D l E r P n

/-- The finite-matrix realization identifies E[0] with U_s by multiplication, with
one mapping to one. This pins its monoidal unit to the same matrix model.
Source: rationality point comparison, coefficient-unit normalization
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def MatrixUnitNormalized : Prop :=
  ∀ (F : PointSupertraceFrame E.val)
    (e : F.complex ≅ (CochainComplex.singleFunctor (ModuleCat.{0} E.val) 0).obj
      (ModuleCat.of E.val E.val)),
    ∃ t : M.model F ≅ (CochainComplex.singleFunctor (PointCondensedModules D.k l) 0).obj
        (𝟙_ (PointCondensedModules D.k l)),
      (∀ (a : Fin (F.rank 0)) (V : (point D).ProEtᵒᵖ),
        ((((biproduct.ι (fun _ : Fin (F.rank 0) ↦ 𝟙_ (PointCondensedModules D.k l)) a ≫
          (M.termIso F 0).inv ≫ t.hom.f 0).hom.hom.app V)
            (unitSection D l V))) =
          (((S.scalar ((e.hom.f 0).hom (F.basis 0 a)).val).hom.hom.app V)
            (unitSection D l V))) ∧
      HEq ((M.modelIso F).hom ≫ DerivedCategory.Q.map t.hom ≫
        (DerivedCategory.singleFunctorIsoCompQ (PointCondensedModules D.k l) 0).inv.app
          (𝟙_ (PointCondensedModules D.k l)) ≫
        (DerivedCategory.singleFunctorObjUnitIso (PointCondensedModules D.k l)).hom)
        ((R.rho.map (ObjectProperty.homMk
          (X := ⟨DerivedCategory.Q.{0}.obj F.complex, M.frame_mem F⟩)
          (Y := 𝟙_ (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory)
          (DerivedCategory.Q.{0}.map e.hom ≫
          (DerivedCategory.singleFunctorIsoCompQ.{0} (ModuleCat.{0} E.val) 0).inv.app
            (ModuleCat.of E.val E.val) ≫
          (DerivedCategory.singleFunctorObjUnitIso.{0} (ModuleCat.{0} E.val)).hom)) ≫
            (Functor.Monoidal.εIso R.rho).inv).hom)

omit R S M in
/-- All comparison clauses, using a single shared choice of the dependency's matrix
realization. No arbitrary natural isomorphism is accepted: the normalized one is unique.
Source: rationality point comparison, whole statement
(blueprint: lem-zl-point-realization-coefficient-comparison). -/
def ComparisonStatement (A : CondensedPointSupertraceData D.k l E) : Prop :=
  letI := A.realization
  letI := A.scalars
  letI := A.matrices
  MatrixUnitNormalized D l E ∧
    ∃ c : RawComparison (point D) l E,
      ∃! β : extendedRealization D l E r c ≅ matrixRealization D l hl E,
        Normalized D l hl E r c β ∧
          ∃ (a : (extendedRealization D l E r c).CommShift ℤ)
            (f : (fibre D l hl E).CommShift ℤ),
            ShiftCompatible D l hl E r c β a f

omit R S M in
/-- Point realization commutes with the specified condensed coefficient extension,
with the same completed integral category, raw rationalization, matrices, shifts and unit.

Source: main-20261015, sec-zeta-weil/sk-thm-rationality, first sentence of the proof
(blueprint: lem-zl-point-realization-coefficient-comparison).

Proof:
1. The point is noetherian of dimension zero, and l is invertible since l differs from
   D.p. Apply integralStratifiedPerfectDetailed with the quotient-normalized completed
   coefficient comparison. The integral categories have identical objects and maps in
   these coordinates. Extend their Hom maps on pure tensors to obtain RawComparison.
2. Apply the recorded point-fibre equivalence. For an adic N choose a bounded finite-
   dimensional representative C of its fibre, with finite bases. Choose m clearing all
   differential denominators. Rescale the degree-i basis by varpi^(-mi). The resulting
   O_E spans form a bounded finite-free subcomplex P with P tensor E = C; take P=0
   for C=0. Its completed constant sheaf complex belongs to the integral category by
   the stratified-perfect characterization.
3. Sections of the completed ring at the point are O_E, by continuous-coefficient
   immersion restriction. Thus point sections of this representative, followed by
   tensor E, give C with the original basis identification. The point equivalence's
   full faithfulness gives the unique representative isomorphism with this fibre.
4. The specified J is scalar extension along integralIso followed by inclusion. On
   these bounded finite-free complexes its universal counit is invertible. Coefficient
   restriction is the up/down identification. The final T is the recorded exact
   extension to Omega, computed termwise. Each basis generator 1 tensor e maps to the
   same generator over U_s. The resulting differential matrices are exactly those of C
   through E into Omega. The degree-i diagonal varpi^(-mi) removes the rescaled basis.
   These are precisely modelCounit and MatrixNormalized, with SectionNormalized fixing
   the point-equivalence unit. Combine them with that unit to obtain beta_N.
5. Lift an arbitrary derived map between bounded projective representatives to a
   chain map by derived_map_lift. Clear its finitely many denominators. Faithfulness
   of the point fibre identifies its integral representative with this chain map;
   linearity cancels the clearing scalar. Both realizations apply the same matrices,
   so beta is natural on derived maps. The identity with two sets of choices proves
   independence of bases, lattices and quasi-isomorphic representatives.
6. Apply this independence to shifted choices C[n],P[n]. Both differentials have the
   same Koszul signs, giving ShiftCompatible. For E_s take P=O_E[0], C=E[0] and the
   identity point representative. The tensor multiplication maps send 1 to 1; this
   is the canonical unit identification, fixed also by MatrixUnitNormalized.
7. Every adic object has the representative from step 2. The normalization equation
   on it fixes beta_N, proving uniqueness. The canonical coefficient/carrier lifts
   preserve all these equations and do not impose a universe equality.
-/
theorem point_realization_coefficient_comparison :
    ∃ A : CondensedPointSupertraceData D.k l E, ComparisonStatement D l hl E r A := by
  sorry


end WeilConjectures.PointRealizationComparison
