/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProductComparisons.NativeSixFunctorKunnethMaps
public import WeilConjectures.SmoothPurity.FiniteRingTrace.FiniteRingTraceDualizingComplex
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfRfShriekPreservation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompCompositionWitnesses
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.CharP.CharAndCard

/-! # Auxiliary comparisons between constructible exceptional presentations

These helpers instantiate the recorded general product maps. They do not define
exceptional admissibility or replace its recorded functor. `recordedExceptional` is
literally `traceFormulaCtfUpperShriek`; `recordedExceptionalComparison` identifies
the supplied adjunction at an auxiliary compactification with that functor by
right-adjoint uniqueness.
The comparison uses the normalized compact-support comparison and so preserves counits.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-coefficients-constructible/sec-n-brown/sk-thm-existence/def-trf-admissibility.md
(blueprint: thm-trf-kunneth-verdier).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.ProductComparisons
open scoped CategoryTheory.Obj

namespace WeilConjectures.FiniteRingTrace

-- Match the structure-map instances used by the recorded admissibility interface.
local instance {k : Type u} [Field k] (X : SepFinType k) :
    LocallyOfFiniteType (X.obj.left ↘ Spec (.of k)) := by
  change LocallyOfFiniteType X.obj.hom
  infer_instance

local instance {k : Type u} [Field k] (X : SepFinType k) :
    QuasiCompact (X.obj.left ↘ Spec (.of k)) := by
  change QuasiCompact X.obj.hom
  infer_instance

local instance {k : Type u} [Field k] (X : SepFinType k) :
    IsSeparated (X.obj.left ↘ Spec (.of k)) := by
  change IsSeparated X.obj.hom
  infer_instance

-- A morphism between separated finite-type k-schemes inherits these properties
-- from its composite with the target structure map. Keep the instances local so
-- this module does not depend on instances incidentally imported elsewhere.
local instance {k : Type u} [Field k] {X Y : SepFinType k} (f : X ⟶ Y) :
    IsSeparated f.hom.left := by
  have : IsSeparated (f.hom.left ≫ Y.obj.hom) := by
    rw [f.hom.w]
    infer_instance
  exact IsSeparated.of_comp f.hom.left Y.obj.hom

local instance {k : Type u} [Field k] {X Y : SepFinType k} (f : X ⟶ Y) :
    LocallyOfFiniteType f.hom.left := by
  have : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) := by
    rw [f.hom.w]
    infer_instance
  exact locallyOfFiniteType_of_comp f.hom.left Y.obj.hom

local instance {k : Type u} [Field k] {X Y : SepFinType k} (f : X ⟶ Y) :
    QuasiCompact f.hom.left := by
  have : QuasiCompact (f.hom.left ≫ Y.obj.hom) := by
    rw [f.hom.w]
    infer_instance
  exact QuasiCompact.of_comp f.hom.left Y.obj.hom

/-- Bundle the existing discrete coefficient ring, retaining its actual multiplication.
Source: def-trf-admissibility, arbitrary finite ring convention
(blueprint: thm-trf-kunneth-verdier). -/
abbrev scalarRing (A : Type) [CommRing A] [Finite A] : ScalarSixRing.{u} :=
  CommMon.mk (coefficient A)

/-- The existing coefficient-admissibility witness for the discrete finite primary coefficient.
Source: def-trf-admissibility, coefficient hypothesis (blueprint: thm-trf-kunneth-verdier). -/
abbrev coefficientAdmissible (A : Type) [CommRing A] [Finite A]
    (ell : ℕ) [Fact ell.Prime]
    (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0) :
    IsLocalizingAdmissibleCoefficient ell (coefficient A :
      Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  let : IsTopologicalRing A := DiscreteTopology.topologicalRing
  exact Or.inl ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨hA.choose, hA.choose_spec.2⟩, ⟨Iso.refl _⟩⟩

/-- The unique comparison with another constructible presentation of the same
exceptional adjoint. Its left comparison is the normalized compactification comparison
followed by the given exact equality with compact support. Right-adjoint uniqueness
fixes the comparison, including the counit; no independent isomorphism is selected.
Source: def-trf-admissibility, specified constructible adjoint convention
(blueprint: thm-trf-kunneth-verdier). -/
def exceptionalComparison (A : Type) [CommRing A] [Finite A]
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hne : ringChar D.k ≠ ell)
    (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
    {X Y : SepFinType D.k} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (T : CurrentConstructibleExceptionalData (coefficient A) f.hom) :
    ProductComparisons.exceptional (scalarRing A) (exceptionalAt A D ell hne hA f c) ≅
      T.right := by
  let J := exceptionalAt A D ell hne hA f c
  let H := (relativeDatum D ell hne).coherent (scalarRing A) (coefficientAdmissible A ell hA)
  let eAmbient : ProductComparisons.lower (scalarRing A) J ⋙
      (constantModelBoundedConstructible (coefficient A) Y.obj.left ⊓
        DerivedCategory.finiteTorAmplitude _).ι ≅
      T.lower ⋙ (constantModelBoundedConstructible (coefficient A) Y.obj.left ⊓
        DerivedCategory.finiteTorAmplitude _).ι :=
    Functor.isoWhiskerLeft (ObjectProperty.ιOfLE J.source_mem)
      (H.comparison f c (compactificationOverField f.hom)) ≪≫ eqToIso T.lower_eq.symm
  let e : ProductComparisons.lower (scalarRing A) J ≅ T.lower :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (eAmbient.app K)) (by
      intro K L a
      apply ObjectProperty.hom_ext
      exact eAmbient.hom.naturality a)
  exact (ProductComparisons.adjunction (scalarRing A) J).rightAdjointUniq
    (T.adjunction.ofNatIsoLeft e.symm)

end WeilConjectures.FiniteRingTrace
