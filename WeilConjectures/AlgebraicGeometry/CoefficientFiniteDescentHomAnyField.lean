/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentHom
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.CategoryTheory.Sites.TransfinitePlusSheaf
public import
  WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite descent of coefficient morphisms over any allowed base field

This statement includes characteristic zero and uses the canonical maps, coefficient rings,
ordinary derived categories, and bounded constructible objects of the positive-characteristic
theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

/-- The natural derived scalar adjunctions, uniformly bounded-below coefficient
complex colimit, and finite descent of every shifted morphism, over any field
whose characteristic differs from the coefficient prime. -/
theorem coefficient_finite_descent_hom_of_char_ne
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (_hchar : ringChar k ≠ ℓ)
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (C D : BoundedConstructible (padicSubfieldRingObj X ℓ E)) (r : ℤ) :
    (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      Function.Bijective (finiteCoefficientDerivedHomEquiv X ℓ h C.obj
        (((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧))) ∧
    Function.Bijective (finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj
      (((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj)⟦r⟧)) ∧
    (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (j : F ≤ G)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
      finiteCoefficientDerivedHomEquiv X ℓ (h.trans j) C.obj _
          (coefficientDescentHomTransition X ℓ h j C.obj D.obj r f) =
        finiteCoefficientDerivedHomEquiv X ℓ h C.obj _ f ≫
          coefficientDescentRestrictionTransition X ℓ h j D.obj r) ∧
    (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
      finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj _
          (coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r f) =
        finiteCoefficientDerivedHomEquiv X ℓ h C.obj _ f ≫
          coefficientDescentRestrictionToAlgCl X ℓ h D.obj r) ∧
    (∀ (K : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicSubfieldRingObj X ℓ E)) ℤ)
      (_e : DerivedCategory.Q.obj K ≅ D.obj) (a b : ℤ)
      (_hK : ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)),
      IsFiltered (AsSmall.{u + 1} (Under E)) ∧
        Nonempty (IsColimit (coefficientComplexCocone X ℓ K (coefficientDescentFields ℓ E)
          (fun i ↦ leOfHom (ULift.down i).hom) (fun i ↦ leOfHom (ULift.down i).hom))) ∧
        ∀ (i : AsSmall.{u + 1} (Under E)) (n : ℤ), n < a →
          IsZero (((coefficientComplexDiagram X ℓ K (coefficientDescentFields ℓ E)
            (fun j ↦ leOfHom (ULift.down j).hom)
            (fun j ↦ leOfHom (ULift.down j).hom)).obj i).X n)) ∧
    (∀ f : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C.obj ⟶
        ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj)⟦r⟧,
      ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
        (g : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
          ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
        coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r g = f) ∧
    (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (j : E ≤ G)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧)
      (g : (derivedExtendScalarsSubfield X ℓ j).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ j).obj D.obj)⟦r⟧),
      coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r f =
        coefficientDescentHomToAlgCl X ℓ j C.obj D.obj r g →
      ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (hF : F ≤ H) (hG : G ≤ H),
        coefficientDescentHomTransition X ℓ h hF C.obj D.obj r f =
          coefficientDescentHomTransition X ℓ j hG C.obj D.obj r g) := by
  sorry

end AlgebraicGeometry.ProEtale
