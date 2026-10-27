/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData
public import Sheaf.Paper.SfScalarExtensionComposition

/-! # Localization transport for a normalized scalar associator -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The localization of a supplied normalized associator is the localization of the
canonical integral associator.  This is the transport step in the proof of
`lem-sf-normalized-scalar-associator-localization`: identify the supplied functors with
the completed scalar extensions using their realization equalities, use the three
inverse-realization normalizations and the balanced tensor normalization, then apply
the raw localization functor.  The argument is forward transport and does not use
faithfulness of localization.  It also covers identity embeddings and repeated fields.
(blueprint: lem-sf-normalized-scalar-associator-localization-transport).
-/
theorem normalized_scalar_associator_localization_transport
    (E L M : FieldStage.{max u v} l)
    (i : E.carrier →ₐ[Padic l] L.carrier) (j : L.carrier →ₐ[Padic l] M.carrier)
    (T : Scheme.{max u v})
    (A : Scalar.{u, v} l Ω (s := .integral E) (t := .integral L)
      (PurCompactSupport.completedChange l E.carrier L.carrier i) T)
    (B : Scalar.{u, v} l Ω (s := .integral L) (t := .integral M)
      (PurCompactSupport.completedChange l L.carrier M.carrier j) T)
    (D : Scalar.{u, v} l Ω (s := .integral E) (t := .integral M)
      (PurCompactSupport.completedChange l E.carrier M.carrier (j.comp i)) T)
    (hA : A.functor ⋙ (finiteTorConstructibleIntegral l L.carrier T).ι =
      (finiteTorConstructibleIntegral l E.carrier T).ι ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i T)
    (hB : B.functor ⋙ (finiteTorConstructibleIntegral l M.carrier T).ι =
      (finiteTorConstructibleIntegral l L.carrier T).ι ⋙
        integralScalarExtensionOfUniverses l L.carrier M.carrier j T)
    (hD : D.functor ⋙ (finiteTorConstructibleIntegral l M.carrier T).ι =
      (finiteTorConstructibleIntegral l E.carrier T).ι ⋙
        integralScalarExtensionOfUniverses l E.carrier M.carrier (j.comp i) T)
    (nA : ∀ K, HEq (A.realization.inv.app K)
      ((completedScalarComparison l E.carrier L.carrier i T).app K.obj))
    (nB : ∀ K, HEq (B.realization.inv.app K)
      ((completedScalarComparison l L.carrier M.carrier j T).app K.obj))
    (nD : ∀ K, HEq (D.realization.inv.app K)
      ((completedScalarComparison l E.carrier M.carrier (j.comp i) T).app K.obj))
    (α : ScalarComposition.{u, v} l Ω
      (PurCompactSupport.completedMap_composition l E.carrier L.carrier i M.carrier j)
      T A B D)
    (K : C.{u, v} l Ω T (.integral E)) :
    HEq ((rationalization.{u, v} l Ω M T).map (α.iso.hom.app K))
      ((sfRationalConstructibleLocalization l M.carrier T).map
        ((sfIntegralScalarComp l E.carrier L.carrier i T 0
          (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
          ⟨K.obj, K.property.1⟩)) := by
  sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
