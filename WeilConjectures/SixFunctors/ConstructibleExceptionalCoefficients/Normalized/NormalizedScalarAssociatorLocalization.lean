/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedScalarAssociatorLocalizationTransport

/-! # Localization of a normalized completed scalar associator

## References

* Bhatt–Scholze, *The pro-étale topology for schemes*, Definition 3.4.10 and Lemma 3.4.12
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- A finite-Tor scalar associator with the prescribed ordinary realization localizes
to the intrinsic rational scalar associator. -/
theorem normalized_scalar_associator_localization
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
    HEq ((sfRationalScalarComp l E.carrier L.carrier i T 0
      (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
        ((rationalization.{u, v} l Ω E T).obj K))
      ((rationalization.{u, v} l Ω M T).map (α.iso.hom.app K)) := by
  have hc := (sfRationalScalarComp_existsUnique l E.carrier L.carrier i T 0
      (Fact.out : l.Prime).ne_zero M.carrier j).exists.choose_spec
    ((rationalization.{u, v} l Ω E T).obj K)
  have ht := normalized_scalar_associator_localization_transport l Ω E L M i j T A B D
    hA hB hD nA nB nD α K
  exact hc.trans ht.symm

end WeilConjectures.ConstructibleExceptionalCoefficients
