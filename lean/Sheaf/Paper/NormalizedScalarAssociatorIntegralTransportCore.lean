/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData
public import Sheaf.Paper.SfScalarExtensionComposition

/-! # Ambient core of integral transport for a normalized scalar associator -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Ambient equality underlying integral normalized scalar transport.
Source: Definition 3.4.10 and Lemma 3.4.12, pp. 22-23; Proposition 3.5.1, p. 24.
(blueprint: lem-sf-normalized-scalar-associator-localization-transport-integral-core).
Proof: after applying the faithful finite-Tor integral inclusion, expand the normalized
associator equation using the three realization equalities and inverse-realization
normalizations; identify the resulting ordinary balanced tensor map with the unique
normalized completed integral associator.
-/
theorem normalized_scalar_associator_integral_transport_core
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
    (K : C.{u, v} l Ω T (.integral E))
    (hsource :
      (⟨(B.functor.obj (A.functor.obj K)).obj,
        (B.functor.obj (A.functor.obj K)).property.1⟩ :
        sfIntegralConstructibleCategory l M.carrier T) =
        (sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
          E.carrier L.carrier i T ⋙
          sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
            L.carrier M.carrier j T).obj
          ((⟨K.obj, K.property.1⟩ : sfIntegralConstructibleCategory l E.carrier T)))
    (htarget :
      (⟨(D.functor.obj K).obj, (D.functor.obj K).property.1⟩ :
        sfIntegralConstructibleCategory l M.carrier T) =
        (sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
          E.carrier M.carrier (j.comp i) T).obj
          ((⟨K.obj, K.property.1⟩ : sfIntegralConstructibleCategory l E.carrier T))) :
    (sfIntegralConstructible l M.carrier T).ι.map
      (eqToHom hsource.symm ≫
        (PurCompactSupport.finiteTorIntegralInclusion l M.carrier T).map
          (α.iso.hom.app K) ≫
        eqToHom htarget) =
      (sfIntegralConstructible l M.carrier T).ι.map
        ((sfIntegralScalarComp l E.carrier L.carrier i T 0
          (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
          (⟨K.obj, K.property.1⟩ : sfIntegralConstructibleCategory l E.carrier T)) := by
  sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
