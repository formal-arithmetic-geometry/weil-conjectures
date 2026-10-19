/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralScalarExtension

import Sheaf.Paper.IntegralScalarExtensionConstructible
import Sheaf.Paper.CompletedCoefficientPresentationTransport
import Sheaf.Paper.SfIntegralConstructibleTriangulated

/-!
# Integral scalar extension preserves intrinsic bounded constructibility

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace WeilConjectures

/-- Completed integral scalar extension preserves the intrinsic bounded constructible
predicate over arbitrary schemes.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: the canonical coefficient equivalence supplies a counit isomorphism from a
round-trip object to K. Its two completeness comparisons identify intrinsic completeness
with the existing unrestricted completeness predicate. Extract its auxiliary finite-field
presentation; the finite-reduction functors and uniform interval agree definitionally.
Apply the already stated integralScalarExtension_constructible to this presentation.
Use the target coefficient equivalence and its completeness comparisons in reverse,
then transport along the two counit isomorphisms. Only the completeness comparison is
used: its bounded-constructibility comparison, with geometric hypotheses, is unnecessary.
Thus no Noetherian hypothesis or restriction on the characteristic of Y is introduced.
The legacy preservation theorem remains a proof dependency; it is not proved here.
-/
theorem sfIntegralScalarExtension_constructible
    (p l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (Y : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    sfIntegralConstructible l L Y
      ((integralScalarExtension l E L ι Y).obj K) := by
  have := sfIntegralConstructible_isClosedUnderIsomorphisms l E Y
  have := sfIntegralConstructible_isClosedUnderIsomorphisms l L Y
  let eE := purCoefficientModel l E Y
  let K₀ := eE.functor.obj (eE.inverse.obj K)
  have hK₀ : sfIntegralConstructible l E Y K₀ :=
    ObjectProperty.prop_of_iso _ (eE.counitIso.app K).symm hK
  have hcomplete : IsDerivedCompleteUnrestricted l E Y K₀ :=
    (purCoefficientModel_predicates l E Y (eE.inverse.obj K)).1.mp
      ((purCoefficientModel_predicates l E Y (eE.inverse.obj K)).2.mpr hK₀.1)
  obtain ⟨D, hDl, hcomplete⟩ := hcomplete
  have hKold : boundedConstructibleDerivedCompleteIntegral D l hDl E Y K₀ :=
    ⟨hcomplete, hK₀.2⟩
  have hN := integralScalarExtension_constructible D l hDl E L ι Y ⟨K₀, hKold⟩
  let N := (integralScalarExtension l E L ι Y).obj K₀
  let eL := purCoefficientModel l L Y
  have := (boundedConstructibleDerivedCompleteIntegral_isTriangulated D l hDl L Y).1
  have hN₀ : boundedConstructibleDerivedCompleteIntegral D l hDl L Y
      (eL.functor.obj (eL.inverse.obj N)) :=
    ObjectProperty.prop_of_iso _ (eL.counitIso.app N).symm hN
  have hcompleteN : IsDerivedCompleteUnrestricted l L Y
      (eL.functor.obj (eL.inverse.obj N)) := ⟨D, hDl, hN₀.1⟩
  have hsfN₀ : sfIntegralConstructible l L Y (eL.functor.obj (eL.inverse.obj N)) :=
    ⟨(purCoefficientModel_predicates l L Y (eL.inverse.obj N)).2.mp
      ((purCoefficientModel_predicates l L Y (eL.inverse.obj N)).1.mpr hcompleteN),
      hN₀.2⟩
  have hsfN : sfIntegralConstructible l L Y N :=
    ObjectProperty.prop_of_iso _ (eL.counitIso.app N) hsfN₀
  exact ObjectProperty.prop_of_iso _
    ((integralScalarExtension l E L ι Y).mapIso (eE.counitIso.app K)) hsfN

/-- The completed scalar extension restricted to intrinsic bounded constructible
objects. Its object map is the ambient extension and its morphism map is inherited.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
-/
noncomputable def sfConstructibleIntegralScalarExtension
    (p l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (Y : AlgebraicGeometry.Scheme.{u}) :
    sfIntegralConstructibleCategory l E Y ⥤
      sfIntegralConstructibleCategory l L Y :=
  (sfIntegralConstructible l L Y).lift
    ((sfIntegralConstructible l E Y).ι ⋙ integralScalarExtension l E L ι Y)
    (fun X ↦ sfIntegralScalarExtension_constructible p l _hl E L ι Y X.obj X.property)

/-- The restricted functor is linear for the integral coefficient action.
Source: blueprint order 1460 (blueprint: lem-weil-integral-scalar-extension-constructible).
Proof: the ambient completed extension is linear on morphisms; the full-subcategory
restriction preserves the same equality.
-/
theorem sfConstructibleIntegralScalarExtension_smul
    (p l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (Y : AlgebraicGeometry.Scheme.{u})
    (K K' : sfIntegralConstructibleCategory l E Y)
    (f : K ⟶ K') (a : Padic.coefficientExtensionIntegers l E) :
    (integralScalarExtension l E L ι Y).map
        ((integralScalarDerivedAction l E Y a).app K.obj ≫ f.hom) =
      (integralScalarDerivedAction l L Y
          (integralScalarIntegerInclusion l E L ι a)).app
          ((sfConstructibleIntegralScalarExtension p l _hl E L ι Y).obj K).obj ≫
        ((sfConstructibleIntegralScalarExtension p l _hl E L ι Y).map f).hom := by
  exact (integralScalarExtensionWellDefined l E L ι Y).2.choose_spec.choose_spec.2.2.2.2
    a K.obj K'.obj f.hom

end WeilConjectures
