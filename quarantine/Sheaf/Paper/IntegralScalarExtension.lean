/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.IntegralScalarExtensionWellDefined
public import Sheaf.Paper.IntegralConstructibleLinear
public import Sheaf.Paper.IntegralDerivedReduction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Completed integral scalar extension

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1460; Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- Completed extension, obtained by the universal localization of the specified
strict Roos construction on K-flat complexes with flat terms. The construction has
actual data: its tower, transition maps and diagonal cone maps are those of
`integralScalarOnGood`, not arbitrary maps between homotopy limits.
Source: blueprint order 1460; Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable def integralScalarExtension :
    DerivedCategory (integralTowerModules l E Y) ⥤
      DerivedCategory (integralTowerModules l L Y) :=
  (integralScalarExtensionWellDefined l E L ι Y).2.choose

/-- The representative comparison is part of the universal localization datum.
Source: blueprint order 1460; Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable def integralScalarExtensionComparison :
    integralOperationsGoodLocalization l E Y ⋙ integralScalarExtension l E L ι Y ≅
      integralScalarOnGood l E L ι Y :=
  (integralScalarExtensionWellDefined l E L ι Y).2.choose_spec.choose

/-- Additivity of the specified completed extension.
Source: blueprint order 1460 (blueprint: def-weil-integral-scalar-extension). -/
noncomputable instance integralScalarExtension_additive :
    (integralScalarExtension l E L ι Y).Additive :=
  (integralScalarExtensionWellDefined l E L ι Y).2.choose_spec.choose_spec.1

end WeilConjectures


namespace WeilConjectures

open CategoryTheory CategoryTheory.Limits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- The completed coefficient map, uniquely fixed by its finite quotient projections.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension).
Proof: the quotient inclusion maps commute with reduction. The limit universal property
therefore gives the completed map; joint monicity of its projections gives uniqueness. -/
theorem integralCompletedScalarMap_existsUnique :
    ∃! φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
        completedIntegralCommRingSheafUnrestricted l L Y,
      ∀ n : ℕ, φ ≫ completedIntegralCommRingProjectionUnrestricted l L Y n =
        integralScalarRho l E L ι Y n := by
  sorry

/-- The actual map of completed coefficient rings, fixed at every finite level.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable def integralCompletedScalarMap :
    completedIntegralCommRingSheafUnrestricted l E Y ⟶
      completedIntegralCommRingSheafUnrestricted l L Y :=
  (integralCompletedScalarMap_existsUnique l E L ι Y).exists.choose

/-- The ordinary tensor functor with its prescribed object and morphism formulas.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension).
Proof: use the sectionwise balanced tensor map on each sheaf morphism and then
sheafify. The tensor identity and composition equations descend by the universal
property of sheafification. Additivity holds on tensor generators and hence locally
on all sections. Both objects and maps are specified, so no arbitrary functor is chosen. -/
theorem integralOrdinaryScalarWitness :
    ∃ (F : integralTowerModules.{u, u} l E Y ⥤ integralTowerModules.{u, u} l L Y)
      (h : ∀ N, F.obj N = SheafOfModules.changeOfRings
        (integralCompletedScalarMap l E L ι Y) N)
      (_ : ∀ {N N' : integralTowerModules.{u, u} l E Y} (f : N ⟶ N'),
        F.map f = eqToHom (h N) ≫ SheafOfModules.changeOfRingsHom
          (integralCompletedScalarMap l E L ι Y) N f ≫ eqToHom (h N').symm)
      , F.Additive := by
  sorry

/-- Ordinary tensor with the finite free completed coefficient extension.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable def integralOrdinaryScalar :
    integralTowerModules.{u, u} l E Y ⥤ integralTowerModules.{u, u} l L Y :=
  (integralOrdinaryScalarWitness l E L ι Y).choose

/-- Additivity of ordinary extension of scalars.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable instance integralOrdinaryScalar_additive :
    (integralOrdinaryScalar l E L ι Y).Additive :=
  (integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose_spec.choose_spec

/-- Finite coefficient extensions are finite free, so their ordinary sheaf tensor is exact.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: def-weil-integral-scalar-extension).
Proof: O_L is finite free over O_E. Choose an integral basis only in the proof. Tensor
with that finite free module commutes with the finite coefficient limits defining the
completed sheaf, since finite products and finite sums agree for modules. Thus the
completed coefficient extension is finite locally free. Sectionwise tensor followed by
exact sheafification is exact. Its adjunction gives preservation of finite colimits,
and flatness gives preservation of finite limits. No geometric finiteness is used. -/
theorem integralOrdinaryScalar_exact :
    PreservesFiniteLimits (integralOrdinaryScalar l E L ι Y) ∧
      PreservesFiniteColimits (integralOrdinaryScalar l E L ι Y) := by
  sorry

/-- Exactness on finite limits. Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable instance integralOrdinaryScalar_finiteLimits :
    PreservesFiniteLimits (integralOrdinaryScalar l E L ι Y) :=
  (integralOrdinaryScalar_exact l E L ι Y).1

/-- Exactness on finite colimits. Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable instance integralOrdinaryScalar_finiteColimits :
    PreservesFiniteColimits (integralOrdinaryScalar l E L ι Y) :=
  (integralOrdinaryScalar_exact l E L ι Y).2

/-- Exact ordinary extension, computed termwise on derived complexes. On complete
objects this is the completed scalar extension; that assertion is recorded separately.
Source: Bhatt--Scholze, Proposition 3.5.1
(blueprint: def-weil-integral-scalar-extension). -/
noncomputable abbrev integralOrdinaryDerivedScalar :=
  (integralOrdinaryScalar l E L ι Y).mapDerivedCategory

end WeilConjectures
