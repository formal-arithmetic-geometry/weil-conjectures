/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Preadditive

import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Preservation of quasi-isomorphisms between K-flat complexes

Source: Weil conjectures blueprint, `sec-proetale-coefficients`,
`sk-def-sfb-derived-categories`, definition `def-sfb-preserves-kflat-quasi-iso`
(blueprint: def-sfb-preserves-kflat-quasi-iso).

The binary total tensor is Mathlib's `HomologicalComplex.tensorObj`, with maps
`HomologicalComplex.tensorHom`. Its degree `n` is the coproduct indexed by pairs
`(p, q)` with `p + q = n`. The differential is `d_P ⊗ 1 + (-1)^p (1 ⊗ d_Q)`
on the `(p, q)` summand. Countable coproducts suffice for this construction;
no preservation of these coproducts by tensoring is assumed.

## Main definitions

* `CochainComplex.IsKFlatForTotalTensor`: preservation of quasi-isomorphisms by
  both binary total tensor functors.
* `CategoryTheory.Functor.PreservesTotalTensorKFlatQuasiIso`: termwise preservation
  of quasi-isomorphisms between two such complexes.
-/

@[expose] public section

universe uC vC uD vD

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]

/-- A complex is K-flat if total tensoring on either side preserves every quasi-isomorphism.
(blueprint: def-sfb-preserves-kflat-quasi-iso).

`tensorHom (𝟙 P) s` and `tensorHom s (𝟙 P)` are the morphism actions of the two
functors obtained by fixing one input of `(curriedTensor C).map₂CochainComplex`.
This definition requires only binary total tensors, not a monoidal structure on complexes. -/
def IsKFlatForTotalTensor (P : CochainComplex C ℤ) : Prop :=
  (∀ {Q Q' : CochainComplex C ℤ} (s : Q ⟶ Q'),
    QuasiIso s → QuasiIso (HomologicalComplex.tensorHom (𝟙 P) s)) ∧
  (∀ {Q Q' : CochainComplex C ℤ} (s : Q ⟶ Q'),
    QuasiIso s → QuasiIso (HomologicalComplex.tensorHom s (𝟙 P)))

end CochainComplex

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]

/-- An additive functor preserves K-flat quasi-isomorphisms when its termwise action
preserves every quasi-isomorphism between two K-flat complexes.
(blueprint: def-sfb-preserves-kflat-quasi-iso). No tensor structure on `D` is required. -/
class PreservesTotalTensorKFlatQuasiIso (F : C ⥤ D) [F.Additive] : Prop where
  /-- The termwise image of a quasi-isomorphism between K-flat complexes is a
  quasi-isomorphism. -/
  quasiIso_map {P P' : CochainComplex C ℤ}
    (hP : P.IsKFlatForTotalTensor) (hP' : P'.IsKFlatForTotalTensor)
    (s : P ⟶ P') [QuasiIso s] :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s)

/-- Every exact additive functor preserves K-flat quasi-isomorphisms.
Stacks Project, Tags 010N and 015F (blueprint: def-sfb-preserves-kflat-quasi-iso).

Proof: finite-limit and finite-colimit preservation give the natural cohomology
comparisons from `lem-weil-pbc-exact-functor-complex-cohomology`, implemented by
`Functor.homologyFunctorIso`. For any quasi-isomorphism `s`, these identify each
cohomology map of `F(s)` with the conjugate of `F` applied to the cohomology map of `s`.
The latter is invertible: applying `F` to an inverse supplies its inverse. Thus all
cohomology maps of `F(s)` are invertible. Restrict this argument to morphisms with
both endpoints K-flat. No preservation of coproducts by `F` is needed. -/
theorem preservesTotalTensorKFlatQuasiIso_of_exact (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.PreservesTotalTensorKFlatQuasiIso := by
  refine ⟨fun _ _ s _ ↦ ?_⟩
  exact HomologicalComplex.quasiIso_map_of_preservesHomology s F

end CategoryTheory.Functor
