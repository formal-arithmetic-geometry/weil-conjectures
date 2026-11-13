/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-! # Quasi-coherent algebras and their affine-local properties

Algebra sheaves and their underlying modules reuse `Scheme.CommAlgebraSheaf`
and `Scheme.CommAlgebraSheaf.toModule`. Quasi-coherence uses Mathlib's existing
module-sheaf predicate. Finiteness, integrality and finite presentation are tested
on every affine open using the existing ring-homomorphism predicates.

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry

/-- Quasi-coherence of the existing underlying module of an algebra sheaf. -/
def Scheme.IsQuasiCoherentAlgebra (X : Scheme.{u}) : ObjectProperty X.CommAlgebraSheaf :=
  fun A ↦ A.toModule.IsQuasicoherent

/-- The full category of quasi-coherent algebra sheaves. -/
abbrev QuasiCoherentAlgebra (X : Scheme.{u}) := (X.IsQuasiCoherentAlgebra).FullSubcategory

/-- A finite algebra sheaf has finite section algebras on every affine open. -/
def Scheme.CommAlgebraSheaf.IsFinite {X : Scheme.{u}} (A : X.CommAlgebraSheaf) : Prop :=
  ∀ (U : X.Opens), IsAffineOpen U → (A.hom.hom.app (op U)).hom.Finite

/-- An integral algebra sheaf has integral section algebras on every affine open. -/
def Scheme.CommAlgebraSheaf.IsIntegral {X : Scheme.{u}} (A : X.CommAlgebraSheaf) : Prop :=
  ∀ (U : X.Opens), IsAffineOpen U → (A.hom.hom.app (op U)).hom.IsIntegral

/-- Finite presentation as an algebra, rather than as a module, on every affine open. -/
def Scheme.CommAlgebraSheaf.IsFinitePresentation {X : Scheme.{u}}
    (A : X.CommAlgebraSheaf) : Prop :=
  ∀ (U : X.Opens), IsAffineOpen U → (A.hom.hom.app (op U)).hom.FinitePresentation

/-- The ordered collection of all finite quasi-coherent subalgebras of `A`.
Subobjects of algebra sheaves identify inclusions that differ by an isomorphism. -/
abbrev QuasiCoherentAlgebra.FiniteSubalgebras {X : Scheme.{u}}
    (A : QuasiCoherentAlgebra X) :=
  {B : Subobject A.obj // X.IsQuasiCoherentAlgebra (B : X.CommAlgebraSheaf) ∧
    Scheme.CommAlgebraSheaf.IsFinite (B : X.CommAlgebraSheaf)}

/-- The diagram of finite quasi-coherent subalgebras, with their inclusion maps. -/
def QuasiCoherentAlgebra.finiteSubalgebraDiagram {X : Scheme.{u}}
    (A : QuasiCoherentAlgebra X) : A.FiniteSubalgebras ⥤ X.CommAlgebraSheaf :=
  (show Monotone (fun B : A.FiniteSubalgebras ↦ B.val) from
    fun _ _ h ↦ h).functor ⋙ Subobject.underlying

end AlgebraicGeometry
