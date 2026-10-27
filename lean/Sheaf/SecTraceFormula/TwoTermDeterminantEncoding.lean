/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Sheaf.LinearAlgebra.ProjectiveDeterminantModule

/-!
# Two-term determinant data on the arrow category of modules

Source: Stacks Project, More on Algebra, Tag 0FJI, complexes concentrated in degrees
`-1,0` (blueprint: def-trf-two-term-determinant-encoding).

An arrow of modules is exactly the differential of a two-term complex, and an arrow
morphism is exactly a chain map. We use Mathlib's arrow category directly: `left` is
degree `-1`, `right` is degree `0`, and `hom` is the differential. No theorem about
kernel normalization or determinant calculus is imported here.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct

namespace Module.TwoTerm

/-- Degreewise surjectivity, in the arrow encoding of two-term complexes.
Source: Stacks Project, Tag 0FJI (blueprint: def-trf-two-term-determinant-encoding). -/
def DegreewiseSurjective {R : Type u} [CommRing R]
    {P Q : Arrow (ModuleCat.{v} R)} (a : P ⟶ Q) : Prop :=
  Function.Surjective (ModuleCat.Hom.hom a.left) ∧
    Function.Surjective (ModuleCat.Hom.hom a.right)

/-- The induced map on degree-minus-one cohomology, which has no boundaries.
Source: Stacks Project, Tag 0FJI (blueprint: def-trf-two-term-determinant-encoding). -/
def kernelNeg {R : Type u} [CommRing R]
    {P Q : Arrow (ModuleCat.{v} R)} (a : P ⟶ Q) :
    LinearMap.ker (ModuleCat.Hom.hom P.hom) →ₗ[R]
      LinearMap.ker (ModuleCat.Hom.hom Q.hom) :=
  ((ModuleCat.Hom.hom a.left).domRestrict _).codRestrict _ (by
    intro x
    change ModuleCat.Hom.hom Q.hom (ModuleCat.Hom.hom a.left x) = 0
    have hx := congrArg (fun f ↦ ModuleCat.Hom.hom f (x : P.left)) a.w
    change ModuleCat.Hom.hom Q.hom (ModuleCat.Hom.hom a.left x) =
      ModuleCat.Hom.hom a.right (ModuleCat.Hom.hom P.hom x) at hx
    have hzero : ModuleCat.Hom.hom P.hom (x : P.left) = 0 := x.property
    simpa only [hzero, map_zero] using hx)

/-- Bijectivity on the kernel in degree `-1` and on the cokernel in degree `0`.
The latter is written as injectivity and surjectivity on representatives modulo boundaries.
Source: Stacks Project, Tag 0FJI (blueprint: def-trf-two-term-determinant-encoding). -/
def QuasiIso {R : Type u} [CommRing R]
    {P Q : Arrow (ModuleCat.{v} R)} (a : P ⟶ Q) : Prop :=
  Function.Bijective (kernelNeg a) ∧
    (∀ x y : P.right, ModuleCat.Hom.hom a.right x - ModuleCat.Hom.hom a.right y ∈
      LinearMap.range (ModuleCat.Hom.hom Q.hom) →
      x - y ∈ LinearMap.range (ModuleCat.Hom.hom P.hom)) ∧
    (∀ y : Q.right, ∃ x : P.right, y - ModuleCat.Hom.hom a.right x ∈
      LinearMap.range (ModuleCat.Hom.hom Q.hom))

/-- The two-term determinant line, with ordinary ungraded tensor symmetry.
Source: Stacks Project, Tag 0FJI (blueprint: def-trf-two-term-determinant-encoding). -/
abbrev determinant {R : Type u} [CommRing R] (P : Arrow (ModuleCat.{v} R)) : Type _ :=
  Module.determinantModule R (P.right : Type v) ⊗[R]
    Module.Dual R (Module.determinantModule R (P.left : Type v))

/-- The differential restricted to the degreewise kernel of the chain map.
Source: Stacks Project, Tag 0FJI (blueprint: def-trf-two-term-determinant-encoding). -/
def kernelDifferential {R : Type u} [CommRing R]
    {P Q : Arrow (ModuleCat.{v} R)} (a : P ⟶ Q) :
    LinearMap.ker (ModuleCat.Hom.hom a.left) →ₗ[R]
      LinearMap.ker (ModuleCat.Hom.hom a.right) :=
  ((ModuleCat.Hom.hom P.hom).domRestrict _).codRestrict _ (by
    intro x
    change ModuleCat.Hom.hom a.right (ModuleCat.Hom.hom P.hom x) = 0
    have hx := congrArg (fun f ↦ ModuleCat.Hom.hom f (x : P.left)) a.w
    change ModuleCat.Hom.hom Q.hom (ModuleCat.Hom.hom a.left x) =
      ModuleCat.Hom.hom a.right (ModuleCat.Hom.hom P.hom x) at hx
    have hzero : ModuleCat.Hom.hom a.left (x : P.left) = 0 := x.property
    simpa only [hzero, map_zero] using hx.symm)

/-- The determinant line of the degreewise kernel complex.
Source: Stacks Project, Tag 0FJI (blueprint: def-trf-two-term-determinant-encoding). -/
abbrev kernelDeterminant {R : Type u} [CommRing R]
    {P Q : Arrow (ModuleCat.{v} R)} (a : P ⟶ Q) : Type _ :=
  Module.determinantModule R (LinearMap.ker (ModuleCat.Hom.hom a.right)) ⊗[R]
    Module.Dual R (Module.determinantModule R (LinearMap.ker (ModuleCat.Hom.hom a.left)))

end Module.TwoTerm

end
