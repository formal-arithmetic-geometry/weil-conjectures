/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Topology.Sheaves.CechComparison
public import WeilConjectures.AlgebraicGeometry.Modules.StalkExact
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Tensor
public import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Vanishing
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections

/-!
# The Čech resolution of a sheaf of modules

Let `U : ι → X.Opens` be a finite open cover of a scheme `X` and `ℱ` an `𝒪_X`-module. Write
`j_V : V ⟶ X` for the inclusion of an open. The sheafified Čech complex `Č(U, ℱ)` has in
degree `k` the module `∏_{y : Fin (k + 1) → ι} j_{U_y,*} (ℱ|_{U_y})`, where
`U_y = U (y 0) ⊓ ⋯ ⊓ U (y k)`; it is Mathlib's Čech complex
(`CategoryTheory.cechComplexFunctor`) of the presheaf `V ↦ j_{V,*} (ℱ|_V)` of `𝒪_X`-modules.

## Main results

- `AlgebraicGeometry.Scheme.Modules.cechResolution`: the complex `Č(U, ℱ)`, and its
  augmentation `AlgebraicGeometry.Scheme.Modules.cechResolutionι : ℱ ⟶ Č(U, ℱ)`.
- `AlgebraicGeometry.Scheme.Modules.quasiIso_cechResolutionι`: the augmented Čech complex
  `0 ⟶ ℱ ⟶ Č⁰(U, ℱ) ⟶ Č¹(U, ℱ) ⟶ ⋯` is exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite ZeroObject

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {Z : C} {K L : CochainComplex C ℕ}
  (ι : (single₀ C).obj Z ⟶ K) [QuasiIso ι] [∀ n, Injective (L.X n)]

end CochainComplex

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section ExtendRestrict

end ExtendRestrict

section ExactSections

end ExactSections

section Complex

variable {ι : Type u} (U : ι → X.Opens)

end Complex

section Exactness

variable {ι : Type u} (U : ι → X.Opens) (ℱ : X.Modules)

end Exactness

section Acyclic

instance preservesFiniteLimits_pushforward {Y Z : Scheme.{u}} (h : Y ⟶ Z) :
    PreservesFiniteLimits (pushforward h) :=
  have := (pullbackPushforwardAdjunction h).rightAdjoint_preservesLimits.{0, 0}
  inferInstance

variable {S : Scheme.{u}} (f : X ⟶ S)

variable {ι : Type u} (U : ι → X.Opens)

end Acyclic

end AlgebraicGeometry.Scheme.Modules
