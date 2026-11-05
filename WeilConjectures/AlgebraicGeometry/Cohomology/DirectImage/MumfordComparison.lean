/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolutionBase
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechSectionsBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.QuasiIsoSections
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexOfMatrix
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplexLocus
public import Mathlib.RingTheory.TensorProduct.Free
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.FreeAwayBaseChange

/-!
# Comparison of a free model of the Čech complex with the higher direct images

Consider a cartesian square of schemes
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` affine, a finite affine cover `U` of `X` and a quasi-coherent `𝒪_X`-module `ℱ`.
Let `R` be an `A`-algebra with a ring map `τ : R ⟶ Γ(T, ⊤)` over `A`, `P` a complex of free
`R`-modules of finite rank (with chosen bases) and `Φ : P ⟶ R ⊗[A] Č(U, ℱ)` a morphism which is
a quasi-isomorphism after every base change `R ⟶ B`. Then the complex of free `𝒪_T`-modules with
the matrices of the differentials of `P` (mapped by `τ`) computes the higher direct images
`R^q f'_* g'^* ℱ` (`AlgebraicGeometry.Scheme.Modules.nonempty_homology_freeComplex_iso`).

The comparison morphism to the Čech resolution `f'_* Č(g'⁻¹ U, g'^* ℱ)` is given on the basis
vectors by the images of the basis of `P` under `Φ` and the base change of Čech cochains; over an
affine open `W` of `T` it is identified with `Γ(T, W) ⊗[R] Φ`, hence a quasi-isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Opposite

namespace CochainComplex

variable {R : Type u} [CommRing R] {κ : ℤ → Type u} [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
  (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ∀ n, Module.Basis (κ n) R (P.X n))

end CochainComplex

namespace TensorProduct

variable {R : Type u} [CommRing R] (B : Type u) [CommRing B] [Algebra R B] {N : Type u}
  [AddCommGroup N] [Module R N]

end TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)
  {R : Type u} [CommRing R] [Algebra Γ(S, ⊤) R]

section Sections

variable (W : T.Opens) [Algebra Γ(S, ⊤) Γ(T, W)] [Algebra R Γ(T, W)]
  [IsScalarTower Γ(S, ⊤) R Γ(T, W)]
  (hg : algebraMap Γ(S, ⊤) Γ(T, W) = (g.appLE ⊤ W (le_top.trans g.preimage_top.ge)).hom)

end Sections

/-! ### The base change map of Čech complexes on sections, as a morphism of complexes -/

section SectionsHom

variable (W : T.Opens) [Algebra Γ(S, ⊤) Γ(T, W)] [Algebra R Γ(T, W)]
  [IsScalarTower Γ(S, ⊤) R Γ(T, W)]
  (hg : algebraMap Γ(S, ⊤) Γ(T, W) = (g.appLE ⊤ W (le_top.trans g.preimage_top.ge)).hom)

end SectionsHom

/-! ### The complex of free modules of a complex with bases -/

section Free

variable {Z : Scheme.{u}} {κ : ℤ → Type u} [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
  (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ∀ n, Module.Basis (κ n) R (P.X n))

end Free

/-! ### The comparison morphism -/

section Comparison

variable [Algebra Γ(S, ⊤) Γ(T, ⊤)] [Algebra R Γ(T, ⊤)] [IsScalarTower Γ(S, ⊤) R Γ(T, ⊤)]
  (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = (g.appLE ⊤ ⊤ (le_top.trans g.preimage_top.ge)).hom)
  {κ : ℤ → Type u} [∀ n, Fintype (κ n)] [∀ n, DecidableEq (κ n)]
  (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ∀ n, Module.Basis (κ n) R (P.X n))
  (Φ : P.restriction ComplexShape.embeddingUpNat ⟶
    ((ModuleCat.baseChange Γ(S, ⊤) R).mapHomologicalComplex _).obj (cechModuleComplexNat f ℱ U))

end Comparison

end AlgebraicGeometry.Scheme.Modules
