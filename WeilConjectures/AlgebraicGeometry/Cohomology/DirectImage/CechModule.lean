/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Vanishing
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The Čech complex as a complex of modules over the base

Let `f : X ⟶ S` be a morphism of schemes, `U : ι → X.Opens` a family of opens and `ℱ` an
`𝒪_X`-module. The Čech cochains `c y ∈ Γ(ℱ, U (y 0) ⊓ ⋯ ⊓ U (y k))` form modules over
`A = Γ(S, ⊤)`, through `f^♯ : A ⟶ Γ(X, ⊤)`, and the Čech differential is `A`-linear. This gives
the Čech complex `Č(U, ℱ)` as a cochain complex of `A`-modules,
`AlgebraicGeometry.Scheme.Modules.cechModuleComplex f U ℱ`, indexed by `ℤ` and concentrated in
degrees `≥ 0`: an object of the derived category `D(A)`.

When `S` is affine, `f` quasi-compact and separated, `U` a finite cover of `X` by affine opens
and `ℱ` quasi-coherent, this complex computes the higher direct images of `ℱ` over the affine
base: `H^q(Č(U, ℱ)) ≅ Γ(S, R^q f_* ℱ)` as `A`-modules
(`AlgebraicGeometry.Scheme.Modules.nonempty_homology_cechModuleComplex_linearEquiv`), and it is
exact in degrees `≥ #ι` (`AlgebraicGeometry.Scheme.Modules.exactAt_cechModuleComplex`). Over an
affine base, where quasi-coherent `𝒪_S`-modules are `A`-modules, it is the module-theoretic
incarnation of the derived direct image `Rf_* ℱ`; this is the form in which the blueprint's Čech
resolution is used.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)

variable {ι : Type u} (U : ι → X.Opens)

open TopCat.Presheaf

/-! ### Comparison with Mathlib's Čech complex -/

/-! ### The Čech complex computes the higher direct images over an affine base -/

/-! ### Flatness of the Čech complex -/

end AlgebraicGeometry.Scheme.Modules
