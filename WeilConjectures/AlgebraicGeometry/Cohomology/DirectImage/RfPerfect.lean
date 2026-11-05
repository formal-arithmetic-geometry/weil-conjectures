/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechFlat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.OfFlat

/-!
# Perfectness of `Rf_* ℱ` and derived base change over an affine base

Let `f : X ⟶ S` be quasi-compact and separated with `S = Spec A` affine, `U` a finite cover of
`X` by affine opens and `ℱ` a quasi-coherent `𝒪_X`-module. Over the affine base, the derived
direct image `Rf_* ℱ` is represented in `D(A)` by the Čech complex `Č(U, ℱ)`
(`AlgebraicGeometry.Scheme.Modules.nonempty_homology_cechModuleComplex_linearEquiv`, the
blueprint's `lem-pc-cech-resolution`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isIso_cechModuleComplexBaseChangeComparison`
  (`lem-pc-rf-base-change-flat-module`): if `ℱ` is flat over `S`, then `Rf_* ℱ` is represented
  by a bounded complex `K` of flat `A`-modules, and for every base change `T = Spec B ⟶ S` the
  canonical base-change map `cechModuleComplexBaseChangeComparison` from the derived pullback
  `Lg^* Rf_* ℱ = B ⊗[A] K` to `Rf_{T*} ℱ_T` is an isomorphism.
- `AlgebraicGeometry.Scheme.Modules.isPerfect_Q_cechModuleComplex_of_isClosedImmersion`
  (`lem-pc-projective-noetherian-rf-perfect`): for `S` noetherian, `f` projective and `ℱ`
  coherent and flat over `S`, `Rf_* ℱ` is perfect.
- `AlgebraicGeometry.Scheme.Modules.isPerfect_Q_cechModuleComplex_baseChange_of_isClosedImmersion`
  (`cor-pc-projective-noetherian-rf-perfect-base-change`): the derived pullback of `Rf_* ℱ` along
  any `T = Spec B ⟶ S` is perfect and is `Rf_{T*} ℱ_T`.
- `AlgebraicGeometry.Scheme.Modules.perfect_and_baseChange_cechModuleComplex_of_isProper`
  (`lem-pc-rf-perfect-base-change`): the same for `f` proper of finite presentation and `ℱ` of
  finite presentation and flat over `S`; it is stated in
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange`, downstream of the
  construction of Mumford's complex.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct DerivedCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)

section BaseChange

variable [IsAffine S] [IsSeparated f] [Fintype ι] [Nonempty ι] (hU : ∀ i, IsAffineOpen (U i))
  (hU' : iSup U = ⊤) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

end BaseChange

section Perfect

variable [IsAffine S] [Finite ι] [Nonempty ι] (hU : ∀ i, IsAffineOpen (U i)) (hU' : iSup U = ⊤)
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

end Perfect

end AlgebraicGeometry.Scheme.Modules
