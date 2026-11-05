/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechModuleBaseChange

/-!
# The Čech complex of a module flat over an affine base

Let `f : X ⟶ S` be quasi-compact and separated with `S = Spec A` affine, `U` a finite cover of
`X` by affine opens and `ℱ` a quasi-coherent `𝒪_X`-module flat over `S`. The Čech complex
`Č(U, ℱ)` (`AlgebraicGeometry.Scheme.Modules.cechModuleComplex`) is a complex of flat
`A`-modules computing `Rf_* ℱ` over the affine base, and its formation commutes with every base
change `T = Spec B ⟶ S`. Being exact in degrees `≥ #U` after every base change, its modules of
cycles are flat in degrees `≥ #U - 1`
(`AlgebraicGeometry.Scheme.Modules.flat_ker_d_cechModuleComplex`), so that its truncation in
degrees `≤ #U - 1` is a bounded complex of flat `A`-modules quasi-isomorphic to it, compatibly
with every base change (`AlgebraicGeometry.Scheme.Modules.quasiIso_map_baseChange_ιTruncLE`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)

variable [IsAffine S] [IsSeparated f] [Fintype ι] [Nonempty ι] (hU : ∀ i, IsAffineOpen (U i))
  (hU' : iSup U = ⊤) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

end AlgebraicGeometry.Scheme.Modules
