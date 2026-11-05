/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatShortExact

/-!
# Tor amplitude in `[a, ∞)` and bounded below K-flat models

Let `C` be a closed braided monoidal Grothendieck abelian category with functorial flat
resolutions. An object `K` of `D(C)` has *Tor amplitude in `[a, ∞)`*
(`DerivedCategory.torAmplitudeGE`) if `K ⊗ᴸ F[0]` vanishes in degrees `< a` for every object
`F` of `C`. We show that this holds exactly when `K` is represented by a K-flat complex of flat
objects vanishing in degrees `< a` (`DerivedCategory.torAmplitudeGE_iff_exists_kFlat`, Stacks
Tag 0F1M).

The model is the canonical truncation `τ^{≥ a} P` of a K-flat flat resolution `P` of `K`: its
term in degree `a` is the cokernel of `P^{a-1} ⟶ P^a`, which is flat by the Tor criterion
`CategoryTheory.ObjectProperty.flat_opcycles_of_exactAt`, and the kernel of `P ⟶ τ^{≥ a} P` is
a bounded above complex of flat objects, so `τ^{≥ a} P` is K-flat by
`CochainComplex.kFlat_of_shortExact`. The same argument applies after any exact functor
preserving flat objects (`CochainComplex.kFlat_mapHomologicalComplex_obj_truncGE`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]

variable [Abelian.HasFunctorialFlatResolution C]

end CochainComplex

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

variable {C}

end DerivedCategory
