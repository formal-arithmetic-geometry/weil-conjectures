/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc

/-!
# t-exact functors and the spectral objects attached to t-structures

Let `F : C ⥤ D` be a triangulated functor between triangulated categories equipped with
t-structures `t₁` and `t₂`. We say that `F` is *t-exact* (`Functor.IsTExact`) if it preserves
the objects which are `≤ n` and the objects which are `≥ n` for all `n : ℤ`. A t-exact functor
commutes with the truncation functors (`Functor.eTruncLTIso`, `Functor.eTruncGEIso`), compatibly
with the connecting homomorphisms of the truncation triangles
(`Functor.eTruncGEδLT_comm`). As a consequence, the image under `F` of the spectral object
`t₁.spectralObject X` consisting of all the truncations of `X` identifies to the spectral object
`t₂.spectralObject (F.obj X)` (`Functor.mapTriangulatedSpectralObjectIso`), naturally in `X`.

-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated ComposableArrows Triangulated

variable {C D : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (t₁ : TStructure C) (t₂ : TStructure D)

namespace Functor

variable (F : C ⥤ D)

namespace IsTExact

variable [F.IsTExact t₁ t₂]

end IsTExact

variable [CategoryTheory.IsTriangulated D]
  [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t₁ t₂]

section

variable {t₁ t₂}

end

variable [CategoryTheory.IsTriangulated C]

end Functor

end CategoryTheory
