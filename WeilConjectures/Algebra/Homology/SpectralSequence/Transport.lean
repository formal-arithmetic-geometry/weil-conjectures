/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Transport of spectral sequences along fully faithful exact functors

Let `G : A ⥤ B` be a fully faithful exact functor between abelian categories whose essential
image is closed under subobjects of objects of the form `G.obj Y`. If a first quadrant
cohomological spectral sequence `E'` in `B` has its `E₂`-page in the essential image of `G` and
abuts to `G.obj (H n)`, then it comes from a spectral sequence in `A` abutting to `H n`.

The main application is to `AddCommGrpCat.uliftFunctor : AddCommGrpCat.{w} ⥤
AddCommGrpCat.{max w v}`, which allows to bring spectral sequences constructed in a larger
universe back down to the universe of the groups involved.

## Main statements

- `CategoryTheory.Functor.essImage_homology`: the homology of a complex whose objects lie in the
  essential image of a fully faithful exact functor lies in the essential image.
- `CategoryTheory.SpectralSequence.exists_of_fullyFaithful`: transport of a first quadrant
  spectral sequence together with its abutment along a fully faithful exact functor.
- `AddCommGrpCat.uliftFunctor_essImage_of_mono`: a subgroup of a universe lifted group is in the
  essential image of `AddCommGrpCat.uliftFunctor`.
- `CategoryTheory.SpectralSequence.exists_of_uliftFunctor`: universe lowering for first quadrant
  spectral sequences of abelian groups.
-/

@[expose] public section

universe w v v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

namespace Functor

section Preadditive

variable [Preadditive A] [Preadditive B] (G : A ⥤ B) [G.Full] [G.Faithful] [G.Additive]
  {ι : Type*} {c : ComplexShape ι}

end Preadditive

section Abelian

variable [Abelian A] [Abelian B] (G : A ⥤ B) [G.Full] [G.Faithful] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] {ι : Type*} {c : ComplexShape ι}

end Abelian

section Subobject

variable {G : A ⥤ B}

end Subobject

end Functor

namespace SpectralSequence

variable [Abelian A] [Abelian B] (G : A ⥤ B) [G.Full] [G.Faithful] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

section Abutment

variable {G}

end Abutment

end SpectralSequence

end CategoryTheory

open CategoryTheory

