/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Restriction of scalars preserves homology

Restriction of scalars along a ring homomorphism does not change the underlying abelian groups
and maps, so it preserves the exactness of short complexes, hence their homology. In particular
the homology of a complex of modules, with scalars restricted, is the homology of the complex
with scalars restricted.

## Main definitions

- `ModuleCat.restrictScalarsHomologyIso`: the homology of a homological complex of `S`-modules
  with scalars restricted to `R` along `f : R →+* S` is the restriction of scalars of its
  homology.
-/

@[expose] public section

universe v u₁ u₂

open CategoryTheory

namespace ModuleCat

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

/-- **Restriction of scalars preserves homology**, since it preserves the exactness of short
complexes. -/
instance preservesHomology_restrictScalars : (restrictScalars.{v} f).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun T hT ↦ by
    rw [ShortComplex.moduleCat_exact_iff] at hT ⊢
    exact hT

/-- The homology of a homological complex of `S`-modules, with scalars restricted along
`f : R →+* S`, is the restriction of scalars of its homology. -/
noncomputable def restrictScalarsHomologyIso {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} S) c) (i : ι) :
    (((restrictScalars.{v} f).mapHomologicalComplex c).obj K).homology i ≅
      (restrictScalars.{v} f).obj (K.homology i) :=
  (K.sc i).mapHomologyIso (restrictScalars.{v} f)

end ModuleCat
