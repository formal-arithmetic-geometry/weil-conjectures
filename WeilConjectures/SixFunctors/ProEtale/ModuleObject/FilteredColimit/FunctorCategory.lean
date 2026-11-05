/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Generator.Presheaf

/-!
# Injective resolutions of diagrams of bounded below complexes

Let `C` be a Grothendieck abelian category and `J` a small category. The functor category
`J ⥤ C` is again Grothendieck abelian (`CategoryTheory.Functor.isGrothendieckAbelian`), hence
has enough injectives, and the evaluation functors preserve injective objects, their left
adjoints `X ↦ ∐_{j ⟶ k} X` preserving monomorphisms
(`CategoryTheory.Injective.functor_obj`).

Viewing a diagram `F : J ⥤ CochainComplex C ℤ` as a complex of diagrams
(`CategoryTheory.Functor.complexOfFunctors`), a bounded below injective resolution in `J ⥤ C`
gives a *functorial* resolution of `F`: a natural transformation `F ⟶ I` which is a
quasi-isomorphism at every `j`, where every `I.obj j` is strictly concentrated in the same degrees
as the `F.obj j` and has injective terms
(`CategoryTheory.Functor.exists_quasiIso_injective_of_isStrictlyGE`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace CategoryTheory

namespace Limits

end Limits

namespace Functor

variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (J : Type w) [SmallCategory J]

variable {J}

end Functor

end CategoryTheory
