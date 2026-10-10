/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# The distinguished triangle of a short exact sequence in `D⁺`

A short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` in an abelian category gives a distinguished
triangle `X₁[0] ⟶ X₂[0] ⟶ X₃[0] ⟶ X₁[1]` in the bounded below derived category
(`CategoryTheory.ShortComplex.ShortExact.singleTrianglePlus` and
`CategoryTheory.ShortComplex.ShortExact.singleTrianglePlus_distinguished`): the lift of
Mathlib's `CategoryTheory.ShortComplex.ShortExact.singleTriangle` along the inclusion
`DerivedCategory.Plus C ⥤ DerivedCategory C`.

`CategoryTheory.ShortComplex.ShortExact.exists_mk_singleTrianglePlus_distinguished` states that
this triangle is distinguished in the form `Triangle.mk (E.f[0]) (E.g[0]) δ` for some `δ`, and
`CategoryTheory.ShortComplex.ShortExact.map_exact_of_isHomological` deduces that the image of
`E` under `singleFunctor 0 ⋙ G`, for a homological functor `G`, is exact. Both lemmas take
the zero morphisms of the categories involved as arbitrary instances.

## Implementation notes

`exists_mk_singleTrianglePlus_distinguished` is the form to use over a concrete abelian
category: identifying the objects and morphisms of `hE.singleTrianglePlus` with those of
`DerivedCategory.Plus.singleFunctor C 0` there makes the kernel unfold the derived category,
whereas here the identification is checked once, over an abstract `C`. The zero morphisms are
arbitrary instances, reduced to those of the abelian structure by `Subsingleton.elim`, so that
the lemmas apply as they stand to short complexes of sheaves: the zero morphisms of sheaves
come from the full subcategory of sheaves, and unifying them with those of the abelian
structure at the call site is expensive for the kernel. `singleTrianglePlus_distinguished`
itself cannot be stated for arbitrary zero morphisms, since its connecting morphism is built
from `CategoryTheory.ShortComplex.ShortExact.singleδ`, which needs the abelian instance.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex.ShortExact

open Pretriangulated

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

section

variable {E : ShortComplex C}

/-- The triangle `X₁[0] ⟶ X₂[0] ⟶ X₃[0] ⟶ X₁[1]` in the bounded below derived category
attached to a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`: the lift of
`CategoryTheory.ShortComplex.ShortExact.singleTriangle` along the inclusion
`DerivedCategory.Plus C ⥤ DerivedCategory C`. -/
noncomputable def singleTrianglePlus (hE : E.ShortExact) : Triangle (DerivedCategory.Plus C) :=
  Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map E.f)
    ((DerivedCategory.Plus.singleFunctor C 0).map E.g)
    (DerivedCategory.TStructure.t.plus.fullyFaithfulι.preimage
      (hE.singleδ ≫ (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj E.X₁)))

set_option backward.isDefEq.respectTransparency false in
/-- The triangle `X₁[0] ⟶ X₂[0] ⟶ X₃[0] ⟶ X₁[1]` attached to a short exact sequence is
distinguished in the bounded below derived category. -/
lemma singleTrianglePlus_distinguished (hE : E.ShortExact) :
    hE.singleTrianglePlus ∈ distTriang (DerivedCategory.Plus C) := by
  refine isomorphic_distinguished _ hE.singleTriangle_distinguished _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · simp [singleTrianglePlus, Functor.mapTriangle]
    rfl
  · simp [singleTrianglePlus, Functor.mapTriangle]
    rfl
  · simp only [Functor.mapTriangle, ObjectProperty.ι_obj, ObjectProperty.ι_map, Triangle.mk,
      singleTrianglePlus, ObjectProperty.homMk_hom, Category.assoc, Iso.inv_hom_id_app,
      Functor.comp_obj, Iso.refl_hom, Functor.map_id, Category.comp_id, singleTriangle_mor₃,
      Category.id_comp]
    exact Category.comp_id _

end

section ArbitraryZeroMorphisms

/-- The distinguished triangle of a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, written
with `CategoryTheory.Pretriangulated.Triangle.mk`, for an arbitrary `HasZeroMorphisms C`
instance:
```
X₁[0] --E.f--> X₂[0] --E.g--> X₃[0] --δ--> X₁[0][1]
```
-/
lemma exists_mk_singleTrianglePlus_distinguished [Z : Limits.HasZeroMorphisms C]
    {S : ShortComplex C} (hS : S.ShortExact) :
    ∃ δ : (DerivedCategory.Plus.singleFunctor C 0).obj S.X₃ ⟶
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧,
      Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map S.f)
        ((DerivedCategory.Plus.singleFunctor C 0).map S.g) δ ∈
          distTriang (DerivedCategory.Plus C) := by
  obtain rfl : Z = Preadditive.preadditiveHasZeroMorphisms := Subsingleton.elim _ _
  exact ⟨_, hS.singleTrianglePlus_distinguished⟩

/-- The image of a short exact sequence `S` under a functor `F : C ⥤ D` which factors as the
inclusion of `C` in degree `0` followed by a homological functor `G : D⁺(C) ⥤ D` is exact in
the middle: it is the image under `G` of the distinguished triangle of `S`. The zero
morphisms of `C` and of `D` are arbitrary instances. -/
-- The factorisation `hF` is an equality of functors, not an isomorphism, so that callers whose
-- `F` is definitionally `singleFunctor C 0 ⋙ G` can pass `rfl` and the kernel never has to
-- unfold `F`.
lemma map_exact_of_isHomological [Limits.HasZeroMorphisms C] {S : ShortComplex C}
    (hS : S.ShortExact) {D : Type*} [Category* D] [Abelian D] [Z : Limits.HasZeroMorphisms D]
    (G : DerivedCategory.Plus C ⥤ D) [G.IsHomological] (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : DerivedCategory.Plus.singleFunctor C 0 ⋙ G = F) :
    (S.map F).Exact := by
  obtain ⟨δ, hδ⟩ := hS.exists_mk_singleTrianglePlus_distinguished
  obtain rfl : Z = Preadditive.preadditiveHasZeroMorphisms := Subsingleton.elim _ _
  subst hF
  exact G.map_distinguished_exact _ hδ

end ArbitraryZeroMorphisms

end CategoryTheory.ShortComplex.ShortExact
