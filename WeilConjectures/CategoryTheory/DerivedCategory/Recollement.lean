/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Derived inputs of the open–closed triangle

This file collects the facts about functors induced on unbounded derived categories which are
used to apply the abstract open–closed triangle
`CategoryTheory.Pretriangulated.exists_distTriang_recollement` to derived categories of sheaves.

## Main results

- `CategoryTheory.Adjunction.mapDerivedCategoryAdjunctionOfKInjective`: for an adjunction
  `f ⊣ g` of exact functors, `D(f) ⊣ D(g)`, built from K-injective resolutions only (unlike
  `CategoryTheory.Adjunction.mapDerivedCategoryAdjunction`, which also needs K-flat
  resolutions).
- `CategoryTheory.Adjunction.isIso_unit_of_mapDerivedCategory`: for any adjunction
  `D(f) ⊣ D(g)` between the induced functors of exact `f ⊣ g` whose unit is invertible, the
  unit is invertible.
- `CategoryTheory.Functor.isZero_mapDerivedCategory_obj_mapDerivedCategory_obj`: if `G ∘ F = 0`
  for exact `F`, `G`, then `D(G) ∘ D(F) = 0`.
- `CategoryTheory.Functor.isZero_mapDerivedCategory_obj_rightDerivedFunctor_obj`: if `F ∘ G = 0`
  for exact `F`, then `D(F) ∘ RG = 0`.
-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CategoryTheory

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

namespace Adjunction

variable {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

/-- The levelwise derived adjunction `D(f) ⊣ D(g)` of an adjunction `f ⊣ g` of exact functors,
obtained from `CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction` and the
identification of the total right derived functor of the exact `g` with `D(g)`. It only uses
K-injective resolutions on the target of `f`. -/
noncomputable def mapDerivedCategoryAdjunctionOfKInjective [HasKInjectiveResolutions D]
    (adj : f ⊣ g) : f.mapDerivedCategory ⊣ g.mapDerivedCategory :=
  adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    g.rightDerivedFunctorIsoMapDerivedCategory

/-- If the unit of `f ⊣ g` is an isomorphism, `f` and `g` being exact, then so is the unit of any
adjunction `D(f) ⊣ D(g)`: since `D(f) ⋙ D(g) ≅ D(f ⋙ g) ≅ 𝟭`, the functor `D(f)` is fully
faithful. -/
lemma isIso_unit_of_mapDerivedCategory (adj : f ⊣ g) [IsIso adj.unit]
    (adj' : f.mapDerivedCategory ⊣ g.mapDerivedCategory) : IsIso adj'.unit := by
  have h := adj'.fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryCompIso f g).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso adj.unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso C)
  have := h.full
  have := h.faithful
  infer_instance

end Adjunction

namespace Functor

/-- If `G ∘ F` vanishes on objects, for exact functors `F` and `G`, then so does
`D(G) ∘ D(F)`: the homology objects of `D(F) K` are the `F (H^n K)`. -/
lemma isZero_mapDerivedCategory_obj_mapDerivedCategory_obj (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (hGF : ∀ X, IsZero (G.obj (F.obj X))) (K : DerivedCategory C) :
    IsZero (G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K)) :=
  G.isZero_mapDerivedCategory_obj _ fun n ↦
    (hGF _).of_iso (G.mapIso ((F.mapDerivedCategoryHomologyFunctorIso n).symm.app K))

/-- If `F ∘ G` vanishes on objects, for an exact functor `F`, then `D(F) ∘ RG` vanishes:
representing an object by a K-injective complex `I`, `RG` of it is `G I`, which `F` kills
termwise. -/
lemma isZero_mapDerivedCategory_obj_rightDerivedFunctor_obj [HasKInjectiveResolutions C]
    (G : C ⥤ D) (F : D ⥤ E) [G.Additive]
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hFG : ∀ X, IsZero (F.obj (G.obj X))) (N : DerivedCategory C) :
    IsZero (F.mapDerivedCategory.obj (G.rightDerivedFunctor.obj N)) := by
  obtain ⟨I, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective N
  have hC : IsZero (((G ⋙ F).mapHomologicalComplex _).obj I) := by
    rw [IsZero.iff_id_eq_zero]
    exact HomologicalComplex.hom_ext _ _ fun n ↦ (hFG (I.X n)).eq_of_src _ _
  exact (DerivedCategory.Q.map_isZero hC).of_iso
    (F.mapDerivedCategory.mapIso (G.rightDerivedFunctor.mapIso e ≪≫
      G.rightDerivedFunctorObjQIso I) ≪≫ F.mapDerivedCategoryFactors.app _)

end Functor

end CategoryTheory
