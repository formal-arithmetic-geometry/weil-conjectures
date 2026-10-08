/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Complement
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.FullyFaithful

/-!
# The closed-support triangle on the pro-étale site

Let `i : Z ⟶ T` be a closed immersion with complementary open immersion `j : U ⟶ T`, and let
`Λ` be a finite ring. For any right adjoint `Ri^!` of the derived direct image `Ri_*` on the
unbounded derived categories of pro-étale sheaves of `Λ`-modules, the counit of `Ri_* ⊣ Ri^!`
and the unit of `Lj^* ⊣ Rj_*` extend to a distinguished triangle

`Ri_* Ri^! K ⟶ K ⟶ Rj_* Lj^* K ⟶ (Ri_* Ri^! K)[1]`.

No constructibility is involved. The triangle is
`CategoryTheory.Adjunction.exists_distTriang_counit_unit`, fed with the following sheaf-level
facts about closed immersions on the pro-étale site:

- `j^* i_* = 0` (`AlgebraicGeometry.ProEtale.isZero_openImmersionRestriction_lowerStar`), hence
  `i^* j_! = 0` and `D(j^*) Ri_* = 0`;
- `i_*` is exact and `i^* i_* ≅ 𝟭`, hence `Ri_*` is fully faithful;
- a sheaf killed by `j^*` and `i^*` is zero.

## Main statements

- `AlgebraicGeometry.ProEtale.fullyFaithfulRightDerivedLowerStar`: `Ri_*` is fully faithful.
- `AlgebraicGeometry.ProEtale.isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar`:
  `D(j^*) Ri_* = 0`.
- `AlgebraicGeometry.ProEtale.exists_distTriang_counit_derivedUpperStarLowerStarAdjunction_unit`:
  the closed-support triangle (blueprint `lem-exc-proetale-support-triangle`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] {U Z T : Scheme.{u}}
  (j : U ⟶ T) (i : Z ⟶ T) [IsOpenImmersion j] [IsClosedImmersion i]

/-! ### Sheaf-level input -/

/-- Blueprint `lem-exc-open-closed-detection`: Detection by the open and the closed restriction

Let `i : Z ⟶ T` be a closed immersion with quasi-compact complementary open immersion
`j : U ⟶ T`. A pro-étale sheaf `F` of modules over the finite ring `Λ` with `j^* F = 0` and
`i^* F = 0` is zero. -/
theorem isZero_of_isZero_upperStar [Finite Λ] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)}
    (hj : IsZero ((j)^*[ModuleCat.{u + 1} Λ].obj F))
    (hi : IsZero ((i)^*[ModuleCat.{u + 1} Λ].obj F)) : IsZero F :=
  sorry

/-- Blueprint `lem-exc-proetale-closed-exact`: Exactness of closed direct image

Let `i : Z ⟶ T` be a closed immersion with quasi-compact complementary open immersion
`j : U ⟶ T`. Then the direct image `i_*` of pro-étale sheaves of modules over the finite ring
`Λ` is exact. -/
theorem preservesFiniteColimits_lowerStar_of_isClosedImmersion [Finite Λ] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    PreservesFiniteColimits (i)_*[ModuleCat.{u + 1} Λ] :=
  sorry

/-- Blueprint `lem-exc-proetale-closed-fully-faithful`: Full faithfulness of closed direct image

For a closed immersion `i`, the counit `i^* i_* G ⟶ G` is an isomorphism on all pro-étale
sheaves of modules over the finite ring `Λ`; thus `i_*` is fully faithful. -/
theorem isIso_upperStarLowerStarAdjunction_counit_of_isClosedImmersion [Finite Λ] :
    IsIso (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit :=
  sorry

/-- `i^* j_! F = 0` for an open immersion `j` and a morphism `i` with disjoint ranges: by
`j_! ⊣ j^*` and `i^* ⊣ i_*`, `Hom(i^* j_! F, H) ≅ Hom(F, j^* i_* H)`, and `j^* i_* H = 0`
(`AlgebraicGeometry.ProEtale.isZero_openImmersionRestriction_lowerStar`). -/
lemma isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint_range {Z' : Scheme.{u}}
    (g : Z' ⟶ T) (hgj : Set.range g.base ∩ Set.range j.base = ∅)
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ)) :
    IsZero ((g)^*[ModuleCat.{u + 1} Λ].obj ((j)_!open[ModuleCat.{u + 1} Λ].obj F)) := by
  rw [IsZero.iff_id_eq_zero]
  have hz := isZero_openImmersionRestriction_lowerStar (ModuleCat.{u + 1} Λ) g j hgj
  have : Subsingleton ((g)^*[ModuleCat.{u + 1} Λ].obj ((j)_!open[ModuleCat.{u + 1} Λ].obj F) ⟶
      (g)^*[ModuleCat.{u + 1} Λ].obj ((j)_!open[ModuleCat.{u + 1} Λ].obj F)) :=
    (((upperStarLowerStarAdjunction _ g).homEquiv _ _).trans
      ((openImmersionLowerShriekAdjunction _ j).homEquiv _ _)).subsingleton_congr.2
      ⟨(hz _).eq_of_tgt⟩
  exact Subsingleton.elim _ _

/-! ### Derived consequences -/

/-- The adjunction `D(g^*) ⊣ Rg_*` on unbounded derived categories of pro-étale sheaves:
`AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction` transported along
`Lg^* ≅ D(g^*)`. -/
noncomputable def mapDerivedUpperStarLowerStarAdjunction {Y : Scheme.{u}} (g : Y ⟶ T) :
    D((g)^*[ModuleCat.{u + 1} Λ]) ⊣ R((g)_*[ModuleCat.{u + 1} Λ]) :=
  (derivedUpperStarLowerStarAdjunction _ g).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory _ g)

/-- For an open immersion `j`, the counit `D(j^*) Rj_* ⟶ 𝟭` is an isomorphism:
`D(j_!) ⊣ D(j^*) ⊣ Rj_*` is an adjoint triple whose first unit is invertible, since `j_!` is
fully faithful (`AlgebraicGeometry.ProEtale.fullyFaithfulOpenImmersionLowerShriek`). -/
instance isIso_mapDerivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion :
    IsIso (mapDerivedUpperStarLowerStarAdjunction Λ j).counit :=
  have : IsIso (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).unit :=
    (openImmersionLowerShriekUpperStarAdjunction _ j).unit_isIso_of_L_fully_faithful
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
  (Adjunction.Triple.isIso_unit_iff_isIso_counit
    ⟨derivedOpenImmersionLowerShriekUpperStarAdjunction _ j,
      mapDerivedUpperStarLowerStarAdjunction Λ j⟩).1 inferInstance

/-- `D(j^*) Rg_* = 0` for an open immersion `j` and a morphism `g` with disjoint ranges:
`Hom(N, D(j^*) Rg_* B) ≅ Hom(D(j_!) N, Rg_* B) ≅ Hom(D(g^*) D(j_!) N, B)`, and
`D(g^*) D(j_!) N = 0` because `g^* j_! = 0` on sheaves
(`AlgebraicGeometry.ProEtale.isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint_range`).
-/
theorem isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar {Z' : Scheme.{u}}
    (g : Z' ⟶ T) (hgj : Set.range g.base ∩ Set.range j.base = ∅)
    (B : DerivedCategory (Sheaf (Scheme.ProEt.topology Z') (ModuleCat.{u + 1} Λ))) :
    IsZero (D((j)^*[ModuleCat.{u + 1} Λ]).obj ((R((g)_*[ModuleCat.{u + 1} Λ])).obj B)) := by
  set M := D((j)^*[ModuleCat.{u + 1} Λ]).obj ((R((g)_*[ModuleCat.{u + 1} Λ])).obj B)
  have h₀ : IsZero (D((g)^*[ModuleCat.{u + 1} Λ]).obj (D((j)_!open[ModuleCat.{u + 1} Λ]).obj M)) :=
    Functor.isZero_mapDerivedCategory_obj _ _ fun n ↦
      (isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint_range Λ j g hgj
        ((DerivedCategory.homologyFunctor _ n).obj M)).of_iso
        ((g)^*[ModuleCat.{u + 1} Λ].mapIso
          (((j)_!open[ModuleCat.{u + 1} Λ].mapDerivedCategoryHomologyFunctorIso n).symm.app M))
  rw [IsZero.iff_id_eq_zero]
  have : Subsingleton (M ⟶ M) :=
    (((derivedOpenImmersionLowerShriekUpperStarAdjunction _ j).homEquiv _ _).symm.trans
      ((mapDerivedUpperStarLowerStarAdjunction Λ g).homEquiv _ _).symm).subsingleton_congr.2
      ⟨h₀.eq_of_src⟩
  exact Subsingleton.elim _ _

/-- **`Ri_*` is fully faithful** for a closed immersion `i` with quasi-compact complementary
open: as `i_*` is exact, `Ri_*` is `D(i_*)`, and the counit of `D(i^*) ⊣ D(i_*)` is induced by
the invertible counit `i^* i_* ⟶ 𝟭`
(`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit_of_isClosedImmersion`). -/
noncomputable def fullyFaithfulRightDerivedLowerStar [Finite Λ] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    (R((i)_*[ModuleCat.{u + 1} Λ])).FullyFaithful :=
  have := preservesFiniteColimits_lowerStar_of_isClosedImmersion Λ j i hij
  have := isIso_upperStarLowerStarAdjunction_counit_of_isClosedImmersion Λ i
  have : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryAdjunction
      ).counit := inferInstance
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryAdjunction
    ).fullyFaithfulROfIsIsoCounit.ofIso
    ((i)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorIsoMapDerivedCategory).symm

/-- **Derived open–closed detection**: an object `E` with `D(j^*) E = 0` and `D(i^*) E = 0` is
zero, on homology sheaves by `AlgebraicGeometry.ProEtale.isZero_of_isZero_upperStar`. -/
theorem isZero_of_isZero_mapDerivedCategoryUpperStar [Finite Λ] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {E : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))}
    (hj : IsZero (D((j)^*[ModuleCat.{u + 1} Λ]).obj E))
    (hi : IsZero (D((i)^*[ModuleCat.{u + 1} Λ]).obj E)) : IsZero E :=
  (DerivedCategory.isZero_iff _).2 fun n ↦ isZero_of_isZero_upperStar Λ j i hij
    (((DerivedCategory.isZero_iff _).1 hj n).of_iso
      (((j)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryHomologyFunctorIso n).app E))
    (((DerivedCategory.isZero_iff _).1 hi n).of_iso
      (((i)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryHomologyFunctorIso n).app E))

/-- Blueprint `lem-exc-proetale-support-triangle`: Pro-etale closed-support triangle before
constructible restriction

Let `T` be Noetherian, `i : Z ⟶ T` a closed immersion with complementary open immersion
`j : U ⟶ T`, and `Λ` a finite ring. For any right adjoint `G` of the derived direct image
`Ri_*` on the unbounded derived categories of pro-étale sheaves of `Λ`-modules (such as the
exceptional inverse image `Ri^!`), and every `K`, the counit of `Ri_* ⊣ G` and the unit of
`Lj^* ⊣ Rj_*` extend to a distinguished triangle

```
  Ri_* G K --ε_K--> K --η_K--> Rj_* Lj^* K --w--> (Ri_* G K)[1].
```

This is `CategoryTheory.Adjunction.exists_distTriang_counit_unit`: `Ri_*` is fully faithful
(`AlgebraicGeometry.ProEtale.fullyFaithfulRightDerivedLowerStar`), `D(j^*) Ri_* = 0`, the
counit of `D(j^*) ⊣ Rj_*` is invertible, and `D(j^*)` and `G` jointly detect zero objects
(`CategoryTheory.Adjunction.isZero_of_isZero_rightAdjoint` and
`AlgebraicGeometry.ProEtale.isZero_of_isZero_mapDerivedCategoryUpperStar`). The unit of
`D(j^*) ⊣ Rj_*` is then replaced by that of `Lj^* ⊣ Rj_*`. -/
theorem exists_distTriang_counit_derivedUpperStarLowerStarAdjunction_unit [Finite Λ]
    [IsNoetherian T]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {G : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))}
    (adj : R((i)_*[ModuleCat.{u + 1} Λ]) ⊣ G)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))) :
    ∃ w, Triangle.mk (adj.counit.app K)
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app K) w ∈
        distTriang _ := by
  have hff := fullyFaithfulRightDerivedLowerStar Λ j i hij
  have := hff.full
  have := hff.faithful
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  have : IsIso (mapDerivedUpperStarLowerStarAdjunction Λ i).counit :=
    (mapDerivedUpperStarLowerStarAdjunction Λ i).counit_isIso_of_R_fully_faithful
  have hji : ∀ B, IsZero (D((j)^*[ModuleCat.{u + 1} Λ]).obj
      ((R((i)_*[ModuleCat.{u + 1} Λ])).obj B)) :=
    isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar Λ j i
      (by rw [hij, Set.compl_inter_self])
  obtain ⟨w, hw⟩ := adj.exists_distTriang_counit_unit
    (mapDerivedUpperStarLowerStarAdjunction Λ j) hji
    (fun _ hj hi ↦ adj.isZero_of_isZero_rightAdjoint (mapDerivedUpperStarLowerStarAdjunction Λ i)
      hji (fun _ hj hi ↦ isZero_of_isZero_mapDerivedCategoryUpperStar Λ j i hij hj hi) hj hi) K
  -- Replace the unit of `D(j^*) ⊣ Rj_*` by that of `Lj^* ⊣ Rj_*`.
  let e := Adjunction.leftAdjointUniq (derivedUpperStarLowerStarAdjunction _ j)
    (mapDerivedUpperStarLowerStarAdjunction Λ j)
  refine ⟨(R((j)_*[ModuleCat.{u + 1} Λ])).map (e.hom.app K) ≫ w,
    isomorphic_distinguished _ hw _ ?_⟩
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((R((j)_*[ModuleCat.{u + 1} Λ])).mapIso (e.app K)) (by simp) (by simp [e]) (by simp)

end ProEtale

end AlgebraicGeometry
