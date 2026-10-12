/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Localization

/-!
# The closed-support triangle and restriction to an open, before constructibility

Let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`, and let `Ri^!` be the
right adjoint of the direct image `Ri_*` on the unbounded derived categories of étale sheaves of
modules (`AlgebraicGeometry.Etale.derivedLowerStarClosedUpperShriekAdjunction`, blueprint
`lem-exc-closed-ambient`). This file records:

* the closed-support triangle `i_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶ (i_* Ri^! K)[1]` for every `K`
  (blueprint `lem-exc-closed-support-triangle`), deduced from the supported localization
  triangle `AlgebraicGeometry.Etale.existsUnique_distTriang_supportedLocalization` along
  `Ri_! ≅ Ri_*` and the uniqueness of right adjoints;
* for an open immersion `g`, the counit `Lg^* Rg_* ⟶ 𝟭` is an isomorphism, and
  `Lg^* Ri_* = 0` for a morphism `i` with range disjoint from that of `g` (blueprint
  `lem-exc-open-fully-faithful`).

No constructibility is used anywhere.

## Main statements

- `AlgebraicGeometry.Etale.exists_distTriang_closedSupport`
- `AlgebraicGeometry.Etale.isIso_derivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion`
- `AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_of_disjoint`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A distinguished triangle whose first morphism is the counit `F G K ⟶ K` of an adjunction
`F ⊣ G` gives one whose first morphism is the counit `F' G' K ⟶ K` of an adjunction `F' ⊣ G'`
with `F ≅ F'`, the other morphism being unchanged: the comparison of the right adjoints is
compatible with the counits (`CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit`). -/
lemma Triangle.exists_distTriang_of_counit_iso {F F' : D ⥤ C} {G G' : C ⥤ D} (adj : F ⊣ G)
    (adj' : F' ⊣ G') (e : F ≅ F') {K L : C} {v : K ⟶ L}
    {w : L ⟶ (F.obj (G.obj K))⟦(1 : ℤ)⟧} (hw : Triangle.mk (adj.counit.app K) v w ∈ distTriang C) :
    ∃ w', Triangle.mk (adj'.counit.app K) v w' ∈ distTriang C := by
  let adj'' := adj'.ofNatIsoLeft e.symm
  let φ := Adjunction.rightAdjointUniq adj adj''
  let iso₁ := F.mapIso (φ.app K) ≪≫ e.app _
  refine ⟨w ≫ iso₁.hom⟦(1 : ℤ)⟧', isomorphic_distinguished _ hw _ ?_⟩
  refine Triangle.isoMk _ _ iso₁.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · have h1 := Adjunction.rightAdjointUniq_hom_app_counit adj adj'' K
    have h2 : adj''.counit.app K = e.hom.app _ ≫ adj'.counit.app K := by simp [adj'']
    simp only [Triangle.mk_mor₁, Iso.refl_hom, Category.comp_id, iso₁,
      Iso.trans_symm, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv,
      Category.assoc]
    rw [← h1, h2, ← Functor.map_comp_assoc]
    simp [φ]
  · simp
  · simp [← Functor.map_comp]

end CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

namespace Etale

open Scheme

section OpenImmersion

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- Blueprint `lem-exc-open-fully-faithful`, first half: for an open immersion `g : V ⟶ T`, the
counit `Lg^* Rg_* ⟶ 𝟭` of the derived adjunction `Lg^* ⊣ Rg_*` on the unbounded derived
categories of étale sheaves is an isomorphism, i.e. `Lg^* Rg_* ≅ id`.

The levelwise pullback `D(g^*)` has the exact left adjoint `D(g_!)` with invertible unit
(`AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_unit`), so in
the adjoint triple `D(g_!) ⊣ D(g^*) ⊣ Rg_*` the counit of the second adjunction is invertible
too; and `Lg^* ≅ D(g^*)`. -/
instance isIso_derivedUpperStarLowerStarAdjunction_counit_of_isOpenImmersion {V T : Scheme.{u}}
    (g : V ⟶ T) [IsOpenImmersion g] : IsIso (derivedUpperStarLowerStarAdjunction A g).counit := by
  have : IsIso (mapDerivedUpperStarLowerStarAdjunction A g).counit :=
    (Adjunction.Triple.mk (derivedOpenImmersionLowerShriekUpperStarAdjunction A g)
      (mapDerivedUpperStarLowerStarAdjunction A g)).isIso_unit_iff_isIso_counit.1
      inferInstance
  have hff := (mapDerivedUpperStarLowerStarAdjunction A g).fullyFaithfulROfIsIsoCounit
  have := hff.full
  have := hff.faithful
  exact (derivedUpperStarLowerStarAdjunction A g).counit_isIso_of_R_fully_faithful

/-- Blueprint `lem-exc-open-fully-faithful`, first half, as an isomorphism of functors:
`Lg^* Rg_* ≅ 𝟭` for an open immersion `g`, the counit of `Lg^* ⊣ Rg_*`. -/
noncomputable def rightDerivedLowerStarCompLeftDerivedUpperStarIso {V T : Scheme.{u}}
    (g : V ⟶ T) [IsOpenImmersion g] : R((g)_*[A]) ⋙ L((g)^*[A]) ≅ 𝟭 _ :=
  asIso (derivedUpperStarLowerStarAdjunction A g).counit

/-- Blueprint `lem-exc-open-fully-faithful`, second half: `Lg^* Ri_* = 0` for an open immersion
`g` and a morphism `i` whose range is disjoint from that of `g`, for instance the closed
complement of `g`. At the sheaf level `g^* i_* = 0`
(`AlgebraicGeometry.Etale.isZero_upperStar_lowerStar_of_disjoint_range`), and this passes to
derived categories through K-injective resolutions
(`isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range`)
and `Lg^* ≅ D(g^*)`. -/
lemma isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_of_disjoint {V Z T : Scheme.{u}}
    (g : V ⟶ T) [IsOpenImmersion g] (i : Z ⟶ T)
    (hgi : Disjoint (Set.range g.base) (Set.range i.base))
    (N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    IsZero ((L((g)^*[A])).obj (R((i)_*[A]).obj N)) :=
  (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range A g i hgi
    N).of_iso ((leftDerivedUpperStarIsoMapDerivedCategory A g).app _)

end OpenImmersion

section Triangle

variable {R : Type (u + 1)} [CommRing R] {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  [HasCompactification i] (j : U ⟶ X) [IsOpenImmersion j]

/-- Blueprint `lem-exc-closed-support-triangle`: Closed-support triangle before restriction.

Let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`, and let `Ri^!` be the
right adjoint of the direct image `Ri_*` on the unbounded derived categories of étale sheaves of
modules (`AlgebraicGeometry.Etale.derivedLowerStarClosedUpperShriekAdjunction`, blueprint
`lem-exc-closed-ambient`). For every `K` the counit of `Ri_* ⊣ Ri^!` and the unit of
`Lj^* ⊣ Rj_*` extend to a distinguished triangle
```
  i_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶ (i_* Ri^! K)[1].
```
No constructibility is assumed of the values of the right adjoint.

Since `i` is proper, `Ri_! ≅ Ri_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`), so `Ri^!` is also
right adjoint to `Ri_!`, and the triangle is the supported localization triangle
(`AlgebraicGeometry.Etale.existsUnique_distTriang_supportedLocalization`) transported along the
comparison of the two right adjoints, which is compatible with the counits. -/
theorem exists_distTriang_closedSupport (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    ∃ w, Triangle.mk ((derivedLowerStarClosedUpperShriekAdjunction i j hij).counit.app K)
      ((derivedUpperStarLowerStarAdjunction _ j).unit.app K) w ∈ distTriang _ := by
  have : (R(i)_![ModuleCat.{u + 1} R]).IsLeftAdjoint :=
    ((derivedLowerStarClosedUpperShriekAdjunction i j hij).ofNatIsoLeft
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} R) i).symm).isLeftAdjoint
  obtain ⟨w, hw, -⟩ := existsUnique_distTriang_supportedLocalization _ i j hij K
  exact Pretriangulated.Triangle.exists_distTriang_of_counit_iso (rightDerivedUpperShriekAdjunction _ i)
    (derivedLowerStarClosedUpperShriekAdjunction i j hij)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} R) i) hw

end Triangle

end Etale

end AlgebraicGeometry
