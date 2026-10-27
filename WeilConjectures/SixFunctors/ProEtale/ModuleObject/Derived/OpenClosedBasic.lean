/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion

/-!
# Open and closed immersions on derived categories of module objects over `Λ`

Let `Λ` be a commutative condensed ring, `i : Z ⟶ X` a closed immersion and `j : U ⟶ X` an open
immersion. This file proves the statements on `D(Mod_{Λ_X})` about open and closed immersions
that do not need the bounded constructible six functor formalism of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, so that they can
be used in its construction:

* the derived pushforward `Ri_*` is fully faithful, i.e. the counit `Li^* Ri_* ⟶ 𝟭` is an
  isomorphism
  (`ProEtale.CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion`);
* if `j` is quasi-compact and `i` is onto its complement, the derived restrictions `Lj^*` and
  `Li^*` jointly reflect isomorphisms
  (`ProEtale.CondensedRing.jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl`);
* `Lg^* (j_! K)` vanishes when the range of `g` misses the range of `j`
  (`ProEtale.CondensedRing.isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint`),
  and `Lj^* Rc_*` vanishes when the ranges of `j` and `c` are disjoint
  (`ProEtale.CondensedRing.isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint`);
* a complex `K` with `Lj^* K = 0` is supported on `Z`: the unit `K ⟶ Ri_* Li^* K` is an
  isomorphism
  (`ProEtale.CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero`);
* a complex whose restrictions to a quasi-compact open and to a closed complement are bounded
  constructible is bounded constructible
  (`ProEtale.CondensedRing.boundedConstructible_of_openClosed`);
* on a scheme with noetherian underlying space, `Ri_*` preserves bounded constructible complexes
  (`ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion`).

Since the pullbacks and the extension by zero are exact on module objects, the vanishing and
detection statements follow on homology objects from the sheaf-level statements of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed`, through the isomorphisms
`L(g^*) ≅ D(g^*)` (`ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`). The
pushforward `i_*` on module objects is fully faithful and preserves K-injective complexes, being
right adjoint to the exact functor `i^*`, so its right derived functor is fully faithful
(`CategoryTheory.Functor.full_rightDerivedFunctor`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section ClosedImmersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

instance : ((i)_*⟦Λ⟧).PreservesKInjectiveComplexes :=
  (upperStarLowerStarAdjunction Λ i).preservesKInjectiveComplexes

/-- The derived pushforward `Ri_*` along a closed immersion is fully faithful on module objects
over `Λ`: the counit `Li^* Ri_* ⟶ 𝟭` is an isomorphism. -/
instance isIso_derivedUpperStarLowerStarAdjunction_counit_of_isClosedImmersion :
    IsIso (derivedUpperStarLowerStarAdjunction Λ i).counit :=
  (derivedUpperStarLowerStarAdjunction Λ i).counit_isIso_of_R_fully_faithful

end ClosedImmersion

section Derived

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [QuasiCompact j]

/-- The derived restrictions `Lj^*` and `Li^*` to a quasi-compact open and its closed
complement jointly reflect isomorphisms of `D(Mod_{Λ_X})`. -/
theorem jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    JointlyReflectIsomorphisms (pairFunctor L((j)^*⟦Λ⟧) L((i)^*⟦Λ⟧)) :=
  (Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory _ _
    (jointlyReflectIsomorphisms_upperStar_of_isCompl Λ i j hij)).pairFunctor_of_iso
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm
    (leftDerivedUpperStarIsoMapDerivedCategory Λ i).symm

end Derived

/-- `Lg^* (j_! K)` vanishes in `D(Mod_{Λ_W})` when the range of `g : W ⟶ X` misses the range of
the open immersion `j : U ⟶ X`. -/
lemma isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint {U W X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : W ⟶ X)
    (hjg : Disjoint (Set.range j.base) (Set.range g.base))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) :
    IsZero (L((g)^*⟦Λ⟧).obj (D((j)_!open⟦Λ⟧).obj K)) :=
  (Functor.isZero_mapDerivedCategory_obj _ _ fun n ↦
    (isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint Λ j g hjg
      ((DerivedCategory.homologyFunctor _ n).obj K)).of_iso
      ((g)^*⟦Λ⟧.mapIso (((j)_!open⟦Λ⟧.mapDerivedCategoryHomologyFunctorIso n).symm.app
        K))).of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ g).app _)

omit [IsCommMonObj Λ] in
/-- A zero complex is bounded constructible. -/
lemma boundedConstructible_of_isZero {X : Scheme.{u}}
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (hK : IsZero K) : boundedConstructible (condensedRingObj Λ X) K :=
  (mem_boundedConstructible_iff _ _).2
    ⟨⟨0, 0, fun _ _ ↦ (DerivedCategory.homologyFunctor _ _).map_isZero hK⟩,
      fun _ ↦ ProEtale.isConstructibleModuleObject_of_isZero _
        ((DerivedCategory.homologyFunctor _ _).map_isZero hK)⟩

/-- **Open–closed locality of bounded constructibility**: for an open immersion `j` with
quasi-compact range and a closed immersion `i` onto its complement, a complex whose derived
restrictions along `j` and `i` are bounded constructible is bounded constructible. -/
theorem boundedConstructible_of_openClosed {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hj : boundedConstructible (condensedRingObj Λ U) ((L((j)^*⟦Λ⟧)).obj K))
    (hi : boundedConstructible (condensedRingObj Λ Z) ((L((i)^*⟦Λ⟧)).obj K)) :
    boundedConstructible (condensedRingObj Λ X) K := by
  have hc : IsCompl (Set.range i.base) (Set.range j.base) := by
    rw [hij]
    exact isCompl_compl.symm
  obtain ⟨⟨aj, bj, habj⟩, hcj⟩ := (mem_boundedConstructible_iff _ _).1 hj
  obtain ⟨⟨ai, bi, habi⟩, hci⟩ := (mem_boundedConstructible_iff _ _).1 hi
  refine (mem_boundedConstructible_iff _ _).2 ⟨⟨min aj ai, max bj bi, fun q hq ↦ ?_⟩,
    fun q ↦ ?_⟩
  · have hqi : q < ai ∨ bi < q := hq.imp (fun h ↦ lt_of_lt_of_le h (min_le_right _ _))
      (fun h ↦ lt_of_le_of_lt (le_max_right _ _) h)
    have hqj : q < aj ∨ bj < q := hq.imp (fun h ↦ lt_of_lt_of_le h (min_le_left _ _))
      (fun h ↦ lt_of_le_of_lt (le_max_left _ _) h)
    exact isZero_of_isZero_upperStar_of_isCompl Λ i j hc _
      ((habi q hqi).of_iso ((leftDerivedUpperStarHomologyIso Λ i q).app K))
      ((habj q hqj).of_iso ((leftDerivedUpperStarHomologyIso Λ j q).app K))
  · exact isConstructibleModuleObject_of_openClosed Λ j i hij _
      ((hcj q).of_iso ((leftDerivedUpperStarHomologyIso Λ j q).app K).symm)
      ((hci q).of_iso ((leftDerivedUpperStarHomologyIso Λ i q).app K).symm)

/-- `Lj^* Rc_*` vanishes when the ranges of the open immersion `j` and of the closed immersion `c`
are disjoint: a morphism `N ⟶ Lj^* Rc_* B` is a morphism `Lc^* j_! N ⟶ B`, and `Lc^* j_! = 0`. -/
lemma isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (c : Z ⟶ X)
    (hjc : Disjoint (Set.range j.base) (Set.range c.base))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    IsZero ((L((j)^*⟦Λ⟧)).obj ((R((c)_*⟦Λ⟧)).obj B)) := by
  have h : IsZero (D((j)^*⟦Λ⟧).obj ((R((c)_*⟦Λ⟧)).obj B)) := by
    rw [IsZero.iff_id_eq_zero]
    apply ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv _ _).symm.injective
    apply ((derivedUpperStarLowerStarAdjunction Λ c).homEquiv _ _).symm.injective
    exact (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint Λ j c hjc
      _).eq_of_src _ _
  exact h.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).app _)

/-- A complex whose restriction to the quasi-compact open `U` vanishes is supported on the closed
complement `Z`: the unit `K ⟶ Ri_* Li^* K` is an isomorphism. Its restriction to `Z` is an
isomorphism by the triangle identity, the counit being an isomorphism, and its restriction to `U`
is a morphism between zero objects. -/
theorem isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (hK : IsZero ((L((j)^*⟦Λ⟧)).obj K)) :
    IsIso ((derivedUpperStarLowerStarAdjunction Λ i).unit.app K) := by
  have hN : IsZero ((L((j)^*⟦Λ⟧)).obj ((R((i)_*⟦Λ⟧)).obj ((L((i)^*⟦Λ⟧)).obj K))) :=
    isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint Λ j i
      hij.symm.disjoint _
  have h₁ : IsIso ((L((j)^*⟦Λ⟧)).map ((derivedUpperStarLowerStarAdjunction Λ i).unit.app K)) :=
    isIso_of_source_target_iso_zero _ hK.isoZero hN.isoZero
  have h₂ : IsIso ((L((i)^*⟦Λ⟧)).map ((derivedUpperStarLowerStarAdjunction Λ i).unit.app K)) :=
    IsIso.of_isIso_fac_right (hh := IsIso.id _)
      ((derivedUpperStarLowerStarAdjunction Λ i).left_triangle_components K)
  exact (jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl Λ i j hij).isIso_of_pairFunctor
    _ h₁ h₂

/-- **Closed pushforward preserves bounded constructibility**: for a closed immersion
`c : Z ⟶ X` into a scheme with noetherian underlying space, `Rc_*` maps bounded constructible
complexes to bounded constructible complexes: `Lc^* Rc_* B ≅ B`, and the restriction of `Rc_* B`
to the open complement of `Z` vanishes. -/
theorem boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion {X Z : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (c : Z ⟶ X) [IsClosedImmersion c]
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))} (hB : boundedConstructible (condensedRingObj Λ Z) B) :
    boundedConstructible (condensedRingObj Λ X) ((R((c)_*⟦Λ⟧)).obj B) := by
  let U : X.Opens := ⟨(Set.range c.base)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact U.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hU : Set.range U.ι.base = (Set.range c.base)ᶜ := Scheme.Opens.range_ι U
  refine boundedConstructible_of_openClosed Λ U.ι c (by rw [hU, compl_compl]) _ ?_ ?_
  · exact boundedConstructible_of_isZero Λ
      (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint Λ U.ι c
        (by rw [hU]; exact disjoint_compl_left) B)
  · exact (boundedConstructible _).prop_of_iso
      (asIso ((derivedUpperStarLowerStarAdjunction Λ c).counit.app B)).symm hB

end AlgebraicGeometry.ProEtale.CondensedRing
