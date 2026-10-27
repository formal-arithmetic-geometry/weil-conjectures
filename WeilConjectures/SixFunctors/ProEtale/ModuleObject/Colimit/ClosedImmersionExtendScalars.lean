/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleOpenCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomologyCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.ClosedImmersion

/-!
# Closed pushforward and extension of scalars

Let `Λ` be a commutative condensed ring, `i : Z ⟶ X` a closed immersion and `j : U ⟶ X` a
quasi-compact open immersion onto its complement. This file proves, without the bounded
constructible six functor formalism of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` (which depends
on the present file through the descent of constructible complexes):

* a complex `K ∈ D(Mod_{Λ_X})` with `Lj^* K = 0` is supported on `Z`: the unit
  `K ⟶ Ri_* Li^* K` is an isomorphism
  (`ProEtale.CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero`);
* `Ri_*` preserves bounded constructible complexes on a scheme with noetherian underlying space
  (`ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj_of_isClosedImmersion`);
* for a flat coefficient change `a : Λ ⟶ Λ'`, the extension of scalars commutes with `Ri_*`:
  `T^X (Ri_* N) ≅ Ri_* (T^Z N)`
  (`ProEtale.CondensedRing.derivedExtendScalarsLowerStarIsoOfIsClosedImmersion`), since
  `Lj^* T^X (Ri_* N) ≅ T^U (Lj^* Ri_* N) = 0` by (Pull).

Some of the intermediate statements are primed versions of statements of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion` and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward`,
which import `Derived.BoundedConstructible`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The counit `Li^* Ri_* ⟶ 𝟭` of the derived adjunction along a closed immersion is an
isomorphism: `i_*` is fully faithful and preserves K-injective complexes. -/
lemma isIso_derivedUpperStarLowerStarAdjunction_counit_app_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    IsIso ((derivedUpperStarLowerStarAdjunction Λ i).counit.app B) := by
  have : ((i)_*⟦Λ⟧).PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction Λ i).preservesKInjectiveComplexes
  have := (derivedUpperStarLowerStarAdjunction Λ i).counit_isIso_of_R_fully_faithful
  infer_instance

/-- The derived restrictions `Lj^*` and `Li^*` to a quasi-compact open and its closed
complement jointly reflect isomorphisms of `D(Mod_{Λ_X})`. -/
theorem jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl' {Z U X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    JointlyReflectIsomorphisms (pairFunctor L((j)^*⟦Λ⟧) L((i)^*⟦Λ⟧)) :=
  (Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory _ _
    (jointlyReflectIsomorphisms_upperStar_of_isCompl Λ i j hij)).pairFunctor_of_iso
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm
    (leftDerivedUpperStarIsoMapDerivedCategory Λ i).symm

/-- `Lg^* (j_! K)` vanishes when the range of `g` misses the range of the open immersion
`j`. -/
lemma isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint' {U W X : Scheme.{u}}
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

/-- `Lj^* Rc_*` vanishes when the ranges of the open immersion `j` and of `c` are disjoint: a
morphism `N ⟶ Lj^* Rc_* B` is a morphism `Lc^* j_! N ⟶ B`, and `Lc^* j_! = 0`. -/
lemma isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint' {X U Z : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (c : Z ⟶ X)
    (hjc : Disjoint (Set.range j.base) (Set.range c.base))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    IsZero ((L((j)^*⟦Λ⟧)).obj ((R((c)_*⟦Λ⟧)).obj B)) := by
  have h : IsZero (D((j)^*⟦Λ⟧).obj ((R((c)_*⟦Λ⟧)).obj B)) := by
    rw [IsZero.iff_id_eq_zero]
    apply ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv _ _).symm.injective
    apply ((derivedUpperStarLowerStarAdjunction Λ c).homEquiv _ _).symm.injective
    exact (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint' Λ j c hjc
      _).eq_of_src _ _
  exact h.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).app _)

/-- A complex `K` whose restriction to the quasi-compact open complement `U` of a closed
immersion `i : Z ⟶ X` vanishes is supported on `Z`: the unit `K ⟶ Ri_* Li^* K` is an
isomorphism. Its restriction to `Z` is an isomorphism by the triangle identity, the counit
being an isomorphism, and its restriction to `U` is a morphism between zero objects. -/
lemma isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero {Z U X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hK : IsZero ((L((j)^*⟦Λ⟧)).obj K)) :
    IsIso ((derivedUpperStarLowerStarAdjunction Λ i).unit.app K) := by
  refine (jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl' Λ i j
    hij).isIso_of_pairFunctor
    _ ?_ ?_
  · exact isIso_of_source_target_iso_zero _ (hK.iso (isZero_zero _))
      ((isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint' Λ j i
        hij.symm.disjoint _).iso (isZero_zero _))
  · have := isIso_derivedUpperStarLowerStarAdjunction_counit_app_of_isClosedImmersion Λ i
      ((L((i)^*⟦Λ⟧)).obj K)
    have h := (derivedUpperStarLowerStarAdjunction Λ i).left_triangle_components K
    have : IsIso ((L((i)^*⟦Λ⟧)).map ((derivedUpperStarLowerStarAdjunction Λ i).unit.app K) ≫
        (derivedUpperStarLowerStarAdjunction Λ i).counit.app ((L((i)^*⟦Λ⟧)).obj K)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _
      ((derivedUpperStarLowerStarAdjunction Λ i).counit.app ((L((i)^*⟦Λ⟧)).obj K))

/-- **Open–closed locality of bounded constructibility**: for an open immersion `j` with
quasi-compact range and a closed immersion `i` onto its complement, a complex whose derived
restrictions along `j` and `i` are bounded constructible is bounded constructible. -/
theorem boundedConstructible_of_openClosed' {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
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

omit [IsCommMonObj Λ] in
/-- A zero complex is bounded constructible. -/
lemma boundedConstructible_of_isZero' {X : Scheme.{u}}
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (hK : IsZero K) : boundedConstructible (condensedRingObj Λ X) K :=
  (mem_boundedConstructible_iff _ _).2
    ⟨⟨0, 0, fun _ _ ↦ (DerivedCategory.homologyFunctor _ _).map_isZero hK⟩,
      fun _ ↦ ProEtale.isConstructibleModuleObject_of_isZero _
        ((DerivedCategory.homologyFunctor _ _).map_isZero hK)⟩

/-- **Closed pushforward preserves bounded constructibility**: for a closed immersion
`c : Z ⟶ X` into a scheme with noetherian underlying space, `Rc_*` maps bounded constructible
complexes to bounded constructible complexes. -/
theorem boundedConstructible_rightDerivedLowerStar_obj_of_isClosedImmersion {X Z : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (c : Z ⟶ X) [IsClosedImmersion c]
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))} (hB : boundedConstructible (condensedRingObj Λ Z) B) :
    boundedConstructible (condensedRingObj Λ X) ((R((c)_*⟦Λ⟧)).obj B) := by
  let U : X.Opens := ⟨(Set.range c.base)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have : TopologicalSpace.NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact U.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hU : Set.range U.ι.base = (Set.range c.base)ᶜ := Scheme.Opens.range_ι U
  have := isIso_derivedUpperStarLowerStarAdjunction_counit_app_of_isClosedImmersion Λ c B
  refine boundedConstructible_of_openClosed' Λ U.ι c (by rw [hU, compl_compl]) _ ?_ ?_
  · refine boundedConstructible_of_isZero' Λ
      (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint' Λ U.ι c ?_ B)
    rw [hU]
    exact disjoint_compl_left
  · exact (boundedConstructible _).prop_of_iso
      (asIso ((derivedUpperStarLowerStarAdjunction Λ c).counit.app B)).symm hB

/-- The derived extension of scalars along a flat coefficient change preserves zero objects,
being isomorphic to the levelwise functor. -/
lemma isZero_leftDerivedExtendScalars_obj
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X : Scheme.{u}}
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (hK : IsZero K) :
    IsZero ((L(Mod.extendScalars (coefficientMap a X))).obj K) :=
  (Functor.map_isZero (Mod.extendScalars (coefficientMap a X)).mapDerivedCategory hK).of_iso
    ((Functor.leftDerivedFunctorIsoMapDerivedCategory _).app K)

set_option maxHeartbeats 800000 in
-- Unifying the instance arguments of the derived extensions of scalars appearing in (Pull) with
-- those of the statement is slow.
/-- For a flat coefficient change `a : Λ ⟶ Λ'` and a closed immersion `i : Z ⟶ X` with
quasi-compact open complement (e.g. `X` with noetherian underlying space), the extension of
scalars commutes with the derived pushforward: `T^X (Ri_* N) ≅ Ri_* (T^Z N)`. The complex
`T^X (Ri_* N)` restricts to `T^U (Lj^* Ri_* N) = 0` on the complement by (Pull), so it is
`Ri_* Li^* T^X (Ri_* N) ≅ Ri_* T^Z (Li^* Ri_* N) ≅ Ri_* T^Z N`. -/
noncomputable def derivedExtendScalarsLowerStarIsoOfIsClosedImmersion
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
    {Z X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X] (i : Z ⟶ X) [IsClosedImmersion i]
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (L(Mod.extendScalars (coefficientMap a X))).obj ((R((i)_*⟦Λ⟧)).obj N) ≅
      (R((i)_*⟦Λ'⟧)).obj ((L(Mod.extendScalars (coefficientMap a Z))).obj N) :=
  let U : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  haveI : TopologicalSpace.NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  haveI : QuasiCompact U.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hc : IsCompl (Set.range i.base) (Set.range U.ι.base) := by
    rw [Scheme.Opens.range_ι U]
    exact isCompl_compl
  let M := (R((i)_*⟦Λ⟧)).obj N
  let TM := (L(Mod.extendScalars (coefficientMap a X))).obj M
  have h0 : IsZero ((L((U.ι)^*⟦Λ'⟧)).obj TM) :=
    (isZero_leftDerivedExtendScalars_obj Λ a
      (isZero_leftDerivedUpperStar_obj_rightDerivedLowerStar_obj_of_disjoint'
        Λ U.ι i hc.symm.disjoint N)).of_iso ((derivedPullIso a U.ι).app M).symm
  have hη := isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero Λ' i U.ι hc TM h0
  have hε := isIso_derivedUpperStarLowerStarAdjunction_counit_app_of_isClosedImmersion Λ i N
  (@asIso _ _ _ _ ((derivedUpperStarLowerStarAdjunction Λ' i).unit.app TM) hη).trans
    ((R((i)_*⟦Λ'⟧)).mapIso (((derivedPullIso a i).app M).symm.trans
      ((L(Mod.extendScalars (coefficientMap a Z))).mapIso
        (@asIso _ _ _ _ ((derivedUpperStarLowerStarAdjunction Λ i).counit.app N)
        hε))))

end AlgebraicGeometry.ProEtale.CondensedRing
