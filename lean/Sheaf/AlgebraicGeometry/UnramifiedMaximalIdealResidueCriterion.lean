/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.Separable

import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.Morphisms.FormallyUnramifiedStalkNeighbourhood

/-! # The maximal-ideal and residue-field criterion for unramifiedness at a point

Source: Stacks Project, Morphisms, Tag 02GF, equivalence (1) with (6)
(blueprint: lem-trf-unramified-maximal-ideal-residue-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- A locally finite type morphism is unramified on a neighbourhood of a point exactly when
its actual stalk map extends the target maximal ideal to the source maximal ideal and its
induced residue-field extension is finite separable algebraic.

Source: Stacks Project, Morphisms, Tag 02GF, equivalence (1) with (6).
(blueprint: lem-trf-unramified-maximal-ideal-residue-criterion).

Proof:
1. Given an unramified open neighbourhood, apply
   lem-weil-pbc-unramified-formally-unramified to its restricted morphism. Formal
   unramifiedness passes to its actual stalk map. Identify the stalks of the open subscheme
   with those of X and apply lem-trf-stalk-formally-unramified-maximal-residue-criterion.
   This gives the asserted maximal-ideal equality and finite separable residue extension.
2. Conversely, apply lem-trf-stalk-formally-unramified-maximal-residue-criterion to the
   actual stalk map. Then lem-sbc-formally-unramified-stalk-neighbourhood gives an open
   neighbourhood on which the morphism is formally unramified. Its restriction is locally
   of finite type, since open immersions and compositions preserve local finite type.
   Apply lem-weil-pbc-lft-formally-unramified-unramified to obtain unramifiedness there. -/
theorem unramified_neighbourhood_iff_maximalIdeal_residue
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    (∃ V : X.Opens, x ∈ V ∧ IsUnramified (V.ι ≫ f)) ↔
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))).map (f.stalkMap x).hom =
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
        (f.residueFieldMap x).hom.Finite ∧
        @Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) _ _
          (f.residueFieldMap x).hom.toAlgebra := by
  have hn : (∃ V : X.Opens, x ∈ V ∧ IsUnramified (V.ι ≫ f)) ↔
      (f.stalkMap x).hom.FormallyUnramified := by
    constructor
    · rintro ⟨V, hx, hV⟩
      have := hV.2
      have : FormallyUnramified (V.ι ≫ f) := inferInstance
      let y : V := ⟨x, hx⟩
      have h := FormallyUnramified.stalkMap (V.ι ≫ f) y
      rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at h
      have h' := h.comp (RingHom.FormallyUnramified.of_surjective
        (ConcreteCategory.bijective_of_isIso (V.stalkIso y).hom).2)
      change ((f.stalkMap x ≫ V.ι.stalkMap y) ≫
        (V.stalkIso y).hom).hom.FormallyUnramified at h'
      rw [Category.assoc, ← Scheme.Opens.stalkIso_inv,
        Iso.inv_hom_id, Category.comp_id] at h'
      exact h'
    · intro h
      obtain ⟨V, hx, hV⟩ := FormallyUnramified.exists_neighbourhood_of_stalkMap f x h
      have := hV
      exact ⟨V, hx, inferInstance, inferInstance⟩
  rw [hn]
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Algebra.EssFiniteType (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap f x
  have e : (f.residueFieldMap x).hom.toAlgebra =
      (inferInstance : Algebra (IsLocalRing.ResidueField (S.presheaf.stalk (f x)))
        (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
    refine Algebra.algebra_ext _ _ fun r ↦ ?_
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    rfl
  change Algebra.FormallyUnramified (S.presheaf.stalk (f x)) (X.presheaf.stalk x) ↔ _
  constructor
  · intro h
    have := h
    refine ⟨Algebra.FormallyUnramified.map_maximalIdeal, ?_, ?_⟩
    · change @Module.Finite _ _ _ _ (f.residueFieldMap x).hom.toAlgebra.toModule
      rw [e]
      exact inferInstanceAs <| Module.Finite
        (IsLocalRing.ResidueField (S.presheaf.stalk (f x)))
        (IsLocalRing.ResidueField (X.presheaf.stalk x))
    · rw [e]
      exact inferInstanceAs <| Algebra.IsSeparable
        (IsLocalRing.ResidueField (S.presheaf.stalk (f x)))
        (IsLocalRing.ResidueField (X.presheaf.stalk x))
  · rintro ⟨hm, _, hs⟩
    rw [e] at hs
    have : Algebra.IsSeparable
        (IsLocalRing.ResidueField (S.presheaf.stalk (f x)))
        (IsLocalRing.ResidueField (X.presheaf.stalk x)) := hs
    exact Algebra.FormallyUnramified.of_map_maximalIdeal hm

end AlgebraicGeometry
