/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed

/-!

# Open–closed detection and vanishing on derived categories of module objects over `Λ`

Let `Λ` be a commutative condensed ring, `j : U ⟶ X` a quasi-compact open immersion and
`i : Z ⟶ X` a closed immersion onto the complement of its range. This file lifts the
sheaf-level statements of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed` to the
derived categories `D(Mod_{Λ_X})` and to the bounded constructible derived categories
`Dᵇc(X)⟦Λ⟧`:

* the derived restrictions `Lj^*` and `Li^*` jointly reflect isomorphisms
  (`ProEtale.CondensedRing.jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl`,
  `ProEtale.CondensedRing.isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl`);
* `Lg^* (j_! K)` vanishes when the range of `g` misses the range of the open immersion `j`
  (`ProEtale.CondensedRing.isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint`,
  `ProEtale.CondensedRing.isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek`).

Since the pullbacks and the extension by zero are exact on module objects, both follow on
homology objects from the sheaf-level statements, through the isomorphisms
`L(g^*) ≅ D(g^*)` (`ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`).

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

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

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

include ℓ k

/-- **Open–closed detection on bounded constructible complexes**: for a quasi-compact open
immersion `j : U ⟶ X` and a closed immersion `i : Z ⟶ X` onto its complement, a morphism `φ`
of `Dᵇc(X)⟦Λ⟧` such that `Lj^* φ` and `Li^* φ` are isomorphisms is an isomorphism. -/
theorem isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl
    {Z U X : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (j : U ⟶ X) [QuasiCompact j.left]
    (hij : IsCompl (Set.range i.left.base) (Set.range j.left.base))
    {K K' : Dᵇc(X.left)⟦Λ⟧} (φ : K ⟶ K')
    (hj : IsIso ((boundedConstructibleUpperStar Λ ℓ j).map φ))
    (hi : IsIso ((boundedConstructibleUpperStar Λ ℓ i).map φ)) : IsIso φ := by
  have hι : IsIso ((boundedConstructible (condensedRingObj Λ X.left)).ι.map φ) :=
    (jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl Λ i.left j.left
      hij).isIso_of_pairFunctor _
      ((NatIso.isIso_map_iff (boundedConstructibleUpperStarCompatibility Λ ℓ j) φ).1
        (by rw [Functor.comp_map]; infer_instance))
      ((NatIso.isIso_map_iff (boundedConstructibleUpperStarCompatibility Λ ℓ i) φ).1
        (by rw [Functor.comp_map]; infer_instance))
  exact isIso_of_reflects_iso φ (boundedConstructible (condensedRingObj Λ X.left)).ι

/-- **`Lg^* (j_! K)` vanishes on bounded constructible complexes** when the range of `g` misses
the range of the open immersion `j`. -/
lemma isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek
    {U W X : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : U ⟶ X) [IsOpenImmersion j.left] (g : W ⟶ X)
    (hjg : Disjoint (Set.range j.left.base) (Set.range g.left.base)) (K : Dᵇc(U.left)⟦Λ⟧) :
    IsZero ((boundedConstructibleUpperStar Λ ℓ g).obj
      ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K)) := by
  have h : IsZero ((boundedConstructible (condensedRingObj Λ W.left)).ι.obj
      ((boundedConstructibleUpperStar Λ ℓ g).obj
        ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).obj K))) :=
    (isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint Λ j.left g.left hjg
      K.obj).of_iso ((boundedConstructibleUpperStarCompatibility Λ ℓ g).app _ ≪≫
        L((g.left)^*⟦Λ⟧).mapIso
          ((boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).app K))
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact (boundedConstructible (condensedRingObj Λ W.left)).ι.map_injective (by simpa using h)

end BoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
