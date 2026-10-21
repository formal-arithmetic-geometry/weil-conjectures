/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ProEtaleConstantModuleEncoding
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.AlgebraicGeometry.ClassicalDerivedDefinitions
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedCategories

/-!
# Exact derived restriction to constant scalar sections

Source: Stacks Tags 093I and 03CY, and the coefficient-encoding passage of
proper base change (blueprint: lem-pe-constant-derived-encoding).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Restriction retains addition on sections. -/
instance proEtaleModuleRestriction_additive (X : Scheme.{u}) (A : Type u) [CommRing A] :
    (proEtaleModuleRestriction X A).Additive where
  map_add := by intros; ext U x; rfl

/-- The proved scalar-encoding equivalence supplies its categorical instance. -/
instance proEtaleModuleRestriction_equivalence (X : Scheme.{u}) (A : Type u) [CommRing A] :
    (proEtaleModuleRestriction X A).IsEquivalence :=
  proEtaleModuleRestriction_isEquivalence X A

/-- Restriction on the ordinary derived categories. No completion is involved. -/
abbrev proEtaleDerivedModuleRestriction (X : Scheme.{u}) (A : Type u) [CommRing A] :
    proEtaleDerivedCategory X A ⥤
      DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  (proEtaleModuleRestriction X A).mapDerivedCategory

private noncomputable def fixedHomologyStandardIso (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] (q : ℤ) :
    DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) q ≅
      (ShrinkHoms.equivalence.{u + 1}
        (@DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
          _ _ (HasDerivedCategory.standard _))).inverse ⋙
        @DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
          _ _ (HasDerivedCategory.standard _) q := by
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let Qs := @DerivedCategory.Q C _ _ (HasDerivedCategory.standard _)
  let Hs := @DerivedCategory.homologyFunctor C _ _ (HasDerivedCategory.standard _) q
  let e := ShrinkHoms.equivalence.{u + 1} (@DerivedCategory C _ _ (HasDerivedCategory.standard _))
  let hi : DerivedCategory.Q ⋙ e.inverse ≅ Qs :=
    (Functor.associator Qs e.functor e.inverse).symm ≪≫
      Functor.isoWhiskerLeft Qs e.unitIso.symm ≪≫ Functor.rightUnitor Qs
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) C).preimageIso
  exact DerivedCategory.homologyFunctorFactors C q ≪≫
    (@DerivedCategory.homologyFunctorFactors C _ _ (HasDerivedCategory.standard _) q).symm ≪≫
    (Functor.isoWhiskerRight hi Hs).symm ≪≫ Functor.associator _ _ _

/-- Derived restriction has the same cohomology, after identifying localization models.
Source: Stacks Tags 093I and 05RT (blueprint: lem-pe-constant-derived-encoding).
Proof: exact restriction commutes with cohomology. The second comparison only changes
from the small-Hom localization to the standard localization, through its equivalence.
-/
def proEtaleDerivedModuleRestrictionHomologyIso (X : Scheme.{u}) (A : Type u) [CommRing A]
    (q : ℤ) (K : proEtaleDerivedCategory X A) :
    (proEtaleModuleRestriction X A).obj
        ((DerivedCategory.homologyFunctor _ q).obj K) ≅
      (DerivedCategory.homologyFunctor _ q).obj
        ((proEtaleDerivedModuleRestriction X A).obj K) :=
  ((proEtaleModuleRestriction X A).mapDerivedCategoryHomologyFunctorIso q).app K

private theorem classicalFor_iso_iff (X : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ]
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (e : F ≅ G) :
    ProEtale.IsClassicalModuleFor X Λ F ↔ ProEtale.IsClassicalModuleFor X Λ G := by
  have h {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
      (e : F ≅ G) (hF : ProEtale.IsClassicalModuleFor X Λ F) :
        ProEtale.IsClassicalModuleFor X Λ G := by
    intro I _ _ P
    have hmap := ProEtale.continuityMap_natural P e.hom.hom
    have : IsIso (ProEtale.continuityMap P F.obj) := hF P
    have : IsIso (Functor.whiskerLeft P.diagram.op e.hom.hom) := by
      change IsIso (Functor.isoWhiskerLeft P.diagram.op
        ((sheafToPresheaf _ _).mapIso e)).hom
      infer_instance
    apply (isIso_comp_left_iff
      (colimMap (Functor.whiskerLeft P.diagram.op e.hom.hom)) _).mp
    rw [hmap]
    infer_instance
  exact ⟨h e, h e.symm⟩

/-- Exact restriction reflects every cohomological lower bound.
Source: Stacks Tag 05RT (blueprint: lem-pe-constant-derived-encoding).
Proof: exactness identifies each cohomology object with its restriction, and faithful
restriction reflects zero identities. Apply this in every degree below the bound.
-/
theorem proEtaleDerivedModuleRestriction_isGE_iff (X : Scheme.{u}) (A : Type u)
    [CommRing A] (K : proEtaleDerivedCategory X A) (n : ℤ) :
    DerivedCategory.IsGE ((proEtaleDerivedModuleRestriction X A).obj K) n ↔
      DerivedCategory.IsGE K n := by
  constructor
  · intro h
    apply (DerivedCategory.isGE_iff K n).mpr
    intro i hi
    exact Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (proEtaleModuleRestriction X A)
        ((DerivedCategory.isGE_iff _ n).mp h i hi)
  · intro h
    let := h
    exact (proEtaleModuleRestriction X A).isGE_mapDerivedCategory_obj K n

/-- Restriction identifies the two classicality predicates on derived objects.
Source: Stacks Tags 093I and 05RT (blueprint: lem-pe-constant-derived-encoding).
Proof: cohomology commutes with exact restriction. Its underlying set sheaf is unchanged.
The same continuity maps therefore characterize classicality, and their invertibility is
invariant under the cohomology comparison isomorphisms.
-/
theorem proEtaleDerivedModuleRestriction_classical_iff (X : Scheme.{u}) (A : Type u)
    [CommRing A] (K : proEtaleDerivedCategory X A) :
    ProEtale.IsClassicalModuleComplex K ↔
      ProEtale.IsClassicalComplexFor X (ULift.{u + 1, u} A)
        ((proEtaleDerivedModuleRestriction X A).obj K) := by
  have hfirst : ProEtale.IsClassicalModuleComplex K ↔ ProEtale.IsClassicalComplex A K := by
    apply forall_congr'
    intro q
    exact (ProEtale.isClassicalModule_iff A _).symm
  rw [hfirst]
  apply forall_congr'
  intro q
  have he := ((proEtaleModuleRestriction X A).mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
    (fixedHomologyStandardIso X (ULift.{u + 1, u} A) q).app
      ((proEtaleDerivedModuleRestriction X A).obj K)
  change ProEtale.IsClassicalModuleFor X (ULift.{u + 1, u} A)
    ((proEtaleModuleRestriction X A).obj
      ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q).obj K)) ↔ _
  exact classicalFor_iso_iff X (ULift.{u + 1, u} A) he

/-- Classicality is invariant under an isomorphism in the fixed-coefficient localization.
Source: naturality of continuity maps (blueprint: lem-pe-constant-derived-encoding).
-/
theorem proEtaleFixedClassical_iso_iff (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    {K L : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))}
    (e : K ≅ L) :
    ProEtale.IsClassicalComplexFor X A K ↔ ProEtale.IsClassicalComplexFor X A L := by
  apply forall_congr'
  intro q
  exact classicalFor_iso_iff X A
    ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q).mapIso
      ((ShrinkHoms.equivalence _).inverse.mapIso e))

end AlgebraicGeometry.Scheme
