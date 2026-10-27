/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.ModuleAbelianUniverseEquiv
public import Sheaf.AlgebraicGeometry.QcoherentZariskiCohomologyMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import Sheaf.AlgebraicGeometry.ZariskiModuleHMapFormula

/-! # Ext universe transport respects the abelian h-map

Source: Mathlib Ext.mapExactFunctor_hom and Ext.homEquiv_chgUniv;
Stacks Project, Tag 01FB.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

attribute [local instance] HasExt.standard
attribute [local irreducible] zariskiModuleHMap tensorPullback tensorPullbackObj

private theorem universe_mapFunctor
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
    [hsJ : HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [hlJ : HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u})]
    [hsK : HasExt.{u} (Sheaf K AddCommGrpCat.{u})]
    [hlK : HasExt.{u + 1} (Sheaf K AddCommGrpCat.{u})]
    (L : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u})
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : (constantSheaf K AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ)) ≅
      L.obj ((constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))))
    (F : Sheaf J AddCommGrpCat.{u}) (q : ℕ) (x : Sheaf.H.{u} F q) :
    @coherentExtUniverseEquiv _ _ _ hsK hlK _ _ q
      (Sheaf.H.mapFunctor.{u} L e F q x) =
    Sheaf.H.mapFunctor.{u + 1} L e F q
      (@coherentExtUniverseEquiv _ _ _ hsJ hlJ _ _ q x) := by
  let := HasDerivedCategory.standard (Sheaf J AddCommGrpCat.{u})
  let := HasDerivedCategory.standard (Sheaf K AddCommGrpCat.{u})
  apply Abelian.Ext.homAddEquiv.injective
  rw [coherentExtUniverseEquiv_hom]
  simp only [Sheaf.H.mapFunctor_apply, Abelian.Ext.homAddEquiv_apply,
    Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, Abelian.Ext.mapExactFunctor_hom]
  have hx : (@coherentExtUniverseEquiv _ _ _ hsJ hlJ _ _ q x).hom = x.hom := by
    simpa only [Abelian.Ext.homAddEquiv_apply] using
      (coherentExtUniverseEquiv_hom (hs := hsJ) (hl := hlJ) q x)
  rw [hx]

private theorem universe_sheaf_hmap
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
    [hsJ : HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    [hlJ : HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u})]
    [hsK : HasExt.{u} (Sheaf K AddCommGrpCat.{u})]
    [hlK : HasExt.{u + 1} (Sheaf K AddCommGrpCat.{u})]
    (L : Sheaf J AddCommGrpCat.{u} ⥤ Sheaf K AddCommGrpCat.{u})
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : (constantSheaf K AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ)) ≅
      L.obj ((constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))))
    (A : Sheaf J AddCommGrpCat.{u}) (B : Sheaf K AddCommGrpCat.{u})
    (φ : L.obj A ⟶ B) (q : ℕ) (x : Sheaf.H.{u} A q) :
    @coherentExtUniverseEquiv _ _ _ hsK hlK _ _ q
      (Sheaf.H.map.{u} φ q (Sheaf.H.mapFunctor.{u} L e A q x)) =
    Sheaf.H.map.{u + 1} φ q (Sheaf.H.mapFunctor.{u + 1} L e A q
      (@coherentExtUniverseEquiv _ _ _ hsJ hlJ _ _ q x)) := by
  exact (coherentSheafUniverseEquiv_naturality K q φ _).trans
    (congrArg (Sheaf.H.map.{u + 1} φ q) (universe_mapFunctor L e A q x))

/-- Universe change commutes with the explicit abelian Ext h-map.
Source: Mathlib Ext.mapExactFunctor_hom and Ext.homEquiv_chgUniv;
Stacks Project, Tag 01FB.
(blueprint: lem-pbc-module-abelian-universe-hmap).

Proof: Unfold the cached universe equivalences. Universe change commutes with
postcomposition by the coefficient map, by coherentSheafUniverseEquiv_naturality.
For inverse image, compare the represented derived morphisms with
Ext.mapExactFunctor_hom and Ext.homEquiv_chgUniv, including precomposition by the
constant-integer comparison. The explicit coefficient and constant-sheaf maps
are exactly those in zariskiModuleHMap, by its definition. -/
theorem moduleAbelianUniverseMap_hmap {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (φ : F ⟶ (pushforward g).obj G)
    (q : ℕ) (x : H F q) :
    moduleAbelianUniverseMap Y G q
      (Sheaf.H.map (coeff g φ) q
        (Sheaf.H.mapFunctor (invImage g) (constIso g).symm
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) q x)) =
      zariskiModuleHMap g φ q (moduleAbelianUniverseMap X F q x) := by
  unfold moduleAbelianUniverseMap
  exact (universe_sheaf_hmap
    (hsJ := comparisonHasExt X) (hlJ := HasExt.standard _)
    (hsK := comparisonHasExt Y) (hlK := HasExt.standard _)
    (invImage g) (constIso g).symm _ _ (coeff g φ) q x).trans
      (zariskiModuleHMap_formula g F G φ q _)

end
end AlgebraicGeometry.Scheme.Modules
