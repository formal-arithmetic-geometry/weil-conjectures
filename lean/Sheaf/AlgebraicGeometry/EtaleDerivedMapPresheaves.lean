/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Presheaves of derived etale maps

Source: Stacks Project, sites-cohomology.tex, Tag 09BE, lemma-locally-constant-map,
and the derived Hom presheaf used in the finite-ring extension of that lemma
(blueprint: def-weil-pbc-etale-derived-map-presheaves).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Etale

variable {X : Scheme.{u}} (B : Type (u + 1)) [CommRing B]

/-- The comparison between restriction to `U` and restriction first to `V` then to `U`.
Source: Stacks, Tag 09BE, restriction of derived maps
(blueprint: def-weil-pbc-etale-derived-map-presheaves). -/
noncomputable def derivedMapRestrictionIso {U V : X.Etale} (f : U ⟶ V)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K ≅
      (upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory.obj
        ((upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj K) :=
  (Functor.mapDerivedCategoryNatIso
    (upperStarComp (ModuleCat.{u + 1} B) f.left V.hom U.hom f.w.symm) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).app K

/-- Restrict a derived morphism along an arrow of the small etale site.
Source: Stacks, Tag 09BE (blueprint: def-weil-pbc-etale-derived-map-presheaves). -/
noncomputable def restrictDerivedMap
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    {U V : X.Etale} (f : U ⟶ V)
    (a : (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj K ⟶
      (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj L) :
    (upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K ⟶
      (upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj L :=
  (derivedMapRestrictionIso B f K).hom ≫
    (upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory.map a ≫
      (derivedMapRestrictionIso B f L).inv

/-- Restrict an isomorphism in the same manner.
Source: Stacks, Tag 09BE (blueprint: def-weil-pbc-etale-derived-map-presheaves). -/
noncomputable def restrictDerivedIso
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    {U V : X.Etale} (f : U ⟶ V)
    (a : (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj K ≅
      (upperStar (ModuleCat.{u + 1} B) V.hom).mapDerivedCategory.obj L) :
    (upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj K ≅
      (upperStar (ModuleCat.{u + 1} B) U.hom).mapDerivedCategory.obj L :=
  derivedMapRestrictionIso B f K ≪≫
    (upperStar (ModuleCat.{u + 1} B) f.left).mapDerivedCategory.mapIso a ≪≫
      (derivedMapRestrictionIso B f L).symm

/-- The restriction functions satisfy the presheaf laws.
Source: Stacks, Tag 09BE (blueprint: def-weil-pbc-etale-derived-map-presheaves).
Proof: restriction to an identity is the identity by the unit coherence of pullback.
The pullback associativity coherence identifies restriction along a composite with
successive restriction. Apply the corresponding composition comparisons on derived
categories; the middle comparison and its inverse cancel. For isomorphisms the same
calculation applies to the forward and inverse arrows. -/
theorem derivedMapRestriction_laws
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (∀ (U : X.Etale) (a), restrictDerivedMap B (K := K) (L := L) (𝟙 U) a = a) ∧
    (∀ (U V W : X.Etale) (f : U ⟶ V) (g : V ⟶ W) (a),
      restrictDerivedMap B (K := K) (L := L) (f ≫ g) a =
        restrictDerivedMap B f (restrictDerivedMap B g a)) ∧
    (∀ (U : X.Etale) (a), restrictDerivedIso B (K := K) (L := L) (𝟙 U) a = a) ∧
    (∀ (U V W : X.Etale) (f : U ⟶ V) (g : V ⟶ W) (a),
      restrictDerivedIso B (K := K) (L := L) (f ≫ g) a =
        restrictDerivedIso B f (restrictDerivedIso B g a)) := by
  sorry

/-- The presheaf `U ↦ Hom(K|U,L|U)` in the derived categories of etale module sheaves.
Source: Stacks, Tag 09BE (blueprint: def-weil-pbc-etale-derived-map-presheaves). -/
noncomputable def derivedHomPresheaf
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    X.Etaleᵒᵖ ⥤ Type (u + 1) where
  obj U := (upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.obj K ⟶
    (upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.obj L
  map f := TypeCat.ofHom (restrictDerivedMap B (K := K) (L := L) f.unop)
  map_id U := ConcreteCategory.hom_ext _ _ ((derivedMapRestriction_laws B K L).1 U.unop)
  map_comp f g :=
    ConcreteCategory.hom_ext _ _ ((derivedMapRestriction_laws B K L).2.1 _ _ _ g.unop f.unop)

/-- The presheaf `U ↦ Isom(K|U,L|U)`, which can take the empty value.
Source: Stacks, Tag 09BE (blueprint: def-weil-pbc-etale-derived-map-presheaves). -/
noncomputable def derivedIsoPresheaf
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    X.Etaleᵒᵖ ⥤ Type (u + 1) where
  obj U := (upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.obj K ≅
    (upperStar (ModuleCat.{u + 1} B) U.unop.hom).mapDerivedCategory.obj L
  map f := TypeCat.ofHom (restrictDerivedIso B (K := K) (L := L) f.unop)
  map_id U := ConcreteCategory.hom_ext _ _ ((derivedMapRestriction_laws B K L).2.2.1 U.unop)
  map_comp f g :=
    ConcreteCategory.hom_ext _ _ ((derivedMapRestriction_laws B K L).2.2.2 _ _ _ g.unop f.unop)

end AlgebraicGeometry.Etale
