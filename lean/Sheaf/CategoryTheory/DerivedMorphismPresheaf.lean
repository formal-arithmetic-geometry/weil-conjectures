/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Derived morphism presheaves on localized sites

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
namespace CategoryTheory
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
variable (J : GrothendieckTopology C) (B : Type (u + 1)) [CommRing B]

/-- Restriction of module sheaves to the localized site is additive, section by section.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
instance derivedSliceRestriction_additive (U : C) :
    (J.overPullback (ModuleCat.{u + 1} B) U).Additive where
  map_add := by intros; rfl

/-- Relocalization along a map of site objects is additive, section by section.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
instance derivedSliceMap_additive {U V : C} (f : V ⟶ U) :
    (J.overMapPullback (ModuleCat.{u + 1} B) f).Additive where
  map_add := by intros; rfl

/-- Exact restriction to a localized site, applied to the actual derived category.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev derivedSliceRestriction (U : C) :=
  (J.overPullback (ModuleCat.{u + 1} B) U).mapDerivedCategory

/-- Relocalization is exact: in particular it preserves finite colimits.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves)

Proof: Relocalization is inverse image for localization of topoi. Its restriction description is
left exact. It is also a left adjoint (the localized-site restriction adjunction), hence
preserves colimits. Apply this to constant-coefficient module sheaves; finite colimits are among
these colimits. -/
theorem derivedSliceMap_preservesFiniteColimits {U V : C} (f : V ⟶ U) :
    PreservesFiniteColimits (J.overMapPullback (ModuleCat.{u + 1} B) f) := by
  sorry

attribute [instance] derivedSliceMap_preservesFiniteColimits

/-- Exact relocalization of derived module sheaves along a map of site objects.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev derivedSliceMap {U V : C} (f : V ⟶ U) :=
  (J.overMapPullback (ModuleCat.{u + 1} B) f).mapDerivedCategory

/-- The canonical restriction/relocalization isomorphism on module sheaves.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def sliceRestrictionMapIso {U V : C} (f : V ⟶ U) :
    J.overPullback (ModuleCat.{u + 1} B) U ⋙
      J.overMapPullback (ModuleCat.{u + 1} B) f ≅
        J.overPullback (ModuleCat.{u + 1} B) V :=
  NatIso.ofComponents (fun F ↦ F.pushforwardOverMapIso f)
    (by intros; ext; rfl)

/-- The restriction/relocalization isomorphism induced on derived categories.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedSliceMapIso {U V : C} (f : V ⟶ U) :
    derivedSliceRestriction J B U ⋙ derivedSliceMap J B f ≅
      derivedSliceRestriction J B V :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sliceRestrictionMapIso J B f)

variable (A D : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))

/-- Restriction of an actual derived morphism, conjugated by the canonical slice isomorphisms.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalHomRestriction {U V : C} (f : V ⟶ U)
    (a : (derivedSliceRestriction J B U).obj A ⟶
      (derivedSliceRestriction J B U).obj D) :
    (derivedSliceRestriction J B V).obj A ⟶
      (derivedSliceRestriction J B V).obj D :=
  (derivedSliceMapIso J B f).inv.app A ≫ (derivedSliceMap J B f).map a ≫
    (derivedSliceMapIso J B f).hom.app D

/-- Restriction of an actual derived isomorphism, with the same canonical identifications.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalIsoRestriction {U V : C} (f : V ⟶ U)
    (a : (derivedSliceRestriction J B U).obj A ≅
      (derivedSliceRestriction J B U).obj D) :
    (derivedSliceRestriction J B V).obj A ≅
      (derivedSliceRestriction J B V).obj D :=
  ((derivedSliceMapIso J B f).app A).symm ≪≫ (derivedSliceMap J B f).mapIso a ≪≫
    (derivedSliceMapIso J B f).app D

/-- The restriction maps on derived Hom sets satisfy the identity and composition laws.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves)

Proof: On module sheaves the slice restriction identifications are identity maps on sections.
Their identity and cocycle laws therefore hold before deriving. Derive these identities using
the composition comparison for exact functors. Expand the three conjugations in the displayed
formulas, cancel consecutive comparison isomorphisms, and use preservation of identity and
composition by the localized functor. -/
theorem derivedLocalHomRestriction_laws :
    (∀ (U : C) (a : (derivedSliceRestriction J B U).obj A ⟶
      (derivedSliceRestriction J B U).obj D),
      derivedLocalHomRestriction J B A D (𝟙 U) a = a) ∧
    (∀ (U V W : C) (f : V ⟶ U) (g : W ⟶ V)
      (a : (derivedSliceRestriction J B U).obj A ⟶
        (derivedSliceRestriction J B U).obj D),
      derivedLocalHomRestriction J B A D g (derivedLocalHomRestriction J B A D f a) =
        derivedLocalHomRestriction J B A D (g ≫ f) a) := by
  sorry

/-- The restriction maps on derived isomorphisms satisfy the identity and composition laws.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves)

Proof: Apply the identity and cocycle calculation for derived Hom restriction to the hom
components. Apply it to the inverse components as well. Isomorphisms are determined by their hom
component, giving both equalities. -/
theorem derivedLocalIsoRestriction_laws :
    (∀ (U : C) (a : (derivedSliceRestriction J B U).obj A ≅
      (derivedSliceRestriction J B U).obj D),
      derivedLocalIsoRestriction J B A D (𝟙 U) a = a) ∧
    (∀ (U V W : C) (f : V ⟶ U) (g : W ⟶ V)
      (a : (derivedSliceRestriction J B U).obj A ≅
        (derivedSliceRestriction J B U).obj D),
      derivedLocalIsoRestriction J B A D g (derivedLocalIsoRestriction J B A D f a) =
        derivedLocalIsoRestriction J B A D (g ≫ f) a) := by
  sorry

/-- The presheaf of actual derived morphisms on localized sites, not underived module Hom.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalHomPresheaf : Cᵒᵖ ⥤ Type (u + 1) where
  obj U := (derivedSliceRestriction J B U.unop).obj A ⟶
    (derivedSliceRestriction J B U.unop).obj D
  map f := ↾(derivedLocalHomRestriction J B A D f.unop)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (derivedLocalHomRestriction_laws J B A D).1 U.unop a
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact ((derivedLocalHomRestriction_laws J B A D).2 _ _ _ f.unop g.unop a).symm

/-- The presheaf of actual derived isomorphisms on localized sites, retaining the inverse data.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalIsoPresheaf : Cᵒᵖ ⥤ Type (u + 1) where
  obj U := (derivedSliceRestriction J B U.unop).obj A ≅
    (derivedSliceRestriction J B U.unop).obj D
  map f := ↾(derivedLocalIsoRestriction J B A D f.unop)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (derivedLocalIsoRestriction_laws J B A D).1 U.unop a
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact ((derivedLocalIsoRestriction_laws J B A D).2 _ _ _ f.unop g.unop a).symm

/-- Sheafification of the presheaf of actual derived morphisms.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev derivedLocalHomSheaf [HasWeakSheafify J (Type (u + 1))] :=
  (presheafToSheaf J (Type (u + 1))).obj (derivedLocalHomPresheaf J B A D)

/-- Sheafification of the presheaf of actual derived isomorphisms.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev derivedLocalIsoSheaf [HasWeakSheafify J (Type (u + 1))] :=
  (presheafToSheaf J (Type (u + 1))).obj (derivedLocalIsoPresheaf J B A D)

/-- The section of a binary product corresponding to a specified pair of sections.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def sheafPairSection [HasWeakSheafify J (Type (u + 1))]
    (F G : Sheaf J (Type (u + 1))) (U : C)
    (s : F.obj.obj (op U)) (t : G.obj.obj (op U)) : (F ⨯ G).obj.obj (op U) :=
  inv (prodComparison (sheafToPresheaf J (Type (u + 1)) ⋙
    (evaluation Cᵒᵖ (Type (u + 1))).obj (op U)) F G)
    ((Types.binaryProductIso _ _).inv (s, t))

/-- Composition has a unique extension to the sheafified derived Hom presheaves.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves)

Proof: Composition commutes with restriction by functoriality of the localized derived functors.
Thus it defines a presheaf map from the product of the two Hom presheaves to the third.
Sheafification preserves finite products. Use that comparison and sheafify this presheaf map to
obtain the required morphism. The sheafification units are locally surjective; two morphisms
agreeing on pairs in their image agree locally on every pair of sections, hence agree by the
sheaf condition. This proves the asserted uniqueness. -/
theorem derivedLocalHomSheafComp_exists [HasSheafify J (Type (u + 1))]
    (G : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))) :
    ∃! m : derivedLocalHomSheaf J B A D ⨯ derivedLocalHomSheaf J B D G ⟶
        derivedLocalHomSheaf J B A G,
      ∀ (U : C) (f : (derivedSliceRestriction J B U).obj A ⟶
        (derivedSliceRestriction J B U).obj D)
      (g : (derivedSliceRestriction J B U).obj D ⟶
        (derivedSliceRestriction J B U).obj G),
      m.hom.app (op U)
          (sheafPairSection J _ _ U
            ((toSheafify J (derivedLocalHomPresheaf J B A D)).app (op U) f)
            ((toSheafify J (derivedLocalHomPresheaf J B D G)).app (op U) g)) =
        (toSheafify J (derivedLocalHomPresheaf J B A G)).app (op U) (f ≫ g) := by
  sorry

/-- Composition on sheafified derived Hom, determined uniquely by composition on local morphisms.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalHomSheafComp [HasSheafify J (Type (u + 1))]
    (G : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))) :
    derivedLocalHomSheaf J B A D ⨯ derivedLocalHomSheaf J B D G ⟶
      derivedLocalHomSheaf J B A G :=
  (derivedLocalHomSheafComp_exists J B A D G).choose

/-- Composition of isomorphisms has a unique extension to the sheafified presheaves.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves)

Proof: Use the same construction with actual composition of isomorphisms. It is compatible with
restriction, so gives a presheaf map. Sheafify it using left exactness of set sheafification.
Every pair of sections is locally represented by a pair of actual isomorphisms; the specified
values therefore determine the extension uniquely. -/
theorem derivedLocalIsoSheafComp_exists [HasSheafify J (Type (u + 1))]
    (G : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))) :
    ∃! m : derivedLocalIsoSheaf J B A D ⨯ derivedLocalIsoSheaf J B D G ⟶
        derivedLocalIsoSheaf J B A G,
      ∀ (U : C) (f : (derivedSliceRestriction J B U).obj A ≅
        (derivedSliceRestriction J B U).obj D)
      (g : (derivedSliceRestriction J B U).obj D ≅
        (derivedSliceRestriction J B U).obj G),
      m.hom.app (op U)
          (sheafPairSection J _ _ U
            ((toSheafify J (derivedLocalIsoPresheaf J B A D)).app (op U) f)
            ((toSheafify J (derivedLocalIsoPresheaf J B D G)).app (op U) g)) =
        (toSheafify J (derivedLocalIsoPresheaf J B A G)).app (op U) (f ≪≫ g) := by
  sorry

/-- Composition on sheafified derived Isom, determined uniquely by local composition.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalIsoSheafComp [HasSheafify J (Type (u + 1))]
    (G : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))) :
    derivedLocalIsoSheaf J B A D ⨯ derivedLocalIsoSheaf J B D G ⟶
      derivedLocalIsoSheaf J B A G :=
  (derivedLocalIsoSheafComp_exists J B A D G).choose

variable {J B} {A D}

/-- Precomposition and postcomposition commute with restriction of actual derived morphisms.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves)

Proof: Use naturality of the derived slice-restriction comparison on f and g. Expand the
conjugations defining local restriction, use preservation of composition by the local functor,
and cancel the adjacent comparison isomorphisms. The resulting composites on both sides are
identical. -/
theorem derivedLocalHomPresheafMap_natural
    {A' D' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (f : A' ⟶ A) (g : D ⟶ D') (U V : C) (h : V ⟶ U)
    (a : (derivedSliceRestriction J B U).obj A ⟶
      (derivedSliceRestriction J B U).obj D) :
    (derivedSliceRestriction J B V).map f ≫
        derivedLocalHomRestriction J B A D h a ≫
          (derivedSliceRestriction J B V).map g =
      derivedLocalHomRestriction J B A' D' h
        ((derivedSliceRestriction J B U).map f ≫ a ≫
          (derivedSliceRestriction J B U).map g) := by
  sorry

/-- The map on local derived Hom presheaves induced by precomposition and postcomposition.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalHomPresheafMap
    {A' D' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (f : A' ⟶ A) (g : D ⟶ D') :
    derivedLocalHomPresheaf J B A D ⟶ derivedLocalHomPresheaf J B A' D' where
  app U := ↾fun a ↦ (derivedSliceRestriction J B U.unop).map f ≫ a ≫
    (derivedSliceRestriction J B U.unop).map g
  naturality := by
    intro U V h
    apply ConcreteCategory.hom_ext
    intro a
    exact derivedLocalHomPresheafMap_natural f g _ _ h.unop a

/-- The map on local derived Isom presheaves induced by isomorphisms of the two arguments.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalIsoPresheafMap
    {A' D' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (f : A' ≅ A) (g : D ≅ D') :
    derivedLocalIsoPresheaf J B A D ⟶ derivedLocalIsoPresheaf J B A' D' where
  app U := ↾fun a ↦ (derivedSliceRestriction J B U.unop).mapIso f ≪≫ a ≪≫
    (derivedSliceRestriction J B U.unop).mapIso g
  naturality := by
    intro U V h
    apply ConcreteCategory.hom_ext
    intro a
    apply Iso.ext
    exact derivedLocalHomPresheafMap_natural f.hom g.hom _ _ h.unop a.hom

/-- Sheafification of the natural map on derived Isom presheaves.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev derivedLocalIsoSheafMap [HasWeakSheafify J (Type (u + 1))]
    {A' D' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (f : A' ≅ A) (g : D ≅ D') :=
  (presheafToSheaf J (Type (u + 1))).map (derivedLocalIsoPresheafMap f g)

/-- Sheafification of the natural map on derived Hom presheaves.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev derivedLocalHomSheafMap [HasWeakSheafify J (Type (u + 1))]
    {A' D' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))}
    (f : A' ⟶ A) (g : D ⟶ D') :=
  (presheafToSheaf J (Type (u + 1))).map (derivedLocalHomPresheafMap f g)

/-- The natural inclusion of local derived isomorphisms into local derived morphisms.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def derivedLocalIsoToHomPresheaf :
    derivedLocalIsoPresheaf J B A D ⟶ derivedLocalHomPresheaf J B A D where
  app U := ↾fun f ↦ f.hom
  naturality := by intros; rfl

/-- The map from derived Isom to derived Hom after sheafification.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev derivedLocalIsoToHomSheaf [HasWeakSheafify J (Type (u + 1))] :=
  (presheafToSheaf J (Type (u + 1))).map (derivedLocalIsoToHomPresheaf (A := A) (D := D))

variable (J B)

/-- A functor on derived module sheaves with its localized functors and coherent restriction
comparisons. The two naturality fields express precisely that the conjugated local maps give
presheaf maps; no arbitrary map replaces a derived morphism.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
structure DerivedLocalFunctor (B' : Type (u + 1)) [CommRing B'] where
  globalFunctor : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)) ⥤
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} B'))
  localFunctor (U : C) : DerivedCategory (Sheaf (J.over U) (ModuleCat.{u + 1} B)) ⥤
    DerivedCategory (Sheaf (J.over U) (ModuleCat.{u + 1} B'))
  restrictionIso (U : C) : derivedSliceRestriction J B U ⋙ localFunctor U ≅
    globalFunctor ⋙ derivedSliceRestriction J B' U
  hom_naturality (A D : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))
      (U V : C) (h : V ⟶ U)
      (a : (derivedSliceRestriction J B U).obj A ⟶
        (derivedSliceRestriction J B U).obj D) :
    (restrictionIso V).inv.app A ≫
        (localFunctor V).map (derivedLocalHomRestriction J B A D h a) ≫
          (restrictionIso V).hom.app D =
      derivedLocalHomRestriction J B' (globalFunctor.obj A) (globalFunctor.obj D) h
        ((restrictionIso U).inv.app A ≫ (localFunctor U).map a ≫
          (restrictionIso U).hom.app D)
  iso_naturality (A D : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))
      (U V : C) (h : V ⟶ U)
      (a : (derivedSliceRestriction J B U).obj A ≅
        (derivedSliceRestriction J B U).obj D) :
    ((restrictionIso V).app A).symm ≪≫
        (localFunctor V).mapIso (derivedLocalIsoRestriction J B A D h a) ≪≫
          (restrictionIso V).app D =
      derivedLocalIsoRestriction J B' (globalFunctor.obj A) (globalFunctor.obj D) h
        (((restrictionIso U).app A).symm ≪≫ (localFunctor U).mapIso a ≪≫
          (restrictionIso U).app D)

namespace DerivedLocalFunctor
variable {J B} {B' : Type (u + 1)} [CommRing B'] (T : DerivedLocalFunctor J B B')
variable (A D : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)))

/-- The map on derived Hom presheaves induced by a coherent family of localized functors.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def homPresheafMap :
    derivedLocalHomPresheaf J B A D ⟶
      derivedLocalHomPresheaf J B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) where
  app U := ↾fun a ↦ (T.restrictionIso U.unop).inv.app A ≫
    (T.localFunctor U.unop).map a ≫ (T.restrictionIso U.unop).hom.app D
  naturality := by
    intro U V h
    apply ConcreteCategory.hom_ext
    intro a
    exact T.hom_naturality A D _ _ h.unop a

/-- The map on derived Isom presheaves induced by the same localized functors.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def isoPresheafMap :
    derivedLocalIsoPresheaf J B A D ⟶
      derivedLocalIsoPresheaf J B' (T.globalFunctor.obj A) (T.globalFunctor.obj D) where
  app U := ↾fun a ↦ ((T.restrictionIso U.unop).app A).symm ≪≫
    (T.localFunctor U.unop).mapIso a ≪≫ (T.restrictionIso U.unop).app D
  naturality := by
    intro U V h
    apply ConcreteCategory.hom_ext
    intro a
    exact T.iso_naturality A D _ _ h.unop a

/-- The induced map on sheafified derived Hom.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev homSheafMap [HasWeakSheafify J (Type (u + 1))] :=
  (presheafToSheaf J (Type (u + 1))).map (T.homPresheafMap A D)

/-- The induced map on sheafified derived Isom.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable abbrev isoSheafMap [HasWeakSheafify J (Type (u + 1))] :=
  (presheafToSheaf J (Type (u + 1))).map (T.isoPresheafMap A D)

end DerivedLocalFunctor

variable {B' : Type (u + 1)} [CommRing B']

/-- The canonical commutation of restriction of scalars with localization, given by identity maps.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def sliceRestrictScalarsSheafIso (φ : B →+* B') (U : C) :
    J.overPullback (ModuleCat.{u + 1} B') U ⋙ Sheaf.restrictScalars (J.over U) φ ≅
      Sheaf.restrictScalars J φ ⋙ J.overPullback (ModuleCat.{u + 1} B) U :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The same canonical scalar/restriction commutation on actual derived categories.

Source: Stacks Project, Sites and Sheaves, localized sites; Cohomology on Sites, Tags 0946 and
09BE; Pro-etale Cohomology, Tag 0F63. (blueprint: def-weil-pbc-derived-morphism-presheaves) -/
noncomputable def sliceRestrictScalarsIso (φ : B →+* B') (U : C) :
    derivedSliceRestriction J B' U ⋙ Sheaf.derivedRestrictScalars (J.over U) φ ≅
      Sheaf.derivedRestrictScalars J φ ⋙ derivedSliceRestriction J B U :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (sliceRestrictScalarsSheafIso J B φ U) ≪≫
        Functor.mapDerivedCategoryCompIso _ _

end CategoryTheory
