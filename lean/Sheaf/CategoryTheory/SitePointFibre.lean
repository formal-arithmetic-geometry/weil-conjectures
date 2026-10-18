/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.Paper.SitePointReconstructionSets
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Reconstruction of a topos point from pointed site objects

Source: Stacks Project, Sites, Tags 00YA (2), 00Y7, 00Y8, and 00YV (6)
(blueprint: lem-trf-site-point-fibre).

The point is the given geometric adjunction, presented using sheaves on the
one-object site. No intrinsic site point is assumed. The comparison is uniquely
characterized by evaluation of inverse images of sheafified Yoneda sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology

/-- The punctual site in the common site/coefficient universe. Its only covering
sieve is maximal. Source: Stacks, Sites, 00X9 and 00YA (2)
(blueprint: lem-trf-site-point-fibre). -/
def sitePointTopology : GrothendieckTopology (Discrete PUnit.{u + 1}) := ⊥

/-- Sections as ordinary coefficient modules: restrict the sheaf-ring action along
constant scalar sections. Source: Stacks, Sites, 00YV (6)
(blueprint: lem-trf-site-point-fibre). -/
def sitePointModuleSections
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [CommRing Λ] [HasWeakSheafify J RingCat.{u}] :
    ConstantLeftModuleInverseImage.Modules J Λ ⥤ Cᵒᵖ ⥤ ModuleCat.{u} Λ :=
  constantRingModuleRestriction J Λ ⋙ sheafToPresheaf J (ModuleCat.{u} Λ)

/-- `L_p(T) = p⁻¹(h_T^#)`, evaluated at the sole punctual object. Here `L` is
precisely the inverse image in the supplied geometric adjunction.
Source: Stacks, Sites, 00YA (2) (blueprint: lem-trf-site-point-fibre). -/
def sitePointRepresentableFiber
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    (L : Sheaf J.toGrothendieck (Type u) ⥤ Sheaf sitePointTopology.{u} (Type u)) : C ⥤ Type u :=
  CategoryTheory.yoneda ⋙ presheafToSheaf J.toGrothendieck (Type u) ⋙ L ⋙
    (sheafSections sitePointTopology.{u} (Type u)).obj (op ⟨PUnit.unit⟩)

/-- The diagram `((T,a) ↦ F(T))` on `N_pᵒᵖ`; the category of elements uses
exactly the equation `L_p(b)(a)=a'` for its arrows. Source: Stacks, Sites, 00YA (2)
(blueprint: lem-trf-site-point-fibre). -/
def sitePointSectionsDiagram
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    (L : Sheaf J.toGrothendieck (Type u) ⥤ Sheaf sitePointTopology.{u} (Type u))
    (Λ : Type u) [CommRing Λ] [HasWeakSheafify J.toGrothendieck RingCat.{u}]
    (F : ConstantLeftModuleInverseImage.Modules J.toGrothendieck Λ) :
    (sitePointRepresentableFiber J L).Elementsᵒᵖ ⥤ ModuleCat.{u} Λ :=
  (CategoryOfElements.π (sitePointRepresentableFiber J L)).op ⋙
    (sitePointModuleSections J.toGrothendieck Λ).obj F

/-- The sectionwise map of pointed section diagrams induced by a module morphism.
Source: Stacks, Sites, 00YA (2) (blueprint: lem-trf-site-point-fibre). -/
def sitePointSectionsMap
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    (L : Sheaf J.toGrothendieck (Type u) ⥤ Sheaf sitePointTopology.{u} (Type u))
    (Λ : Type u) [CommRing Λ] [HasWeakSheafify J.toGrothendieck RingCat.{u}]
    {F G : ConstantLeftModuleInverseImage.Modules J.toGrothendieck Λ} (f : F ⟶ G) :
    sitePointSectionsDiagram J L Λ F ⟶ sitePointSectionsDiagram J L Λ G :=
  Functor.whiskerLeft (CategoryOfElements.π (sitePointRepresentableFiber J L)).op
    ((sitePointModuleSections J.toGrothendieck Λ).map f)

/-- Punctual module sheaves as ordinary `Λ`-modules, using evaluation and restriction
along constant scalars. Source: Stacks, Sites, 00X9 and 00YV (6)
(blueprint: lem-trf-site-point-fibre). -/
def sitePointModuleEvaluation (Λ : Type u) [CommRing Λ]
    [HasWeakSheafify sitePointTopology.{u} RingCat.{u}] :
    ConstantLeftModuleInverseImage.Modules sitePointTopology.{u} Λ ⥤ ModuleCat.{u} Λ :=
  sitePointModuleSections sitePointTopology.{u} Λ ⋙
    (evaluation _ _).obj (op ⟨PUnit.unit⟩)

/-- Reconstruct the given topos point from inverse images of sheafified representables.
The uniquely specified linear comparison has the formula `p⁻¹(s)(a)` after the
recorded underlying-set isomorphism of the constant-module lift. Exactness means
preservation of both finite limits and finite colimits. Initial restriction uses
the canonical colimit map and retains the formula and naturality.

Source: Stacks Project, Sites, 00YA (2), 00Y7, 00Y8 and 00YV (6), and Algebra,
00DB (blueprint: lem-trf-site-point-fibre).

Proof (the eight steps of the node):
1. Yoneda, sheafification and `L` preserve finite limits. Thus `L_p` preserves the
terminal object, products and equalizers. The terminal point, paired product points
and lifted equalizer points prove cofilteredness. Objects and arrows are small in
`u`, since they are pairs and subtypes of data in `u`.
2. Yoneda, sheafification and the given adjunction identify `(R E)(T)` with maps
`L_p(T) → E`. Naturality identifies restriction with precomposition. This is the
already existing sheaf `R E`, so no extra site-point datum is assumed.
3. Maps from the set colimit of pointed sections to `E` are compatible families.
Currying them identifies these with sheaf maps to `R E`, naturally in both variables.
4. Under that bijection and the given adjunction, precomposition with the comparison
`[T,a,s] ↦ L(s)(a)` is a bijection. Taking maps into the source and target gives its
inverse. The formula and sectionwise action give uniqueness and naturality.
5. The underlying set of the filtered module colimit is the filtered set colimit:
representatives agree precisely after refinement to a common pointed object, by the
set and module elementwise colimit criteria. Addition uses a common refinement;
scalar multiplication uses one representative.
6. The supplied constant-module lift transports addition and scalar endomorphisms
by `L`. Apply `L` to the sheafified section maps and to their addition and scalar
composites. Its finite-product comparison and `d.moduleSetIso` prove that the map
in step 4 is linear, hence a module isomorphism, with the stated normalization.
7. The constant-module inverse-image theorem gives preservation of kernels and
cokernels. Punctual evaluation identifies its target with ordinary modules and
preserves both; filtered module colimits are exact by Algebra 00DB.
8. A small full initial subcategory is cofiltered: refine common sources and
an equalizing source using initiality, and use fullness to lift the arrows.
Initial restriction, dual to the initial-functor limit theorem, gives the canonical
map `colimit.pre`; composing it with the comparison gives the normalized iso.
Its legs give the same representative formula, its naturality gives the displayed
square, and filtered module colimits over the restricted index are again exact. -/
theorem site_point_fibre
    {C : Type u} [SmallCategory C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    [HasFiniteLimits C]
    (Λ : Type u) [CommRing Λ] [HasWeakSheafify J.toGrothendieck RingCat.{u}]
    [HasWeakSheafify sitePointTopology.{u} RingCat.{u}]
    (L : Sheaf J.toGrothendieck (Type u) ⥤ Sheaf sitePointTopology.{u} (Type u))
    (R : Sheaf sitePointTopology.{u} (Type u) ⥤ Sheaf J.toGrothendieck (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L)
    (d : ConstantLeftModuleInverseImageData.{u, w}
      J.toGrothendieck sitePointTopology Λ L R adj hL) :
    IsCofiltered (sitePointRepresentableFiber J L).Elements ∧
      ∃ c : ∀ F : ConstantLeftModuleInverseImage.Modules J.toGrothendieck Λ,
        colimit (sitePointSectionsDiagram J L Λ F) ⟶
          (sitePointModuleEvaluation Λ).obj (d.moduleFunctor.obj F),
        (∀ F, IsIso (c F)) ∧
        (∀ (F : ConstantLeftModuleInverseImage.Modules J.toGrothendieck Λ) (T : C)
          (a : (sitePointRepresentableFiber J L).obj T)
          (s : ((sitePointModuleSections J.toGrothendieck Λ).obj F).obj (op T)),
          (d.moduleSetIso.hom.app F).hom.app (op ⟨PUnit.unit⟩)
            ((c F).hom ((colimit.ι (sitePointSectionsDiagram J L Λ F) (op ⟨T, a⟩)).hom s)) =
          (L.map (CategoryTheory.sitePointSectionHom J
            ((ConstantLeftModuleInverseImage.W J.toGrothendieck Λ).obj F) s)).hom.app
              (op ⟨PUnit.unit⟩) a) ∧
        (∀ (F G : ConstantLeftModuleInverseImage.Modules J.toGrothendieck Λ) (f : F ⟶ G),
          colim.map (sitePointSectionsMap J L Λ f) ≫ c G =
            c F ≫ (sitePointModuleEvaluation Λ).map (d.moduleFunctor.map f)) ∧
        (∀ (F : ConstantLeftModuleInverseImage.Modules J.toGrothendieck Λ)
          (q : colimit (sitePointSectionsDiagram J L Λ F) ⟶
            (sitePointModuleEvaluation Λ).obj (d.moduleFunctor.obj F)),
          (∀ (T : C) (a : (sitePointRepresentableFiber J L).obj T)
            (s : ((sitePointModuleSections J.toGrothendieck Λ).obj F).obj (op T)),
            (d.moduleSetIso.hom.app F).hom.app (op ⟨PUnit.unit⟩)
              (q.hom ((colimit.ι (sitePointSectionsDiagram J L Λ F) (op ⟨T, a⟩)).hom s)) =
            (L.map (CategoryTheory.sitePointSectionHom J
              ((ConstantLeftModuleInverseImage.W J.toGrothendieck Λ).obj F) s)).hom.app
              (op ⟨PUnit.unit⟩) a) → q = c F) ∧
        PreservesFiniteLimits d.moduleFunctor ∧ PreservesFiniteColimits d.moduleFunctor ∧
        PreservesFiniteLimits (d.moduleFunctor ⋙ sitePointModuleEvaluation Λ) ∧
        PreservesFiniteColimits (d.moduleFunctor ⋙ sitePointModuleEvaluation Λ) ∧
        HasExactColimitsOfShape (sitePointRepresentableFiber J L).Elementsᵒᵖ (ModuleCat.{u} Λ) ∧
        (∀ {B : Type u} [SmallCategory B]
          (H : B ⥤ (sitePointRepresentableFiber J L).Elements) [H.Full] [H.Faithful]
          [Functor.Initial H],
          IsCofiltered B ∧ HasExactColimitsOfShape Bᵒᵖ (ModuleCat.{u} Λ) ∧
          ∃ e : ∀ F : ConstantLeftModuleInverseImage.Modules J.toGrothendieck Λ,
            colimit (H.op ⋙ sitePointSectionsDiagram J L Λ F) ≅
              (sitePointModuleEvaluation Λ).obj (d.moduleFunctor.obj F),
            (∀ F, (e F).hom = colimit.pre (sitePointSectionsDiagram J L Λ F) H.op ≫ c F) ∧
            (∀ (F : ConstantLeftModuleInverseImage.Modules J.toGrothendieck Λ) (b : B)
              (s : (H.op ⋙ sitePointSectionsDiagram J L Λ F).obj (op b)),
              (d.moduleSetIso.hom.app F).hom.app (op ⟨PUnit.unit⟩)
                ((e F).hom.hom
                  ((colimit.ι (H.op ⋙ sitePointSectionsDiagram J L Λ F) (op b)).hom s)) =
              (L.map (CategoryTheory.sitePointSectionHom J
                ((ConstantLeftModuleInverseImage.W J.toGrothendieck Λ).obj F) s)).hom.app
              (op ⟨PUnit.unit⟩) (H.obj b).2) ∧
            (∀ (F G : ConstantLeftModuleInverseImage.Modules J.toGrothendieck Λ) (f : F ⟶ G),
              colim.map (Functor.whiskerLeft H.op (sitePointSectionsMap J L Λ f)) ≫ (e G).hom =
                (e F).hom ≫ (sitePointModuleEvaluation Λ).map (d.moduleFunctor.map f))) := by
  sorry

/-- The canonical comparison into the actual constant-module inverse image, written
as an ordinary module by punctual evaluation. The preceding theorem determines
this map uniquely by `L(s)(a)`; choosing that unique map postpones only its proof,
not any unspecified data. Source: Stacks, Sites, 00YA (2) and 00YV (6)
(blueprint: lem-trf-site-point-fibre). -/
def sitePointFiberComparison
    {C : Type u} [SmallCategory C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    [HasFiniteLimits C]
    (Λ : Type u) [CommRing Λ] [HasWeakSheafify J.toGrothendieck RingCat.{u}]
    [HasWeakSheafify sitePointTopology.{u} RingCat.{u}]
    (L : Sheaf J.toGrothendieck (Type u) ⥤ Sheaf sitePointTopology.{u} (Type u))
    (R : Sheaf sitePointTopology.{u} (Type u) ⥤ Sheaf J.toGrothendieck (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L)
    (d : ConstantLeftModuleInverseImageData.{u, w}
      J.toGrothendieck sitePointTopology Λ L R adj hL)
    (F : ConstantLeftModuleInverseImage.Modules J.toGrothendieck Λ) :
    colimit (sitePointSectionsDiagram J L Λ F) ⟶
      (sitePointModuleEvaluation Λ).obj (d.moduleFunctor.obj F) :=
  (site_point_fibre J hJ Λ L R adj hL d).2.choose F

/-- The canonical initial-restriction isomorphism. Its hom is `colimit.pre` followed
by `sitePointFiberComparison`, as specified by the reconstruction theorem; an
isomorphism is uniquely determined by this hom. Source: Stacks, Categories, 002R,
dualized, and Sites, 00YA (2) (blueprint: lem-trf-site-point-fibre). -/
def sitePointInitialFiberIso
    {C : Type u} [SmallCategory C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    [HasFiniteLimits C]
    (Λ : Type u) [CommRing Λ] [HasWeakSheafify J.toGrothendieck RingCat.{u}]
    [HasWeakSheafify sitePointTopology.{u} RingCat.{u}]
    (L : Sheaf J.toGrothendieck (Type u) ⥤ Sheaf sitePointTopology.{u} (Type u))
    (R : Sheaf sitePointTopology.{u} (Type u) ⥤ Sheaf J.toGrothendieck (Type u))
    (adj : L ⊣ R) (hL : PreservesFiniteLimits L)
    (d : ConstantLeftModuleInverseImageData.{u, w}
      J.toGrothendieck sitePointTopology Λ L R adj hL)
    {B : Type u} [SmallCategory B]
    (H : B ⥤ (sitePointRepresentableFiber J L).Elements) [H.Full] [H.Faithful]
    [Functor.Initial H] (F : ConstantLeftModuleInverseImage.Modules J.toGrothendieck Λ) :
    colimit (H.op ⋙ sitePointSectionsDiagram J L Λ F) ≅
      (sitePointModuleEvaluation Λ).obj (d.moduleFunctor.obj F) :=
  (((site_point_fibre J hJ Λ L R adj hL d).2.choose_spec.2.2.2.2.2.2.2.2.2 H).2.2).choose F

end CategoryTheory.GrothendieckTopology
