/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Reconstruction of a set-valued point from pointed site objects

Source: Stacks Project, Sites, Tags 00YA, 00YB and 00YC
(blueprint: lem-trf-site-point-reconstruction-sets).
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits Opposite

/-- The functor of pointed sheafified representables attached to a geometric morphism.
Source: Stacks Project, Sites, Tag 00YA (blueprint: lem-trf-site-point-reconstruction-sets). -/
noncomputable def sitePointFunctor {C : Type u} [Category.{v} C]
    (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v)
      (Sheaf J.toGrothendieck (Type v))) : C ⥤ Type v :=
  yoneda ⋙ presheafToSheaf J.toGrothendieck (Type v) ⋙ p.inverse

/-- The category of pointed objects of `sitePointFunctor`.
Source: Stacks Project, Sites, Tags 00YB and 00YC
(blueprint: lem-trf-site-point-reconstruction-sets). -/
abbrev sitePointNeighbourhood {C : Type u} [Category.{v} C]
    (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v)
      (Sheaf J.toGrothendieck (Type v))) :=
  (sitePointFunctor J p).Elements

/-- The diagram of sections indexed by pointed site objects.
Source: Stacks Project, Sites, Tag 00YA (blueprint: lem-trf-site-point-reconstruction-sets). -/
noncomputable def sitePointSectionDiagram {C : Type u} [Category.{v} C]
    (J : Precoverage C)
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v)
      (Sheaf J.toGrothendieck (Type v)))
    (F : Sheaf J.toGrothendieck (Type v)) :
    (sitePointNeighbourhood J p)ᵒᵖ ⥤ Type v where
  obj X := F.obj.obj (op X.unop.1)
  map f := F.obj.map f.unop.val.op
  map_id := by
    intro X
    simp
  map_comp := by
    intro X Y Z f g
    simp

/-- The sheaf morphism represented by a section of a sheaf on an object.
Source: Stacks Project, Sites, Tags 00Y6 and 00YA
(blueprint: lem-trf-site-point-reconstruction-sets). -/
noncomputable def sitePointSectionHom {C : Type u} [Category.{v} C]
    (J : Precoverage C) [HasWeakSheafify J.toGrothendieck (Type v)]
    (F : Sheaf J.toGrothendieck (Type v))
    {U : C} (s : F.obj.obj (op U)) :
    (presheafToSheaf J.toGrothendieck (Type v)).obj (yoneda.obj U) ⟶ F :=
  ((sheafificationAdjunction J.toGrothendieck (Type v)).homEquiv
      (yoneda.obj U) F).symm (yonedaEquiv.symm s)

/-- Set-valued site-point reconstruction from sheafified representables.
Source: Stacks Project, Sites, Tags 00YA (lemma-point-site-topos (2)), 00YB
(lemma-neighbourhoods-directed), and 00YC (proposition-point-limits)
(blueprint: lem-trf-site-point-reconstruction-sets).

Proof: the representable, sheafification, and inverse-image functors preserve finite
limits, yielding the finite-limit clause and the cofiltered category of pointed objects.
The sheaf axiom and local representatives prove joint surjectivity for every covering.
Yoneda and the geometric-morphism adjunction identify sections with maps from the
inverse-image pointed sets. The colimit universal property then identifies cocones with
maps into the direct image, and Yoneda uniqueness gives the canonical bijection.

The fourth clause says that the colimit `c` of the sections over pointed objects exists
(in `Type v`, with no `HasColimit` hypothesis, which is not automatic when the objects of
the site lie in a larger universe than `v`) and that the canonical map `e.hom` from it,
`(U, a, s) ↦ p⁻¹(s)(a)`, is a bijection.
-/
theorem site_point_reconstruction_sets {C : Type u} [Category.{v} C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    [HasFiniteLimits C]
    [HasWeakSheafify J.toGrothendieck (Type v)]
    (p : GeometricMorphism (Type v)
      (Sheaf J.toGrothendieck (Type v))) :
    PreservesFiniteLimits (sitePointFunctor J p) ∧
      (∀ (I : Type (max u v)) (U : C) (Ui : I → C)
        (f : ∀ i, Ui i ⟶ U),
        Presieve.ofArrows Ui f ∈ J U →
          ∀ x : (sitePointFunctor J p).obj U,
            ∃ (i : I) (y : (sitePointFunctor J p).obj (Ui i)),
              (sitePointFunctor J p).map (f i) y = x) ∧
      IsCofiltered (sitePointNeighbourhood J p) ∧
      (∀ (F : Sheaf J.toGrothendieck (Type v)),
        ∃ (c : Cocone (sitePointSectionDiagram J p F))
          (e : c.pt ≅ p.inverse.obj F),
          Nonempty (IsColimit c) ∧
          (∀ (U : C) (a : (sitePointFunctor J p).obj U)
            (s : F.obj.obj (op U)),
            e.hom (c.ι.app (Opposite.op ⟨U, a⟩) s) =
              (p.inverse.map (sitePointSectionHom J F s)) a)) ∧
      (∀ (F G : Sheaf J.toGrothendieck (Type v)) (α : F ⟶ G)
        (U : C) (s : F.obj.obj (op U)),
        sitePointSectionHom J G ((Sheaf.homEquiv α).app (op U) s) =
          sitePointSectionHom J F s ≫ α) := by
  sorry

end CategoryTheory
