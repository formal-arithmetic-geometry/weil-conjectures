/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Stalks of topological inverse images

Source: Stacks Project, Sheaves, Tags 008H, 008O and Section 008P
(blueprint: lem-weil-pbc-topological-inverse-image-stalk).

The two statements give the natural stalk isomorphism, its formula on germs using
the sheaf-adjunction unit, and representation of every inverse-image stalk element.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Sheaf

/-- Stalks of the inverse image for sheaves of abelian groups, naturally in the sheaf.
Source: Stacks Project, Sheaves, Tags 008H, 008O and Section 008P.
(blueprint: lem-weil-pbc-topological-inverse-image-stalk)

Proof route from the node:
0. Identify the inverse image with the sheafification of the presheaf inverse image
   (def-weil-pbc-topological-inverse-image); the unit is the presheaf unit followed
   by the sheafification map.
1. Apply lem-weil-pbc-presheaf-inverse-image-stalk to identify the presheaf stalks,
   with its germ formula.
2. Apply lem-weil-pbc-stalk-sheafification-space in the abelian case, or
   lem-weil-pbc-ring-stalk-sheafification-space in the ring case, to the
   sheafification map.
3. Compose these isomorphisms. Their germ formulas give the displayed unit formula.
4. Represent an original stalk element by a germ (def-weil-pbc-module-stalk,
   and lem-weil-pbc-filtered-colimit-algebras-elementwise for rings). Surjectivity
   of the composite gives the final clause.
5. Naturality of the unit gives naturality on germs; since germs exhaust stalks,
   this gives naturality of the isomorphism.
-/
theorem exists_inverseImage_stalk_iso_ab {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    ∃ c : (forget AddCommGrpCat.{u} Y ⋙ Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)) ≅
        (pullback AddCommGrpCat.{u} f ⋙ forget AddCommGrpCat.{u} X ⋙
          Presheaf.stalkFunctor AddCommGrpCat.{u} x),
      (∀ (G : Y.Sheaf AddCommGrpCat.{u}) (V : Opens Y) (hV : f x ∈ V)
          (s : G.obj.obj (op V)),
        (c.app G).hom (Presheaf.germ G.obj V (f x) hV s) =
          Presheaf.germ ((pullback AddCommGrpCat.{u} f).obj G).obj
            ((Opens.map f).obj V) x hV
            ((((pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app G).hom.app (op V)) s)) ∧
      (∀ (G : Y.Sheaf AddCommGrpCat.{u})
          (t : Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
            ((pullback AddCommGrpCat.{u} f).obj G).obj x),
        ∃ (V : Opens Y) (hV : f x ∈ V) (s : G.obj.obj (op V)),
          Presheaf.germ ((pullback AddCommGrpCat.{u} f).obj G).obj
            ((Opens.map f).obj V) x hV
            ((((pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app G).hom.app
              (op V)) s) = t) := by
  sorry

/-- Stalks of the inverse image for sheaves of commutative rings, naturally in the sheaf.
Source: Stacks Project, Sheaves, Tags 008H, 008O and Section 008P.
(blueprint: lem-weil-pbc-topological-inverse-image-stalk)

Proof route from the node:
0. Identify the inverse image with the sheafification of the presheaf inverse image
   (def-weil-pbc-topological-inverse-image); the unit is the presheaf unit followed
   by the sheafification map.
1. Apply lem-weil-pbc-presheaf-inverse-image-stalk to identify the presheaf stalks,
   with its germ formula.
2. Apply lem-weil-pbc-stalk-sheafification-space in the abelian case, or
   lem-weil-pbc-ring-stalk-sheafification-space in the ring case, to the
   sheafification map.
3. Compose these isomorphisms. Their germ formulas give the displayed unit formula.
4. Represent an original stalk element by a germ (def-weil-pbc-module-stalk,
   and lem-weil-pbc-filtered-colimit-algebras-elementwise for rings). Surjectivity
   of the composite gives the final clause.
5. Naturality of the unit gives naturality on germs; since germs exhaust stalks,
   this gives naturality of the isomorphism.
-/
theorem exists_inverseImage_stalk_iso_commRing {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    ∃ c : (forget CommRingCat.{u} Y ⋙ Presheaf.stalkFunctor CommRingCat.{u} (f x)) ≅
        (pullback CommRingCat.{u} f ⋙ forget CommRingCat.{u} X ⋙
          Presheaf.stalkFunctor CommRingCat.{u} x),
      (∀ (G : Y.Sheaf CommRingCat.{u}) (V : Opens Y) (hV : f x ∈ V)
          (s : G.obj.obj (op V)),
        (c.app G).hom (Presheaf.germ G.obj V (f x) hV s) =
          Presheaf.germ ((pullback CommRingCat.{u} f).obj G).obj
            ((Opens.map f).obj V) x hV
            ((((pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app G).hom.app (op V)) s)) ∧
      (∀ (G : Y.Sheaf CommRingCat.{u})
          (t : Presheaf.stalk (C := CommRingCat.{u}) (X := X)
            ((pullback CommRingCat.{u} f).obj G).obj x),
        ∃ (V : Opens Y) (hV : f x ∈ V) (s : G.obj.obj (op V)),
          Presheaf.germ ((pullback CommRingCat.{u} f).obj G).obj
            ((Opens.map f).obj V) x hV
            ((((pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app G).hom.app
              (op V)) s) = t) := by
  sorry

end TopCat.Sheaf
