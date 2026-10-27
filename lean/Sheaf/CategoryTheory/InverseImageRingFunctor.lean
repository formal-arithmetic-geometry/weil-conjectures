/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects
public import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects

/-!
# Ring-sheaf lift of a finite-limit-preserving inverse image

Source: Stacks Project, Sites, Tag 00YV, the discussion before the proposition and
its proof for rings as sextuples (blueprint: lem-route-inverse-image-ring-functor).

The four helper maps are the actual sectionwise operations of a ring sheaf, regarded
as maps of sheaves of sets. The theorem records their transport by the canonical
product and terminal comparisons and the compatibility of the lifted adjunction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory

/-- Addition of a ring sheaf as a map of sheaves of sets.
Source: Stacks Project, Sites, Tag 00YV, rings as sextuples
(blueprint: lem-route-inverse-image-ring-functor). -/
def ringSheafAdd {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    (sheafCompose J (forget CommRingCat.{u})).obj R ⊗
      (sheafCompose J (forget CommRingCat.{u})).obj R ⟶
        (sheafCompose J (forget CommRingCat.{u})).obj R :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : R.obj.obj U × R.obj.obj U ↦ x.1 + x.2)
     naturality := by
       intro U V f
       ext x
       change R.obj.obj U × R.obj.obj U at x
       change (R.obj.map f).hom x.1 + (R.obj.map f).hom x.2 =
         (R.obj.map f).hom (x.1 + x.2)
       exact (map_add _ _ _).symm }⟩

/-- Multiplication of a ring sheaf as a map of sheaves of sets.
Source: Stacks Project, Sites, Tag 00YV, rings as sextuples
(blueprint: lem-route-inverse-image-ring-functor). -/
def ringSheafMul {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    (sheafCompose J (forget CommRingCat.{u})).obj R ⊗
      (sheafCompose J (forget CommRingCat.{u})).obj R ⟶
        (sheafCompose J (forget CommRingCat.{u})).obj R :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun x : R.obj.obj U × R.obj.obj U ↦ x.1 * x.2)
     naturality := by
       intro U V f
       ext x
       change R.obj.obj U × R.obj.obj U at x
       change (R.obj.map f).hom x.1 * (R.obj.map f).hom x.2 =
         (R.obj.map f).hom (x.1 * x.2)
       exact (map_mul _ _ _).symm }⟩

/-- Zero of a ring sheaf as a map from the terminal sheaf of sets.
Source: Stacks Project, Sites, Tag 00YV, rings as sextuples
(blueprint: lem-route-inverse-image-ring-functor). -/
def ringSheafZero {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    𝟙_ (Sheaf J (Type u)) ⟶ (sheafCompose J (forget CommRingCat.{u})).obj R :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (0 : R.obj.obj U))
     naturality := by
       intro U V f
       ext x
       change (0 : R.obj.obj V) = (R.obj.map f).hom 0
       exact (map_zero _).symm }⟩

/-- One of a ring sheaf as a map from the terminal sheaf of sets.
Source: Stacks Project, Sites, Tag 00YV, rings as sextuples
(blueprint: lem-route-inverse-image-ring-functor). -/
def ringSheafOne {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :
    𝟙_ (Sheaf J (Type u)) ⟶ (sheafCompose J (forget CommRingCat.{u})).obj R :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun _ ↦ (1 : R.obj.obj U))
     naturality := by
       intro U V f
       ext x
       change (1 : R.obj.obj V) = (R.obj.map f).hom 1
       exact (map_one _).symm }⟩

/-- A finite-limit-preserving left adjoint on set sheaves lifts to commutative ring
sheaves, naturally on underlying sheaves and compatibly with operations and adjunction.
Source: Stacks Project, Sites, Tag 00YV, discussion before the proposition and proof
for rings as sextuples (blueprint: lem-route-inverse-image-ring-functor).

The components of `e` are the stated `e_R`; its naturality is exactly the equation
for every ring-sheaf morphism. The comparison `v` identifies the underlying right
adjoint, so that the final equation compares hom-equivalences in the same hom-set.
The operation equations have domain `L (|R| × |R|)` or `L (*)`, respectively, and
are equivalent to transporting by the inverses of the canonical comparisons.

Proof:
1. Use `sheaves_algebraicStructures_objects`
   (lem-weil-pbc-sheaf-algebraic-structures-objects) on each site to identify ring
   sheaves with internal commutative ring objects, compatibly with forgetting.
2. Finite-limit preservation implies preservation of binary products and the terminal
   object. Apply `Adjunction.liftsGroupRingObjects`
   (lem-weil-pbc-adjunction-lifts-group-ring-objects) to the given adjunction. Its
   ring branch supplies both functors, their adjunction, underlying comparisons,
   and the transport equations for all ring operations.
3. Conjugate both functors and the adjunction by the identifications from step 1.
   The underlying comparisons give `e` and `v`; their naturality gives the asserted
   equation on ring morphisms. The sectionwise operations in step 1 convert the
   operation equations from step 2 to the four displayed equations here.
4. Transport the hom-equivalence clause from step 2 through the same identifications.
   This gives the last equation, hence exactly the original set-sheaf hom-equivalence
   after forgetting rings and applying the underlying comparisons. -/
theorem inverseImage_ring_functor
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    {V : Sheaf K (Type u) ⥤ Sheaf J (Type u)}
    (adj : L ⊣ V) [PreservesFiniteLimits L] :
    ∃ (rings : Sheaf J CommRingCat.{u} ⥤ Sheaf K CommRingCat.{u})
      (Vrings : Sheaf K CommRingCat.{u} ⥤ Sheaf J CommRingCat.{u})
      (a : rings ⊣ Vrings)
      (e : sheafCompose J (forget CommRingCat.{u}) ⋙ L ≅
        rings ⋙ sheafCompose K (forget CommRingCat.{u}))
      (v : Vrings ⋙ sheafCompose J (forget CommRingCat.{u}) ≅
        sheafCompose K (forget CommRingCat.{u}) ⋙ V),
      (∀ R : Sheaf J CommRingCat.{u},
        L.map (ringSheafAdd R) ≫ (e.app R).hom =
          (prodComparisonIso L _ _).hom ≫ ((e.app R).hom ⊗ₘ (e.app R).hom) ≫
            ringSheafAdd (rings.obj R) ∧
        L.map (ringSheafMul R) ≫ (e.app R).hom =
          (prodComparisonIso L _ _).hom ≫ ((e.app R).hom ⊗ₘ (e.app R).hom) ≫
            ringSheafMul (rings.obj R) ∧
        L.map (ringSheafZero R) ≫ (e.app R).hom =
          (preservesTerminalIso L).hom ≫ ringSheafZero (rings.obj R) ∧
        L.map (ringSheafOne R) ≫ (e.app R).hom =
          (preservesTerminalIso L).hom ≫ ringSheafOne (rings.obj R)) ∧
      (∀ (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
        (f : rings.obj R ⟶ S),
        (sheafCompose J (forget CommRingCat.{u})).map (a.homEquiv R S f) ≫
            (v.app S).hom =
          adj.homEquiv ((sheafCompose J (forget CommRingCat.{u})).obj R)
            ((sheafCompose K (forget CommRingCat.{u})).obj S)
            ((e.app R).hom ≫ (sheafCompose K (forget CommRingCat.{u})).map f)) := by
  sorry

end CategoryTheory
