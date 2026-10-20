/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.Paper.OrientedConstructibleSheafVanishing
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Constructible set sheaves on oriented products

Source: Orgogozo, Modifications et cycles proches sur une base generale, Section 8.1,
printed pp. 17--18; Stacks Project Tag 093Q; ILO XI Sections 1.1, 1.9
(blueprint: def-trf-oriented-constructible-set-sheaf).

This is the finite-set version of the recorded module-valued finite rectangle definition.
It uses the same oriented products, finite scheme partitions, and stratum site maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.OrientedConstructibleSheaf

/-- Set-valued restriction to an oriented rectangle, using the same concrete triple
base change as stratumRestriction and its sheafified left Kan extension.
Source: Orgogozo Section 8.1; ILO XI Section 1.9
(blueprint: def-trf-oriented-constructible-set-sheaf). -/
def rectangleSets {X' Y' X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (i : X' ⟶ X) (j : Y' ⟶ Y) :
    Sheaf (productTopology.{u, v} f g) (Type (max (u + 1) v)) ⥤
      Sheaf (productTopology.{u, v} (i ≫ f) (j ≫ g)) (Type (max (u + 1) v)) :=
  sheafToPresheaf _ _ ⋙ (stratumBaseChange.{u, v} f g i j).op.lan ⋙ presheafToSheaf _ _

/-- The finite-set version of the recorded finite-rectangle constructibility definition.
On each rectangle, every site object has a covering sieve on which the sheaf is constant
with a finite set value in each slice. Values can vary with the covering member, and the
cover is not required to have finitely many members. This includes the degenerate topos.
Source: Orgogozo Section 8.1; Stacks 093Q
(blueprint: def-trf-oriented-constructible-set-sheaf). -/
def IsConstructibleSet {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (F : Sheaf (productTopology.{u, v} f g) (Type (max (u + 1) v))) : Prop :=
  ∃ (sX : X.FiniteLocallyClosedStratification) (sY : Y.FiniteLocallyClosedStratification),
    (∀ i : Fin sX.n, Topology.IsConstructible (sX.stratum i)) ∧
    (∀ j : Fin sY.n, Topology.IsConstructible (sY.stratum j)) ∧
    ∀ (i : Fin sX.n) (j : Fin sY.n)
      (U : ProductSite.{u, v} (sX.immersion i ≫ f) (sY.immersion j ≫ g)),
      ∃ R : Sieve U,
        R ∈ productTopology (sX.immersion i ≫ f) (sY.immersion j ≫ g) U ∧
        ∀ (V : ProductSite (sX.immersion i ≫ f) (sY.immersion j ≫ g)) (a : V ⟶ U), R a →
          ∃ M : Type (max (u + 1) v), Finite M ∧
            Nonempty
              (((productTopology (sX.immersion i ≫ f) (sY.immersion j ≫ g)).overPullback
                  (Type (max (u + 1) v)) V).obj
                ((rectangleSets f g (sX.immersion i) (sY.immersion j)).obj F) ≅
                (constantSheaf
                  ((productTopology (sX.immersion i ≫ f) (sY.immersion j ≫ g)).over V)
                  (Type (max (u + 1) v))).obj M)

/-- The same set predicate on the vanishing presentation, via the recorded normalization.
Source: ILO XI Section 1.9 (blueprint: def-trf-oriented-constructible-set-sheaf). -/
def IsConstructibleVanishingSet {X S : Scheme.{u}} (f : X ⟶ S)
    (F : VanishingTopos.{u, v} f) : Prop :=
  IsConstructibleSet f (𝟙 S)
    ((sheafToPresheaf (vanishingTopology f) (Type (max (u + 1) v)) ⋙
      (Functor.whiskeringLeft _ _ _).obj (vanishingNormalization.{u, v} f).op ⋙
      presheafToSheaf (productTopology f (𝟙 S)) (Type (max (u + 1) v))).obj F)

end AlgebraicGeometry.OrientedConstructibleSheaf
