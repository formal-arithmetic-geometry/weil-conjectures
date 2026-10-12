/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresAbelian

/-!
# Internal group objects and the abelian direct image

Source: Stacks Project, Section 00YR and Proposition 00YV, proof of (2).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Source: Stacks Project, Section 00YR and Proposition 00YV, proof of (2).
(blueprint: lem-weil-pbc-etale-abelian-direct-image-internal)

Proof: At each site take the sectionwise identification of abelian sheaves with
internal commutative group objects from `sheavesAlgebraicStructuresAbelian`.
The forward functor uses addition, zero and negation as multiplication, unit and
inverse; its inverse recovers the sectionwise abelian groups and homomorphisms.
The strict inverse identities give equivalences eV and eU, and the underlying
functor identities give iV and iU. The set direct image is precomposition along
base change. Its product comparison is the sectionwise pairing map, and its
terminal comparison is the unique map of singleton sheaves. Consequently the
operations on the image under R.mapCommGrp are exactly the operations of the
original abelian sheaf evaluated at the base-changed object. For each F the underlying
map of β is R.map (iU.hom.app F) followed by iV.inv.app (f_* F). The section
formulas for the two identifications show that this map preserves addition and
zero. The inverse uses iV.hom followed by R.map iU.inv and preserves the same
operations; preservation of negation follows from the group laws. These maps
are inverse because iU and iV are isomorphisms. Naturality follows from the
naturality of iU and iV and the sectionwise formula for direct image on morphisms;
faithfulness of CommGrp.forget gives the group-object naturality equation.
Composing the formula for β with iV.hom cancels iV.inv and gives the displayed
equation.
This argument uses no inverse image and no finite-limit assumption on it. -/
theorem etaleAbelianDirectImageInternal (U V : Scheme.{u}) (f : U ⟶ V) :
    let R : Sheaf U.smallEtaleTopology (Type (u + 1)) ⥤
        Sheaf V.smallEtaleTopology (Type (u + 1)) :=
      (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    letI : R.Braided := Functor.Braided.ofChosenFiniteProducts R
    ∃ (eV : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1} ≌
          CommGrp (Sheaf V.smallEtaleTopology (Type (u + 1))))
      (eU : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1} ≌
          CommGrp (Sheaf U.smallEtaleTopology (Type (u + 1))))
      (iV : eV.functor ⋙ CommGrp.forget _ ≅
        sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology)
      (iU : eU.functor ⋙ CommGrp.forget _ ≅
        sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology)
      (β : eU.functor ⋙ R.mapCommGrp ≅
        Etale.lowerStar AddCommGrpCat.{u + 1} f ⋙ eV.functor),
      ∀ F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1},
        (CommGrp.forget _).map (β.hom.app F) ≫
            iV.hom.app ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj F) =
          R.map (iU.hom.app F) := by sorry

end AlgebraicGeometry
