/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Addition transport for supplied inverse image comparisons

Source: Stacks Project, Tag 03D2, proof of lemma-pullback-module.
(blueprint: lem-weil-pbc-inverse-image-comparison-addition). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Source: Stacks Project, Tags 00X6, 00YV, and 03D2, proof of
lemma-pullback-module.
(blueprint: lem-weil-pbc-inverse-image-comparison-addition).

Proof: Apply etaleInverseImageAlgebraicStructures to obtain the canonical
abelian and commutative-ring lifts and their addition transport equations.
The ring lift is identified with Lr by uniqueness of left adjoints to Rr;
the abelian lift is the fixed La. Apply the two hom-equivalence compatibility
hypotheses to identity maps and use injectivity of the set adjunction's hom
bijection. This identifies the supplied comparisons with the canonical ones,
after the unique ring isomorphism. Naturality of that isomorphism and the fact
that its components are ring homomorphisms carry canonical addition to addition
on Lr. The abelian comparison is identified in the same manner. Precompose
categorical addition maps with the canonical tensor-to-product isomorphisms;
their section values are the sums of the two coordinates, because these
isomorphisms preserve both projections. Substitute the canonical transport
equations and cancel inverse comparison pairs to obtain the two equations.
No scalar action or distributivity law is used. -/
theorem etaleInverseImageComparisonAddition (U V : Scheme.{u}) (f : U ⟶ V)
    (O : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
    [PreservesFiniteLimits (Scheme.etaleSetPullback f)] :
    let L := Scheme.etaleSetPullback f
    let La := Etale.upperStar AddCommGrpCat.{u + 1} f
    let a := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
    let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
    let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
    let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
    let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let aS := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    ∀ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
        Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (ar : Lr ⊣ Rr) (er : Lr ⋙ FrU ≅ FrV ⋙ L),
    let OR := (sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj O)
    let OV := (sheafCompose V.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
    let FV := SheafOfModules.toSheaf.{u + 1} OV
    ∀ (ea : La ⋙ FaU ≅ FaV ⋙ L),
      (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
        FrV.map (ar.homEquiv G F h) =
          aS.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h)) ∧
      (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : La.obj G ⟶ F),
        FaV.map (a.homEquiv G F h) =
          aS.homEquiv (FaV.obj G) (FaU.obj F) (ea.inv.app G ≫ FaU.map h)) →
    ∀ G : SheafOfModules.{u + 1} OV,
    let X := FrV.obj O
    let Y := FaV.obj (FV.obj G)
    let X' := FrU.obj (Lr.obj O)
    let Y' := FaU.obj (La.obj (FV.obj G))
    let eV := fun (P Q : Sheaf V.smallEtaleTopology (Type (u + 1))) ↦
      (limit.isLimit (pair P Q)).conePointUniqueUpToIso
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct P Q)
    let eU := fun (P Q : Sheaf U.smallEtaleTopology (Type (u + 1))) ↦
      (limit.isLimit (pair P Q)).conePointUniqueUpToIso
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct P Q)
    ∃ (axV : X ⊗ X ⟶ X) (ayV : Y ⊗ Y ⟶ Y)
      (ax : X' ⊗ X' ⟶ X') (ay : Y' ⊗ Y' ⟶ Y'),
      (∀ (W : V.Etaleᵒᵖ) (r s : O.obj.obj W), axV.hom.app W (r, s) = r + s) ∧
      (∀ (W : V.Etaleᵒᵖ) (x y : G.val.obj W), ayV.hom.app W (x, y) = x + y) ∧
      (∀ (W : U.Etaleᵒᵖ) (r s : OR.obj.obj W), ax.hom.app W (r, s) = r + s) ∧
      (∀ (W : U.Etaleᵒᵖ) (x y : (La.obj (FV.obj G)).obj.obj W),
        ay.hom.app W (x, y) = x + y) ∧
      ((eU X' X').inv ≫ prod.map (er.hom.app O) (er.hom.app O) ≫
        inv (prodComparison L X X) ≫ L.map (eV X X).hom) ≫
          L.map axV ≫ er.inv.app O = ax ∧
      ((eU Y' Y').inv ≫
        prod.map (ea.hom.app (FV.obj G)) (ea.hom.app (FV.obj G)) ≫
        inv (prodComparison L Y Y) ≫ L.map (eV Y Y).hom) ≫
          L.map ayV ≫ ea.inv.app (FV.obj G) = ay := by sorry

end AlgebraicGeometry
