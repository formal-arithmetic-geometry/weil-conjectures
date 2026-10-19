/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import WeilConjectures.RingTheory.IsStrictHenselization

/-! # A specified pointed-algebra presentation of a strict henselization

Source: Stacks Project, Algebra, Tag 04GW, pointed-algebra interpretation
(blueprint: def-sc-ring-strict-henselization).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- The forgetful diagram of etale `A`-algebras equipped with an `A`-map to `K`.
This is exactly the diagram in `Algebra.IsStrictHenselization`.
Source: Stacks Project, Tag 04GW (blueprint: def-sc-ring-strict-henselization). -/
def strictHenselizationPointedDiagram (A K : Type u) [CommRing A] [CommRing K]
    [Algebra A K] :
    (ObjectProperty.FullSubcategory
      (fun S : Over (CommAlgCat.of A K) ↦ Etale A S.left)) ⥤ CommAlgCat.{u} A :=
  ObjectProperty.ι (fun S : Over (CommAlgCat.of A K) ↦ Etale A S.left) ⋙
    Over.forget (CommAlgCat.of A K)

/-- The cocone consisting of the given pointings into `K`.
Source: Stacks Project, Tag 04GW (blueprint: def-sc-ring-strict-henselization). -/
def strictHenselizationPointingCocone (A K : Type u) [CommRing A] [CommRing K]
    [Algebra A K] : Cocone (strictHenselizationPointedDiagram A K) where
  pt := CommAlgCat.of A K
  ι := {
    app := fun S ↦ S.obj.hom
    naturality := fun _S _T f ↦ Over.w f.hom }

/-- A specified witness of the colimit predicate `Algebra.IsStrictHenselization`.
The cocone, universal property and algebra isomorphism are retained as data, so the
induced residue map refers to this presentation, rather than an unrelated choice.
Source: Stacks Project, Tag 04GW (blueprint: def-sc-ring-strict-henselization). -/
structure StrictHenselizationPresentation (A K H : Type u) [CommRing A] [IsLocalRing A]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing H] [Algebra A H] where
  /-- The defining pointed-etale algebra cocone. -/
  cocone : Cocone (strictHenselizationPointedDiagram A K)
  /-- Its universal property. -/
  isColimit : IsColimit cocone
  /-- The specified identification with the chosen algebra. -/
  identification : cocone.pt ≅ CommAlgCat.of A H

/-- The residue map induced by the pointings on the specified defining cocone.
Source: Stacks Project, Tag 04GW (blueprint: def-sc-ring-strict-henselization). -/
noncomputable def StrictHenselizationPresentation.residueMap
    {A K H : Type u} [CommRing A] [IsLocalRing A]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing H] [Algebra A H] (P : StrictHenselizationPresentation A K H) : H →+* K :=
  (P.identification.inv ≫ P.isColimit.desc (strictHenselizationPointingCocone A K)).hom.toRingHom

end Algebra
