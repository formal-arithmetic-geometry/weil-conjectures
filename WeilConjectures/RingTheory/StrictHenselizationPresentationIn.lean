/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.StrictHenselizationPresentation

/-!
# Strict henselization presentations in a universe containing the base ring

Source: Stacks Project, Algebra, Tag 04GW, pointed-algebra description
(blueprint: def-sc-ring-strict-henselization).

This is the recorded pointed-etale colimit presentation with independent base-ring and
algebra universes. The common algebra universe is at least the base-ring universe.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- The forgetful diagram of pointed etale algebras in any universe containing the base.
Source: Stacks Project, Tag 04GW (blueprint: def-sc-ring-strict-henselization). -/
def strictHenselizationPointedDiagramIn (A : Type u) (K : Type (max u v))
    [CommRing A] [CommRing K] [Algebra A K] :
    (ObjectProperty.FullSubcategory
      (fun S : Over (CommAlgCat.of A K) ↦ Etale A S.left)) ⥤
        CommAlgCat.{max u v} A :=
  ObjectProperty.ι (fun S : Over (CommAlgCat.of A K) ↦ Etale A S.left) ⋙
    Over.forget (CommAlgCat.of A K)

/-- The cocone of pointings to the residue separable closure in the enlarged universe.
Source: Stacks Project, Tag 04GW (blueprint: def-sc-ring-strict-henselization). -/
def strictHenselizationPointingCoconeIn (A : Type u) (K : Type (max u v))
    [CommRing A] [CommRing K] [Algebra A K] :
    Cocone (strictHenselizationPointedDiagramIn.{u, v} A K) where
  pt := CommAlgCat.of A K
  ι := {
    app := fun S ↦ S.obj.hom
    naturality := fun _S _T f ↦ Over.w f.hom }

/-- A specified universal pointed-etale colimit presenting a strict henselization.
The base ring is in `Type u`; all diagram algebras, `K` and `H` are in `Type (max u v)`.
This generalizes `StrictHenselizationPresentation` without changing its defining data.
Source: Stacks Project, Tag 04GW (blueprint: def-sc-ring-strict-henselization). -/
structure StrictHenselizationPresentationIn (A : Type u) (K H : Type (max u v))
    [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing H] [Algebra A H] where
  /-- The cocone on the defining pointed-etale diagram. -/
  cocone : Cocone (strictHenselizationPointedDiagramIn.{u, v} A K)
  /-- Its universal property. -/
  isColimit : IsColimit cocone
  /-- The specified algebra identification with the strict henselization. -/
  identification : cocone.pt ≅ CommAlgCat.of A H

/-- The residue map obtained by descending the pointings of the specified presentation.
Source: Stacks Project, Tag 04GW (blueprint: def-sc-ring-strict-henselization). -/
noncomputable def StrictHenselizationPresentationIn.residueMap
    {A : Type u} {K H : Type (max u v)} [CommRing A] [IsLocalRing A]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing H] [Algebra A H] (P : StrictHenselizationPresentationIn.{u, v} A K H) :
    H →+* K :=
  (P.identification.inv ≫
    P.isColimit.desc (strictHenselizationPointingCoconeIn.{u, v} A K)).hom.toRingHom

end Algebra
