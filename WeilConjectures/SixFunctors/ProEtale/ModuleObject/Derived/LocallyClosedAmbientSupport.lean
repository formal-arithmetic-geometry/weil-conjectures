/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # The ambient locally closed support adjoint -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The ambient support right adjoint and its internal-Hom formula.
Source: the internal-Hom stability proof, support formula; open and closed internal-Hom
adjunctions. Compose the closed support adjunction with open restriction. The exact closed
pushforward is its own derived functor. Apply the closed internal-Hom formula, then the
open formula inside the closed direct image, and finally compose derived direct images.
(blueprint: lem-sfb-locally-closed-ambient-support).
-/
theorem locallyClosed_ambient_support {X S Z : Scheme.{u}} [IsLocallyNoetherian X]
    (a : S ⟶ X) (j : S ⟶ Z) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i] (ha : a = j ≫ i) :
    let F := (openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
      (lowerStar Λ i).rightDerivedFunctor
    ∃ R : DerivedCategory (supportModules Λ X) ⥤ DerivedCategory (supportModules Λ S),
      Nonempty (F ⊣ R) ∧
      ∀ (P : DerivedCategory (supportModules Λ S))
        (L : DerivedCategory (supportModules Λ X)),
      Nonempty (((derivedHom Λ X).obj (op (F.obj P))).obj L ≅
        (lowerStar Λ a).rightDerivedFunctor.obj
          (((derivedHom Λ S).obj (op P)).obj (R.obj L))) := by
  let V : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let v := V.ι
  have hiv : Set.range i.base = (Set.range v.base)ᶜ := by
    change Set.range i.base = (Set.range V.ι.base)ᶜ
    rw [Scheme.Opens.range_ι]
    exact (compl_compl _).symm
  let := closedSupport_lowerStarExact Λ i v hiv
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  let C : TopologicalSpace.Closeds Z :=
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let J := Scheme.IdealSheafData.vanishingIdeal C
  let ci := J.subschemeι
  have hcj : Set.range ci.base = (Set.range j.base)ᶜ := by
    change Set.range J.subschemeι = _
    rw [J.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal C
  let R := (closedSupport Λ i v).rightDerivedFunctor ⋙
    (supportPullback Λ j).mapDerivedCategory
  let e := (lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory
  refine ⟨R, ⟨?_⟩, ?_⟩
  · exact ((openSupportDerivedAdjunction Λ j).comp
      (closedSupportDerivedAdjunction Λ i v hiv)).ofNatIsoLeft
        (Functor.isoWhiskerLeft (openImmersionLowerShriek Λ j).mapDerivedCategory e.symm)
  · intro P L
    obtain ⟨_, _, closed, _⟩ := openClosedInternalHomFormulas Λ i v hiv
    obtain ⟨_, opened, _, _⟩ := openClosedInternalHomFormulas Λ ci j hcj
    let E := (openImmersionLowerShriek Λ j).mapDerivedCategory.obj P
    let H := ((derivedHom Λ S).obj (op P)).obj (R.obj L)
    refine ⟨(((derivedHom Λ X).mapIso (e.symm.app E).op).app L) ≪≫
      closed E L ≪≫
      (lowerStar Λ i).mapDerivedCategory.mapIso
        (opened P ((closedSupport Λ i v).rightDerivedFunctor.obj L)) ≪≫
      (e.app ((lowerStar Λ j).rightDerivedFunctor.obj H)).symm ≪≫
      (rightDerivedLowerStarComp Λ j i).app H ≪≫ ?_⟩
    exact (eqToIso (congrArg (fun f ↦ (lowerStar Λ f).rightDerivedFunctor) ha.symm)).app H
end AlgebraicGeometry.ProEtale.CondensedRing
