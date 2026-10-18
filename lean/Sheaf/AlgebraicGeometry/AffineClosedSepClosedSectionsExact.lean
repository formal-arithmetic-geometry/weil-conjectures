/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import Sheaf.AlgebraicGeometry.AffineSepclosedEtaleAcyclic
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! # Exact sections on affine schemes with closed separably closed points
Source: Stacks Project, Tag 09AY; cohomology.tex, Tag 015B.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The acyclicity theorem makes the constant integer sheaf projective; its coyoneda
functor is global sections, so sections preserve finite colimits.
Source: Stacks Project, Tag 09AY and the projective criterion Ext¹(Z,-)=0.
(blueprint: lem-weil-pbc-affine-closed-sepclosed-sections-exact).
Proof: H¹(T,F)=Ext¹(Z,F) vanishes by affine closed-point acyclicity. The Ext criterion
therefore makes the constant integer sheaf projective. Preadditive coyoneda from a
projective object preserves finite colimits. The constant-sheaf/global-sections
adjunction identifies that coyoneda functor with Γ followed by Hom(Z,-); evaluation
at 1 identifies Hom(Z,-) with the identity on abelian groups. Transport the finite
colimit preservation across these natural isomorphisms. -/
theorem affineClosedSepClosed_sections_preservesFiniteColimits
    (T : Scheme.{u}) [IsAffine T]
    (hclosed : ∀ t : T, IsClosed ({t} : Set T))
    (hsep : ∀ t : T, IsSepClosed (T.residueField t)) :
    PreservesFiniteColimits (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}) := by
  let J := T.smallEtaleTopology
  let Z : AddCommGrpCat.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let ZT : Sheaf J AddCommGrpCat.{u + 1} :=
    (constantSheaf J AddCommGrpCat.{u + 1}).obj Z
  have : Projective ZT := projective_iff_subsingleton_ext_one.mpr fun {F} ↦
    subsingleton_H_of_affine_closed_isSepClosed T hclosed hsep F 1 (by decide)
  let eZ : preadditiveCoyoneda.{u + 1}.obj (op Z) ≅ 𝟭 AddCommGrpCat.{u + 1} :=
    NatIso.ofComponents (fun A ↦ (AddCommGrpCat.uliftZMultiplesAddEquiv A).toAddCommGrpIso)
      (fun g ↦ by ext x; rfl)
  have : PreservesFiniteColimits (preadditiveCoyonedaObj ZT) :=
    preservesFiniteColimits_preadditiveCoyonedaObj_of_projective ZT
  have : PreservesFiniteColimits
      (forget₂ (ModuleCat.{u + 1} (End ZT)ᵐᵒᵖ) AddCommGrpCat.{u + 1}) :=
    ⟨fun I _ _ ↦ ModuleCat.forget₂PreservesColimitsOfShape.{u + 1} (End ZT)ᵐᵒᵖ I⟩
  have : PreservesFiniteColimits (preadditiveCoyoneda.{u + 1}.obj (op ZT)) :=
    comp_preservesFiniteColimits (preadditiveCoyonedaObj ZT)
      (forget₂ (ModuleCat.{u + 1} (End ZT)ᵐᵒᵖ) AddCommGrpCat.{u + 1})
  let e : preadditiveCoyoneda.{u + 1}.obj (op ZT) ≅
      Sheaf.Γ J AddCommGrpCat.{u + 1} :=
    (constantSheafΓAdj J AddCommGrpCat.{u + 1}).preadditiveCoyonedaObjIso Z ≪≫
    Functor.isoWhiskerLeft (Sheaf.Γ J AddCommGrpCat.{u + 1}) eZ ≪≫ Functor.rightUnitor _
  exact preservesFiniteColimits_of_natIso e

end AlgebraicGeometry.Scheme
