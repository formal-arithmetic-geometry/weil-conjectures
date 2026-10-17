/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange
import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
import all Sheaf.Paper.CondensedOpenClosedRecollement

/-!
# Underived cartesian support for module-object extension by zero

Source: Stacks Project, Tag 03DI, and the cartesian extension-by-zero calculation in
`lem-cbc-proetale-extension-zero-base-change`.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option backward.isDefEq.respectTransparency false in
private theorem module_support_of_underlying
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z : Scheme.{u}}
    (i : X ⟶ Z) [IsOpenImmersion i]
    (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (hN : (ProEtale.openImmersionLowerShriek Ab.{u + 1} i).essImage N.X) :
    (openImmersionLowerShriek Λ i).essImage N := by
  let a := ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} i
  have : IsIso a.unit := by
    let a₀ := ProEtale.openImmersionLowerShriekAdjunction Ab.{u + 1} i
    have : IsIso a₀.unit :=
      (ProEtale.openImmersionAdjunctionTriple Ab.{u + 1} i).isIso_unit_iff_isIso_counit.mpr
        (ProEtale.isIso_openImmersionRestrictionLowerStarAdjunction_counit Ab.{u + 1} i)
    have := a₀.fullyFaithfulLOfIsIsoUnit.full
    have := a₀.fullyFaithfulLOfIsIsoUnit.faithful
    exact a.unit_isIso_of_L_fully_faithful
  have := a.fullyFaithfulLOfIsIsoUnit.full
  have := a.fullyFaithfulLOfIsIsoUnit.faithful
  have : IsIso (a.counit.app N.X) := (a.isIso_counit_app_iff_mem_essImage).2 hN
  let al := linearOpenImmersionLowerShriekAdjunction Λ i
  have hlin : IsIso (al.counit.app N) := by
    have hh : IsIso ((Mod.forget _).map (al.counit.app N)) := by
      dsimp [al, linearOpenImmersionLowerShriekAdjunction, Adjunction.mapModLeftAdjunction,
        Adjunction.mkOfHomEquiv, Adjunction.mk', Mod.forget, Mod.Hom.mk']
      rw [Adjunction.homEquiv_counit]
      simp only [Mod.id_hom']
      erw [CategoryTheory.Functor.map_id, Category.id_comp]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  let ec := Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ i)
  refine ⟨ec.inverse.obj ((ProEtale.upperStar Ab.{u + 1} i).mapMod
      (condensedRingObj Λ Z) |>.obj N), ⟨?_⟩⟩
  exact (linearOpenImmersionLowerShriek Λ i).mapIso
      (ec.counitIso.app _) ≪≫ asIso (al.counit.app N)

set_option backward.isDefEq.respectTransparency false in
/-- Pulling an extension by zero across a cartesian refinement stays in the open image.
Source: Stacks Project, Tag 03DI (extension by zero on a localized site), and the
cartesian calculation of `lem-cbc-proetale-extension-zero-base-change`.
(blueprint: lem-sfb-module-open-refinement-support)

Proof: on abelian sheaves, the cartesian extension-by-zero isomorphism identifies
`h^* i₁!` with `i!`. Its maps commute with the coefficient actions: restriction of
the action to the open is the original action, and extension by zero carries that
action through the projection formula. The coefficient morphisms are isomorphisms
and satisfy composition, so restriction along them transports this isomorphism to
module objects over the pulled-back condensed ring. The inverse is linear by
cancelling the forward isomorphism. These constructions are natural in the module.
For an empty open both sides are zero; for an identity refinement this is the
identity identification. No properness or constructibility is needed. -/
theorem openImmersionLowerShriek_refinement_support
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z Z₁ : Scheme.{u}}
    {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁}
    [IsOpenImmersion i] [IsOpenImmersion i₁]
    (sq : IsPullback (𝟙 X) i i₁ h) :
    Nonempty (openImmersionLowerShriek Λ i₁ ⋙ upperStar Λ h ≅
      openImmersionLowerShriek Λ i) := by
  let ai := openImmersionLowerShriekUpperStarAdjunction Λ i
  let ai₁ := openImmersionLowerShriekUpperStarAdjunction Λ i₁
  have : IsIso ai.unit := openUnitIsIso Λ i
  have : IsIso ai₁.unit := openUnitIsIso Λ i₁
  have := ai.fullyFaithfulLOfIsIsoUnit.full
  have := ai.fullyFaithfulLOfIsIsoUnit.faithful
  let F := openImmersionLowerShriek Λ i₁ ⋙ upperStar Λ h
  have hε (M) : IsIso (ai.counit.app (F.obj M)) := by
    apply ai.isIso_counit_app_iff_mem_essImage.mpr
    apply module_support_of_underlying Λ i
    let ef : (upperStar Λ h ⋙ Mod.forget (condensedRingObj Λ Z)) ≅
        Mod.forget (condensedRingObj Λ Z₁) ⋙ ProEtale.upperStar Ab.{u + 1} h :=
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft ((ProEtale.upperStar Ab.{u + 1} h).mapMod
          (condensedRingObj Λ Z₁))
          (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ h)))
        (Mod.forget (condensedRingObj Λ Z))
    refine ⟨(ProEtale.upperStar Ab.{u + 1} (𝟙 X)).obj M.X, ⟨?_⟩⟩
    exact (ProEtale.openImmersionLowerShriekBaseChangeIso Ab.{u + 1} sq).app M.X ≪≫
      (ef.app ((openImmersionLowerShriek Λ i₁).obj M)).symm
  have : IsIso (Functor.whiskerLeft F ai.counit) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hε
  have w : i ≫ h = i₁ := sq.toCommSq.w.symm.trans (Category.id_comp _)
  let et : upperStar Λ i₁ ≅ upperStar Λ h ⋙ upperStar Λ i :=
    eqToIso (congrArg (upperStar Λ) w.symm) ≪≫ upperStarComp Λ i h
  let ei : openImmersionLowerShriek Λ i ≅
      (openImmersionLowerShriek Λ i₁ ⋙ upperStar Λ i₁) ⋙
        openImmersionLowerShriek Λ i :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (asIso ai₁.unit) (openImmersionLowerShriek Λ i)
  let es : (openImmersionLowerShriek Λ i₁ ⋙ upperStar Λ i₁) ⋙
        openImmersionLowerShriek Λ i ≅
      F ⋙ (upperStar Λ i ⋙ openImmersionLowerShriek Λ i) :=
    Functor.squareTransport (G₁ := upperStar Λ i₁) (G₂ := 𝟭 _)
      (G₃ := upperStar Λ h) (G₄ := upperStar Λ i)
      (openImmersionLowerShriek Λ i₁)
      (openImmersionLowerShriek Λ i) ((Functor.rightUnitor (upperStar Λ i₁)) ≪≫ et)
  let ec : F ⋙ (upperStar Λ i ⋙ openImmersionLowerShriek Λ i) ≅ F :=
    asIso (Functor.whiskerLeft F ai.counit) ≪≫ Functor.rightUnitor F
  exact ⟨(ei ≪≫ es ≪≫ ec).symm⟩

end AlgebraicGeometry.ProEtale.CondensedRing
