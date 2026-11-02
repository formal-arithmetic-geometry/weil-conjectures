/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientSourcePullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalIntegralBoundaryPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalBaseChangeCartesian
import WeilConjectures.AlgebraicGeometry.IntegralSourceExchange.DiagonalIntegralSourceExchange
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClosedExchangeTranspose
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-! # The supported integral generator under geometric pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem condensedPushforward_unit
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S) :
    η[condensedRingObj R S] ≫ condensedPushforwardHom R f =
      Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} f) ≫
        (lowerStar Ab.{u + 1} f).map η[condensedRingObj R X] := by
  have h := IsMonHom.one_hom (condensedPushforwardHom R f)
  conv at h =>
    rhs
    rw [Functor.obj.η_def (F := lowerStar Ab.{u + 1} f) (condensedRingObj R X)]
  exact h


private theorem constantDirect_unit {X S : Scheme.{u}} (f : X ⟶ S) :
    Scheme.proEtaleConstantDirectImageMap f Ab.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
      Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} f) := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology S) Ab.{u + 1}).homEquiv
    ((Functor.const S.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) _).injective
  rw [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit]
  have hε (T : Scheme.{u}) :
      Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}) =
        (sheafificationAdjunction (Scheme.ProEt.topology T) Ab.{u + 1}).unit.app
          (𝟙_ (T.ProEtᵒᵖ ⥤ Ab.{u + 1})) := by
    change _ ≫ (sheafToPresheaf _ _).map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  apply NatTrans.ext
  funext V
  have h := Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (Scheme.proEtaleBaseChange f) Ab.{u + 1}
    (Scheme.ProEt.topology S) (Scheme.ProEt.topology X) V
  simpa only [hε, NatTrans.comp_app, Functor.whiskerLeft_app] using! h.symm


private def condensedDirectSquare
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) :
    CondensedRing.lowerStar R hX ⋙ CondensedRing.lowerStar R f ≅
      CondensedRing.lowerStar R f' ⋙ CondensedRing.lowerStar R hS :=
  CondensedRing.lowerStarComp R hX f ≪≫ CondensedRing.lowerStarCongr R h.symm ≪≫
    (CondensedRing.lowerStarComp R f' hS).symm


set_option maxHeartbeats 800000 in
-- The canonical conjugate compares the two composite geometric adjunctions.
private theorem condensedSquare_conjugate
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) :
    conjugateEquiv
      ((CondensedRing.upperStarLowerStarAdjunction R f).comp
        (CondensedRing.upperStarLowerStarAdjunction R hX))
      ((CondensedRing.upperStarLowerStarAdjunction R hS).comp
        (CondensedRing.upperStarLowerStarAdjunction R f'))
      (((CondensedRing.upperStarComp R f' hS).symm ≪≫
        CondensedRing.upperStarCongr R h ≪≫ CondensedRing.upperStarComp R hX f).hom) =
      (condensedDirectSquare R f f' hX hS h).hom := by
  rw [← conjugateIsoEquiv_apply_hom,
    conjugateIsoEquiv_trans _ (CondensedRing.upperStarLowerStarAdjunction R (f' ≫ hS)) _,
    conjugateIsoEquiv_trans _ (CondensedRing.upperStarLowerStarAdjunction R (hX ≫ f)) _]
  simp only [conjugateIsoEquiv_iso_symm,
    CondensedRing.conjugateIsoEquiv_upperStarComp,
    CondensedRing.conjugateIsoEquiv_upperStarCongr,
    condensedDirectSquare, CondensedRing.lowerStarCongr_symm, Iso.trans_assoc]


private def sourceDirectSquare
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (h : diagonalImmersion Y' ≫ baseW g = baseP g ≫ diagonalImmersion Y) :
    CondensedRing.lowerStar R (baseP g) ⋙
        CondensedRing.lowerStar R (diagonalImmersion Y) ≅
      CondensedRing.lowerStar R (diagonalImmersion Y') ⋙
        CondensedRing.lowerStar R (baseW g) :=
  condensedDirectSquare R (diagonalImmersion Y) (diagonalImmersion Y') (baseP g) (baseW g) h


private theorem sourceSquare_conjugate
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (h : diagonalImmersion Y' ≫ baseW g = baseP g ≫ diagonalImmersion Y) :
    conjugateEquiv
      ((CondensedRing.upperStarLowerStarAdjunction R (diagonalImmersion Y)).comp
        (CondensedRing.upperStarLowerStarAdjunction R (baseP g)))
      ((CondensedRing.upperStarLowerStarAdjunction R (baseW g)).comp
        (CondensedRing.upperStarLowerStarAdjunction R (diagonalImmersion Y')))
      (((CondensedRing.upperStarComp R (diagonalImmersion Y') (baseW g)).symm ≪≫
        CondensedRing.upperStarCongr R h ≪≫
        CondensedRing.upperStarComp R (baseP g) (diagonalImmersion Y)).hom) =
      (sourceDirectSquare R g h).hom := by
  exact condensedSquare_conjugate R (diagonalImmersion Y) (diagonalImmersion Y')
    (baseP g) (baseW g) h


private theorem lowerStarCongr_symm_ab {X S : Scheme.{u}} {f g : X ⟶ S} (h : f = g) :
    (lowerStarCongr Ab.{u + 1} h).symm = lowerStarCongr Ab.{u + 1} h.symm := by
  subst g
  rfl


private def abelianDirectSquare
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) :
    lowerStar Ab.{u + 1} hX ⋙ lowerStar Ab.{u + 1} f ≅
      lowerStar Ab.{u + 1} f' ⋙ lowerStar Ab.{u + 1} hS :=
  lowerStarComp Ab.{u + 1} hX f ≪≫ lowerStarCongr Ab.{u + 1} h.symm ≪≫
    (lowerStarComp Ab.{u + 1} f' hS).symm


set_option maxHeartbeats 800000 in
-- The canonical conjugate compares the two composite geometric adjunctions.
private theorem abelianSquare_conjugate
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) :
    conjugateEquiv
      ((upperStarLowerStarAdjunction Ab.{u + 1} f).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} hX))
      ((upperStarLowerStarAdjunction Ab.{u + 1} hS).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} f'))
      (((upperStarComp Ab.{u + 1} f' hS).symm ≪≫
        upperStarCongr Ab.{u + 1} h ≪≫ upperStarComp Ab.{u + 1} hX f).hom) =
      (abelianDirectSquare f f' hX hS h).hom := by
  rw [← conjugateIsoEquiv_apply_hom,
    conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction Ab.{u + 1} (f' ≫ hS)) _,
    conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction Ab.{u + 1} (hX ≫ f)) _]
  simp only [conjugateIsoEquiv_iso_symm,
    conjugateIsoEquiv_upperStarComp,
    conjugateIsoEquiv_upperStarCongr,
    abelianDirectSquare, lowerStarCongr_symm_ab, Iso.trans_assoc]


private def abelianSourceDirectSquare
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (h : diagonalImmersion Y' ≫ baseW g = baseP g ≫ diagonalImmersion Y) :
    lowerStar Ab.{u + 1} (baseP g) ⋙ lowerStar Ab.{u + 1} (diagonalImmersion Y) ≅
      lowerStar Ab.{u + 1} (diagonalImmersion Y') ⋙ lowerStar Ab.{u + 1} (baseW g) :=
  abelianDirectSquare (diagonalImmersion Y) (diagonalImmersion Y') (baseP g) (baseW g) h


private theorem abelianSourceSquare_conjugate
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (h : diagonalImmersion Y' ≫ baseW g = baseP g ≫ diagonalImmersion Y) :
    conjugateEquiv
      ((upperStarLowerStarAdjunction Ab.{u + 1} (diagonalImmersion Y)).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} (baseP g)))
      ((upperStarLowerStarAdjunction Ab.{u + 1} (baseW g)).comp
        (upperStarLowerStarAdjunction Ab.{u + 1} (diagonalImmersion Y')))
      (((upperStarComp Ab.{u + 1} (diagonalImmersion Y') (baseW g)).symm ≪≫
        upperStarCongr Ab.{u + 1} h ≪≫
        upperStarComp Ab.{u + 1} (baseP g) (diagonalImmersion Y)).hom) =
      (abelianSourceDirectSquare g h).hom := by
  exact abelianSquare_conjugate (diagonalImmersion Y) (diagonalImmersion Y')
    (baseP g) (baseW g) h


private theorem exchangeRight_comp
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {I : B ⥤ A} {RI : A ⥤ B} {W : A ⥤ C}
    {V : B ⥤ D} {J : D ⥤ C} {RJ : C ⥤ D}
    (aI : I ⊣ RI) (aJ : J ⊣ RJ) (s : V ⋙ J ≅ I ⋙ W)
    (M : A) (N : C) (c : W.obj M ⟶ N) :
    (Adjunction.exchangeRight aI aJ s).app M ≫ RJ.map c =
      aJ.homEquiv _ _ (s.hom.app (RI.obj M) ≫ W.map (aI.counit.app M) ≫ c) := by
  simp only [Adjunction.exchangeRight_app, Adjunction.homEquiv_unit,
    CategoryTheory.Functor.map_comp, Category.assoc]


private theorem exchangeRight_transpose
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {I : B ⥤ A} {RI : A ⥤ B} {W : A ⥤ C} {RW : C ⥤ A}
    {V : B ⥤ D} {RV : D ⥤ B} {J : D ⥤ C} {RJ : C ⥤ D}
    (aI : I ⊣ RI) (aW : W ⊣ RW) (aV : V ⊣ RV) (aJ : J ⊣ RJ)
    (s : V ⋙ J ≅ I ⋙ W) (d : RW ⋙ RI ≅ RJ ⋙ RV)
    (hs : conjugateEquiv (aI.comp aW) (aV.comp aJ) s.hom = d.hom)
    (M : A) (N : C) (c : W.obj M ⟶ N) :
    aV.homEquiv _ _ ((Adjunction.exchangeRight aI aJ s).app M ≫ RJ.map c) =
      RI.map (aW.homEquiv _ _ c) ≫ d.hom.app N := by
  rw [exchangeRight_comp]
  exact diagonalClosedExchange_transpose aI aW aV aJ s d hs M N c


private theorem constantInverse_transpose {X S : Scheme.{u}} (f : X ⟶ S) :
    (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _
        (Scheme.proEtaleConstantInverseImageMap f Ab.{u + 1}
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) =
      Scheme.proEtaleConstantDirectImageMap f Ab.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  change (Scheme.proEtaleSheafAdjunction f Ab.{u + 1}).homEquiv _ _ _ = _
  rw [Scheme.proEtaleConstantInverseImageMap, ← Adjunction.homEquiv_counit,
    Equiv.apply_symm_apply]


attribute [local irreducible] CondensedRing.upperStarLowerStarAdjunction
  upperStarLowerStarAdjunction

-- The checked conversion procedure is adapted from the current proof in
-- DiagonalSupportedPullbackScalarNormalization. It transports canonical instance
-- aliases by explicit equality proofs; every generated auxiliary is kernel checked.
universe v

open Lean Meta Elab Tactic in
open Lean Meta in
open Lean Meta in
open Lean Meta in
open Lean Meta Elab Tactic in
termination_by structural fuel


-- Elaborate and check an application while retaining its inferred proposition.
open Lean Meta Elab Term in
scoped elab "diagonal_congruence_term% " t:term : term => do
  let raw ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let raw := (← instantiateMVars raw).consumeMData
  if raw.hasMVar then throwError "Unresolved inferred comparison argument"
  let rebuild : StateRefT SupportedCongrState MetaM Expr := do
    let mut result := raw.getAppFn
    for arg in raw.getAppArgs do
      let ty ← whnf (← inferType result)
      unless ty.isForall do throwError "The comparison helper is not a function"
      let expected := ty.bindingDomain!
      let actual ← inferType arg
      let arg ← if actual == expected then pure arg else do
        let h ← mkEqOfHEq (← supportedNativeHEq actual expected)
        mkAppM ``Eq.mp #[h, arg]
      result := mkApp result arg
    return result
  let (proof, _) ← rebuild.run (← supportedLocalHEqs)
  if proof.hasSorry then throwError "Unfinished inferred comparison"
  return proof

-- Replace implicit definitional conversions at each application argument by
-- kernel-checked heterogeneous congruence, then transport the final proposition.
open Lean Meta Elab Tactic in
scoped elab "diagonal_congruence_exact " t:term : tactic => do
  withMainContext do
    let goal ← getMainGoal
    let raw ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let raw := (← instantiateMVars raw).consumeMData
    if raw.hasMVar then throwError "Unresolved unit proof arguments"
    let rebuild : StateRefT SupportedCongrState MetaM Expr := do
      let mut result := raw.getAppFn
      for arg in raw.getAppArgs do
        let ty ← whnf (← inferType result)
        unless ty.isForall do throwError "The unit helper is not a function"
        let expected := ty.bindingDomain!
        let actual ← inferType arg
        let mut arg := arg
        if actual != expected then
          let h ← mkEqOfHEq (← supportedNativeHEq actual expected)
          arg ← mkAppM ``Eq.mp #[h, arg]
        result := mkApp result arg
      let actual ← inferType result
      let expected ← instantiateMVars (← goal.getType)
      if expected.isMVar then
        unless ← isDefEq expected actual do
          throwError "The inferred comparison proposition does not match"
        pure result
      else
        let h ← mkEqOfHEq (← supportedNativeHEq actual expected)
        mkAppM ``Eq.mp #[h, result]
    let (proof, _) ← rebuild.run (← supportedLocalHEqs)
    if proof.hasSorry then throwError "Unfinished unit conversion proof"
    goal.assign proof
    replaceMainGoal []

-- Elaborate data arguments independently so Lean never normalizes a large
-- category-instance alias while inferring an application argument.
open Lean Meta Elab Term in
scoped elab "diagonal_congruence_apply% " f:term:max
    " arguments" "[" args:term,* "]" : term => do
  let mut result ← elabTerm f none
  synthesizeSyntheticMVarsNoPostponing
  result ← instantiateMVars result
  let mut state ← supportedLocalHEqs
  for stx in args.getElems do
    let arg ← elabTerm stx none
    synthesizeSyntheticMVarsNoPostponing
    let arg ← instantiateMVars arg
    let ty ← whnf (← inferType result)
    unless ty.isForall do throwError "The checked application expected a function"
    let actual ← instantiateMVars (← inferType arg)
    let mut expected ← instantiateMVars ty.bindingDomain!
    if expected.hasMVar then
      unless ← withTransparency .reducible (isDefEq actual expected) do
        throwError "Specify the implicit objects of the checked application"
      expected ← instantiateMVars expected
    if actual.hasMVar || expected.hasMVar then
      throwError "Unresolved checked application argument type"
    let cast : StateRefT SupportedCongrState MetaM Expr := do
      if actual == expected then return arg
      let h ← mkEqOfHEq (← supportedNativeHEq actual expected)
      mkAppM ``Eq.mp #[h, arg]
    let (arg, next) ← cast.run state
    state := next
    result := mkApp result arg
  synthesizeSyntheticMVarsNoPostponing
  result ← instantiateMVars result
  if result.hasMVar || result.hasSorry then
    throwError "Unfinished checked application"
  return result

-- Rebuild proof applications with checked casts at their argument boundaries.
open Lean Meta Elab Tactic in
termination_by structural fuel

open Lean Meta Elab Tactic in
scoped elab "diagonal_checked_exact " t:term : tactic => withMainContext do
  let goal ← getMainGoal
  let expected ← goal.getType
  let raw ← Term.elabTerm t (some expected)
  Term.synthesizeSyntheticMVarsNoPostponing
  let raw ← instantiateMVars raw
  if raw.hasMVar then throwError "unresolved checked proof argument"
  let (proof, _) ← (do
    let proof ← supportedRebuildProof raw
    let actual ← inferType proof
    let h ← mkEqOfHEq (← supportedNativeHEq actual expected)
    mkAppM ``Eq.mp #[h, proof]).run (← supportedLocalHEqs)
  if proof.hasSorry then throwError "unfinished checked proof"
  goal.assign proof
  replaceMainGoal []

set_option maxHeartbeats 2000000 in
-- The four concrete adjunctions share their canonical composition comparisons.
private theorem sourcePullbackMap_transpose
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (h : diagonalImmersion Y' ≫ baseW g = baseP g ≫ diagonalImmersion Y)
    (c : UnitPullEndpoint R (baseP g)) :
    (CondensedRing.upperStarLowerStarAdjunction R (baseW g)).homEquiv
        (source R Y) (source R Y') (sourcePullbackMap R g h c) =
      (CondensedRing.lowerStar R (diagonalImmersion Y)).map
          ((CondensedRing.upperStarLowerStarAdjunction R (baseP g)).homEquiv
            (Mod.regular (condensedRingObj R (ProjectiveLine Y)))
            (Mod.regular (condensedRingObj R (ProjectiveLine Y'))) c.iso.hom) ≫
        (sourceDirectSquare R g h).hom.app
          (Mod.regular (condensedRingObj R (ProjectiveLine Y'))) := by
  unfold sourcePullbackMap ordinaryExchange
  diagonal_congruence_exact (exchangeRight_transpose
      (A := Modules R (ProjectiveLine Y)) (B := Modules R (diagonalSurface Y))
      (C := Modules R (ProjectiveLine Y')) (D := Modules R (diagonalSurface Y'))
      (I := CondensedRing.upperStar R (diagonalImmersion Y))
      (RI := CondensedRing.lowerStar R (diagonalImmersion Y))
      (W := CondensedRing.upperStar R (baseP g))
      (RW := CondensedRing.lowerStar R (baseP g))
      (V := CondensedRing.upperStar R (baseW g))
      (RV := CondensedRing.lowerStar R (baseW g))
      (J := CondensedRing.upperStar R (diagonalImmersion Y'))
      (RJ := CondensedRing.lowerStar R (diagonalImmersion Y'))
      (CondensedRing.upperStarLowerStarAdjunction R (diagonalImmersion Y))
      (CondensedRing.upperStarLowerStarAdjunction R (baseP g))
      (CondensedRing.upperStarLowerStarAdjunction R (baseW g))
      (CondensedRing.upperStarLowerStarAdjunction R (diagonalImmersion Y'))
      ((CondensedRing.upperStarComp R (diagonalImmersion Y') (baseW g)).symm ≪≫
        CondensedRing.upperStarCongr R h ≪≫
        CondensedRing.upperStarComp R (baseP g) (diagonalImmersion Y))
      (sourceDirectSquare R g h) (sourceSquare_conjugate R g h)
      (Mod.regular (condensedRingObj R (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj R (ProjectiveLine Y'))) c.iso.hom)


private theorem coefficientUnit_transpose
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S)
    (c : UnitPullEndpoint R f) :
    ((CondensedRing.upperStarLowerStarAdjunction R f).homEquiv
      (Mod.regular (condensedRingObj R S))
      (Mod.regular (condensedRingObj R X)) c.iso.hom).hom =
      condensedPushforwardHom R f := by
  calc
    _ = (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv
        (condensedRingObj R S) (condensedRingObj R X) (condensedPullbackHom R f) :=
      c.normalization
    _ = _ := by
      rw [Adjunction.homEquiv_unit]
      exact unitAlgHom_comp_map_condensedPullbackHom R f



private theorem lowerStarComp_inv_ab
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (N : Modules R X) :
    ((CondensedRing.lowerStarComp R f g).inv.app N).hom =
      (lowerStarComp Ab.{u + 1} f g).inv.app N.X := by
  apply (cancel_mono ((lowerStarComp Ab.{u + 1} f g).hom.app N.X)).mp
  rw [← CondensedRing.lowerStarComp_hom_app_hom R f g N]
  change (((CondensedRing.lowerStarComp R f g).inv.app N) ≫
    (CondensedRing.lowerStarComp R f g).hom.app N).hom = _
  rw [Iso.inv_hom_id_app, Mod.id_hom']
  rw [CondensedRing.lowerStarComp_hom_app_hom, Iso.inv_hom_id_app]
  rfl


set_option maxHeartbeats 2000000 in
-- Check explicit instance transports in this concrete comparison.
private theorem directSquare_ab
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) (N : Modules R X') :
    ((condensedDirectSquare R f f' hX hS h).hom.app N).hom =
      (abelianDirectSquare f f' hX hS h).hom.app N.X := by
  diagonal_checked_exact (by
    simp only [condensedDirectSquare, abelianDirectSquare, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Mod.comp_hom', lowerStarComp_inv_ab,
      CondensedRing.lowerStarCongr_hom_app_hom, CondensedRing.lowerStarComp_hom_app_hom])


set_option maxHeartbeats 2000000 in
-- Check explicit instance transports in this concrete comparison.
private theorem boundarySource_transpose {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (h : diagonalImmersion Y' ≫ baseW g = baseP g ≫ diagonalImmersion Y) :
    (upperStarLowerStarAdjunction Ab.{u + 1} (baseW g)).homEquiv
        (diagonalIntegralSource Y) (diagonalIntegralSource Y')
        (diagonalBoundarySource (baseW g) (baseP g)
          (diagonalBaseChange_cartesian g).toCommSq) =
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (Scheme.proEtaleConstantDirectImageMap (baseP g) Ab.{u + 1}
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
        (abelianSourceDirectSquare g h).hom.app
          (IntegralSourceExchange.integralConstant (ProjectiveLine Y')) := by
  diagonal_checked_exact (by
    let sa := (upperStarComp Ab.{u + 1} (diagonalImmersion Y') (baseW g)).symm ≪≫
      upperStarCongr Ab.{u + 1} h ≪≫
        upperStarComp Ab.{u + 1} (baseP g) (diagonalImmersion Y)
    have ha := diagonalClosedExchange_transpose
      (upperStarLowerStarAdjunction Ab.{u + 1} (diagonalImmersion Y))
      (upperStarLowerStarAdjunction Ab.{u + 1} (baseP g))
      (upperStarLowerStarAdjunction Ab.{u + 1} (baseW g))
      (upperStarLowerStarAdjunction Ab.{u + 1} (diagonalImmersion Y'))
      sa (abelianSourceDirectSquare g h) (abelianSourceSquare_conjugate g h)
      (IntegralSourceExchange.integralConstant (ProjectiveLine Y))
      (IntegralSourceExchange.integralConstant (ProjectiveLine Y'))
      (Scheme.proEtaleConstantInverseImageMap (baseP g) Ab.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    rw [constantInverse_transpose] at ha
    rw [IntegralSourceExchange.diagonalBoundarySource_exchange]
    simpa only [IntegralSourceExchange.integralExchange,
      IntegralSourceExchange.integralSquare, IntegralSourceExchange.integralConstant,
      sa, upperStarCongr] using! ha)


attribute [local semireducible] CondensedRing.upperStarLowerStarAdjunction
  upperStarLowerStarAdjunction

private theorem supportedGenerator_naturality
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (I : A ⥤ B) (W : C ⥤ A) (J : C ⥤ D) (V : D ⥤ B)
    {L : B ⥤ D} (adj : L ⊣ V) (d : W ⋙ I ≅ J ⋙ V)
    {Z M : A} {Z' M' : C}
    (unitMap : Z ⟶ M) (unitMap' : Z' ⟶ M') (p : M ⟶ W.obj M') (z : Z ⟶ W.obj Z')
    (b : L.obj (I.obj Z) ⟶ J.obj Z') (k : I.obj M ⟶ V.obj (J.obj M'))
    (hk : k = I.map p ≫ d.hom.app M')
    (hb : adj.homEquiv (I.obj Z) (J.obj Z') b = I.map z ≫ d.hom.app Z')
    (hunitMap : unitMap ≫ p = z ≫ W.map unitMap') :
    I.map unitMap ≫ k = adj.homEquiv (I.obj Z) (J.obj M') (b ≫ J.map unitMap') := by
  rw [hk, Adjunction.homEquiv_naturality_right, hb]
  rw [← I.map_comp_assoc, hunitMap, I.map_comp, Category.assoc]
  have hn := d.hom.naturality unitMap'
  dsimp only [Functor.comp_map] at hn
  rw [hn, Category.assoc]


set_option maxHeartbeats 2000000 in
-- Check the concrete coefficient-instance conversions explicitly.
private theorem sourcePullbackMap_hom_transpose
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (h : diagonalImmersion Y' ≫ baseW g = baseP g ≫ diagonalImmersion Y)
    (c : UnitPullEndpoint R (baseP g)) :
    (((CondensedRing.upperStarLowerStarAdjunction R (baseW g)).homEquiv
      (source R Y) (source R Y')) (sourcePullbackMap R g h c)).hom =
      ((CondensedRing.lowerStar R (diagonalImmersion Y)).map
          ((CondensedRing.upperStarLowerStarAdjunction R (baseP g)).homEquiv
            (Mod.regular (condensedRingObj R (ProjectiveLine Y)))
            (Mod.regular (condensedRingObj R (ProjectiveLine Y'))) c.iso.hom) ≫
        (sourceDirectSquare R g h).hom.app
          (Mod.regular (condensedRingObj R (ProjectiveLine Y')))).hom := by
  diagonal_congruence_exact (congrArg
    (fun t : (source R Y) ⟶ (CondensedRing.lowerStar R (baseW g)).obj (source R Y') ↦
      t.hom) (sourcePullbackMap_transpose R g h c))


set_option maxHeartbeats 2000000 in
-- Check the concrete coefficient-instance conversions explicitly.
private theorem sourcePullbackMap_ab_transpose
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (h : diagonalImmersion Y' ≫ baseW g = baseP g ≫ diagonalImmersion Y)
    (c : UnitPullEndpoint R (baseP g)) :
    (((CondensedRing.upperStarLowerStarAdjunction R (baseW g)).homEquiv
      (source R Y) (source R Y')) (sourcePullbackMap R g h c)).hom =
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
          (condensedPushforwardHom R (baseP g)) ≫
        (abelianSourceDirectSquare g h).hom.app
          (condensedRingObj R (ProjectiveLine Y')) := by
  diagonal_checked_exact (by
    have hk := sourcePullbackMap_hom_transpose R g h c
    simpa only [Mod.comp_hom', CondensedRing.lowerStar_map_hom,
      coefficientUnit_transpose R (baseP g) c, sourceDirectSquare,
      directSquare_ab] using! hk)


set_option maxHeartbeats 2000000 in
-- Check the concrete coefficient-instance conversions explicitly.
private theorem boundarySource_unit_transpose {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (h : diagonalImmersion Y' ≫ baseW g = baseP g ≫ diagonalImmersion Y) :
    (upperStarLowerStarAdjunction Ab.{u + 1} (baseW g)).homEquiv
        (diagonalIntegralSource Y) (diagonalIntegralSource Y')
        (diagonalBoundarySource (baseW g) (baseP g)
          (diagonalBaseChange_cartesian g).toCommSq) =
      (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
          (Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} (baseP g))) ≫
        (abelianSourceDirectSquare g h).hom.app
          (IntegralSourceExchange.integralConstant (ProjectiveLine Y')) := by
  diagonal_checked_exact (by
    have hb := boundarySource_transpose g h
    rw [constantDirect_unit] at hb
    exact hb)


set_option maxHeartbeats 8000000 in
-- The concrete comparisons contain composite adjunctions and two coefficient categories.
/-- The ordinary supported coefficient endpoint preserves the integral generator.

Source: blueprint latest, diagonal coefficient changes (3), closed-source exchange.
(blueprint: lem-diagonal-supported-generator-pullback).

Proof: transpose the closed exchange around the other pair of adjunctions. The
result is the closed direct image of the normalized coefficient-unit adjunct,
followed by the canonical direct-image square. On underlying sheaves the latter
is the abelian direct-image square. The coefficient adjunct preserves the
monoidal unit, hence the integral generator. The integral boundary source has
the same direct-image transpose by the site-comparison exchange equation.
Naturality of the direct-image square then gives the claimed equality. -/
theorem diagonalSupportedGenerator_pullback
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (b : BaseSquares g) (c : UnitPullEndpoint R (baseP g)) :
    (lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        η[condensedRingObj R (ProjectiveLine Y)] ≫
      (((CondensedRing.upperStarLowerStarAdjunction R (baseW g)).homEquiv
        (source R Y) (source R Y')) (sourcePullbackMap R g b.diagonal_square c)).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} (baseW g)).homEquiv
        (diagonalIntegralSource Y)
        ((lowerStar Ab.{u + 1} (diagonalImmersion Y')).obj
          (condensedRingObj R (ProjectiveLine Y')))
        (diagonalBoundarySource (baseW g) (baseP g)
          (diagonalBaseChange_cartesian g).toCommSq ≫
          (lowerStar Ab.{u + 1} (diagonalImmersion Y')).map
            η[condensedRingObj R (ProjectiveLine Y')]) := by
  diagonal_congruence_exact (supportedGenerator_naturality
    (lowerStar Ab.{u + 1} (diagonalImmersion Y))
    (lowerStar Ab.{u + 1} (baseP g))
    (lowerStar Ab.{u + 1} (diagonalImmersion Y'))
    (lowerStar Ab.{u + 1} (baseW g))
    (upperStarLowerStarAdjunction Ab.{u + 1} (baseW g))
    (abelianSourceDirectSquare g b.diagonal_square)
    η[condensedRingObj R (ProjectiveLine Y)]
    η[condensedRingObj R (ProjectiveLine Y')]
    (condensedPushforwardHom R (baseP g))
    (Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} (baseP g)))
    (diagonalBoundarySource (baseW g) (baseP g)
      (diagonalBaseChange_cartesian g).toCommSq)
    (((CondensedRing.upperStarLowerStarAdjunction R (baseW g)).homEquiv
      (source R Y) (source R Y')) (sourcePullbackMap R g b.diagonal_square c)).hom
    (sourcePullbackMap_ab_transpose R g b.diagonal_square c)
    (boundarySource_unit_transpose g b.diagonal_square)
    (condensedPushforward_unit R (baseP g)))

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
