/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeExceptionalForgetful.NativeExceptionalForgetfulData
public import WeilConjectures.AlgebraicGeometry.NativeWeilOpenProper.NativeOpenProperForgetting
public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomData
import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedCanonicalRightBoundary
import all WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomExactSequence

/-! # The ordinary graded Hom map of native compact support

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence, expanded by the finite-composite cyclic Hom sequence.
(blueprint: lem-sf-native-exceptional-hom-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor.IsoAlgebra
open WeilConjectures.AdicQbarRealization

attribute [local irreducible] DerivedCategory HasDerivedCategory.standard

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory

private theorem compose_functorial
    {A B C : CyclicDerivedSetting} (s : CyclicDerivedTransport A B)
    (t : CyclicDerivedTransport B C)
    (bA : CyclicDerivedHomBoundary A.action) (bB : CyclicDerivedHomBoundary B.action)
    (bC : CyclicDerivedHomBoundary C.action)
    (hs : CyclicDerivedHomBoundaryFunctorial A.action B.action bA bB
      s.native s.underlying s.shiftIso s.comparison)
    (ht : CyclicDerivedHomBoundaryFunctorial B.action C.action bB bC
      t.native t.underlying t.shiftIso t.comparison)
    (hb : ∀ M, DerivedCategory.TStructure.t.bounded M →
      DerivedCategory.TStructure.t.bounded (s.native.obj M)) :
    CyclicDerivedHomBoundaryFunctorial A.action C.action bA bC
      (s.comp t).native (s.comp t).underlying (s.comp t).shiftIso
        (s.comp t).comparison := by
  intro M N hM hN hJM hJN
  have hsMN := hs M N hM hN (hb M hM) (hb N hN)
  have htMN := ht (s.native.obj M) (s.native.obj N) (hb M hM) (hb N hN) hJM hJN
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    constructor
    · rw [transport_comp, (hsMN.1 r).1, (htMN.1 r).1]
      rfl
    · intro u v
      rw [transport_comp, (hsMN.1 r).2, (htMN.1 r).2, transport_comp, transport_comp]
      rfl
  · intro r u
    rw [transport_comp, hsMN.2.1, htMN.2.1, transport_comp]
    rfl
  · intro f
    rw [transport_comp, hsMN.2.2.1, htMN.2.2.1]
    rfl
  · intro u
    change t.native.map (s.native.map _) = _
    rw [hsMN.2.2.2, htMN.2.2.2, transport_comp]
    rfl

namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
variable {X Y : Space D} (f₀ : X.base ⟶ Y.base)
  [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]

/-- The compactification used by the native functor itself.
Source: LowerShriek.lean, derivedLowerShriek
(blueprint: lem-sf-native-exceptional-hom-transport). -/
abbrev counitCompactification :=
  HasCompactification.compactification f₀.left
    (hf := hasCompactification_of_over (k₀ := D.k₀) f₀.left)

/-- The actual ordinary open/proper functor for the chosen native compactification.
Source: NativeOpenProperForgetting.lean, ordinaryCompactSupport
(blueprint: lem-sf-native-exceptional-hom-transport). -/
abbrev counitOrdinaryShriek :=
  NativeWeilOpenProper.ordinaryCompactSupport (k₀ := D.k₀) (l := l) f₀.left
    (counitCompactification D f₀)

/-- The unit-normalized native forgetting comparison, restricted to Weil complexes.
Source: NativeOpenProperForgetting.lean, compactificationComparison
(blueprint: lem-sf-native-exceptional-hom-transport). -/
def counitForgetComparison :
    nativeShriek D l f₀ ⋙ WeilComplex.forget ≅
      WeilComplex.forget ⋙ counitOrdinaryShriek D l f₀ :=
  Functor.isoWhiskerLeft (WeilComplex.objectProperty D.k₀ l X.base.left).ι
    (NativeWeilOpenProper.compactificationComparison (k₀ := D.k₀) (l := l) f₀.left
      (counitCompactification D f₀))

/-- Transport of an ordinary degree-r morphism by the actual compact-support functor.
All comparisons are fixed constructions, independent of any exceptional counit.
Source: cyclicDerivedHomTransport and native open/proper forgetting
(blueprint: lem-sf-native-exceptional-hom-transport). -/
def counitHomTransport (K H : W D l X) (r : ℤ)
    (v : CyclicDerivedHom (WeilSheaf.frobeniusPullback D.k₀ l X.base.left) K.obj H.obj r) :
    CyclicDerivedHom (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left)
      ((nativeShriek D l f₀).obj K).obj ((nativeShriek D l f₀).obj H).obj r :=
  (counitForgetComparison D l f₀).hom.app K ≫
    (counitOrdinaryShriek D l f₀).map v ≫
    ((counitOrdinaryShriek D l f₀).commShiftIso r).hom.app
      ((WeilComplex.forget).obj H) ≫
    ((counitForgetComparison D l f₀).inv.app H)⟦r⟧'

private theorem compactification_functorial
    (bX : CyclicDerivedHomBoundary (WeilSheaf.frobeniusPullback D.k₀ l X.base.left))
    (bY : CyclicDerivedHomBoundary (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left))
    (hbX : CyclicDerivedHomBoundaryNatural _ bX ∧ CyclicDerivedHomBoundaryNormalized _ bX)
    (hbY : CyclicDerivedHomBoundaryNatural _ bY ∧ CyclicDerivedHomBoundaryNormalized _ bY) :
    CyclicDerivedHomBoundaryFunctorial
      (WeilSheaf.frobeniusPullback D.k₀ l X.base.left)
      (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left) bX bY
      (ProEtaleWeilSheaf.rightDerivedLowerShriek D.k₀ l f₀.left
        (counitCompactification D f₀))
      (counitOrdinaryShriek D l f₀)
      (fun r ↦ (counitOrdinaryShriek D l f₀).commShiftIso r)
      (NativeWeilOpenProper.compactificationComparison (k₀ := D.k₀) (l := l)
        f₀.left (counitCompactification D f₀)) := by
  let c := counitCompactification D (X := X) (Y := Y) f₀
  let := c.over (k₀ := D.k₀)
  let AX : CyclicDerivedSetting :=
    { category := ProEtale.AdicSheaf l (X.base.left ↘ Spec (CommRingCat.of D.k₀)).geometricFiber
      action := WeilSheaf.frobeniusPullback D.k₀ l X.base.left }
  let AZ : CyclicDerivedSetting :=
    { category := ProEtale.AdicSheaf l (c.Z ↘ Spec (CommRingCat.of D.k₀)).geometricFiber
      action := WeilSheaf.frobeniusPullback D.k₀ l c.Z }
  let AY : CyclicDerivedSetting :=
    { category := ProEtale.AdicSheaf l (Y.base.left ↘ Spec (CommRingCat.of D.k₀)).geometricFiber
      action := WeilSheaf.frobeniusPullback D.k₀ l Y.base.left }
  let L := ProEtale.adicOpenImmersionLowerShriek l
    (Hom.geometricFiberMap c.i (comp_over c.i (Spec (CommRingCat.of D.k₀))))
  let P := ProEtale.adicLowerStar l
    (Hom.geometricFiberMap c.g (comp_over c.g (Spec (CommRingCat.of D.k₀))))
  let ej := ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso
    l c.i (comp_over c.i (Spec (CommRingCat.of D.k₀)))
  let ep := ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso
    l c.g (comp_over c.g (Spec (CommRingCat.of D.k₀)))
  let s := CyclicDerivedTransport.exact (X := AX) (Y := AZ) L ej
  let t : CyclicDerivedTransport AZ AY :=
    { native := (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso ep).rightDerivedFunctor
      underlying := P.rightDerivedFunctor
      shifts := inferInstance
      comparison := NativeWeilOpenProper.properComparison (k₀ := D.k₀) (l := l) c.g }
  obtain ⟨bZ, hbZ, _⟩ := exists_cyclicDerivedHomBoundary AZ.action
  have hs := cyclicDerivedHom_exact_functorial AX.action AZ.action L ej
    bX bZ hbX.2 hbZ.2.2 hbX.1 hbZ.2.1
  have ht : CyclicDerivedHomBoundaryFunctorial AZ.action AY.action bZ bY
      t.native t.underlying t.shiftIso t.comparison := by
    apply cyclicDerivedCanonicalRight_functorial AZ.action AY.action P ep t.comparison
      ?_ bZ bY hbZ.2.2 hbY.2 hbZ.2.1 hbY.1
    exact (NativeWeilOpenProper.proper_normalization (k₀ := D.k₀) (l := l) c.g).1
  have hbnd : ∀ M, DerivedCategory.TStructure.t.bounded M →
      DerivedCategory.TStructure.t.bounded (s.native.obj M) := by
    intro M hM
    exact (ProEtaleWeilSheaf.extensionByZero D.k₀ l c.i).bounded_mapDerivedCategory_obj hM
  exact compose_functorial s t bX bZ bY hs ht hbnd

attribute [local irreducible] ProEtaleWeilSheaf.rightDerivedLowerShriek

/-- The action component of normalized cyclic transport.
Source: cyclicDerivedHom_exact_functorial and cyclicDerivedCanonicalRight_functorial,
for the native open/proper compactification.
(blueprint: lem-sf-native-exceptional-hom-transport-action).
Proof: compose exact open-extension functoriality with canonical right-derived
proper-pushforward functoriality, using proper_normalization for its unit equation.
The open extension preserves boundedness. Restrict the resulting action square to
Weil complexes; its forgetting comparison is the fixed compactification comparison. -/
theorem counitHomTransport_action_compatible
    (bX : CyclicDerivedHomBoundary (WeilSheaf.frobeniusPullback D.k₀ l X.base.left))
    (bY : CyclicDerivedHomBoundary (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left))
    (hbX : CyclicDerivedHomBoundaryNatural _ bX ∧ CyclicDerivedHomBoundaryNormalized _ bX)
    (hbY : CyclicDerivedHomBoundaryNatural _ bY ∧ CyclicDerivedHomBoundaryNormalized _ bY)
    (K H : W D l X) :
    ∀ r v, counitHomTransport D l f₀ K H r
        (cyclicDerivedHomAction _ K.obj H.obj r v) =
      cyclicDerivedHomAction _ ((nativeShriek D l f₀).obj K).obj
        ((nativeShriek D l f₀).obj H).obj r (counitHomTransport D l f₀ K H r v) := by
  simp only [counitHomTransport, counitForgetComparison, nativeShriek,
    WeilComplex.derivedLowerShriek,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    WeilComplex.forget, Functor.comp_obj]
  have hK := ((nativeShriek D l (X := X) (Y := Y) f₀).obj K).property.1
  have hH := ((nativeShriek D l (X := X) (Y := Y) f₀).obj H).property.1
  simp only [nativeShriek, WeilComplex.derivedLowerShriek] at hK hH
  have h0 := compactification_functorial D l (X := X) (Y := Y) f₀ bX bY hbX hbY
  dsimp only [CyclicDerivedHomBoundaryFunctorial] at h0
  have h := h0 K.obj H.obj K.property.1 H.property.1 hK hH
  dsimp only [cyclicDerivedHomTransport] at h
  -- Construct `h.2.1` in the forward direction: backward elaboration of its adic
  -- endpoints is expensive. The kernel checks this entire proof term.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some decl := (← Lean.getLCtx).findFromUserName? `h | throwError "missing h"
    let e ← Lean.Meta.mkAppM ``And.left
      #[← Lean.Meta.mkAppM ``And.right #[decl.toExpr]]
    (← Lean.Elab.Tactic.getMainGoal).assign e
    Lean.Elab.Tactic.replaceMainGoal []

/-- The degree-zero forgetting component of normalized cyclic transport.
Source: cyclicDerivedHom_exact_functorial and cyclicDerivedCanonicalRight_functorial,
for the native open/proper compactification.
(blueprint: lem-sf-native-exceptional-hom-transport-forget).
Proof: take the degree-zero component of the composite exact-open and canonical
right-derived proper transport, then restrict its morphism to the full subcategory
of Weil complexes. -/
theorem counitHomTransport_forget_compatible
    (bX : CyclicDerivedHomBoundary (WeilSheaf.frobeniusPullback D.k₀ l X.base.left))
    (bY : CyclicDerivedHomBoundary (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left))
    (hbX : CyclicDerivedHomBoundaryNatural _ bX ∧ CyclicDerivedHomBoundaryNormalized _ bX)
    (hbY : CyclicDerivedHomBoundaryNatural _ bY ∧ CyclicDerivedHomBoundaryNormalized _ bY)
    (K H : W D l X) :
    ∀ v : K ⟶ H, counitHomTransport D l f₀ K H 0
        (cyclicDerivedForget _ K.obj H.obj v.hom) =
      cyclicDerivedForget _ ((nativeShriek D l f₀).obj K).obj
        ((nativeShriek D l f₀).obj H).obj ((nativeShriek D l f₀).map v).hom := by
  intro v
  simp only [counitHomTransport, counitForgetComparison, nativeShriek,
    WeilComplex.derivedLowerShriek,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    WeilComplex.forget, Functor.comp_obj]
  have hK := ((nativeShriek D l (X := X) (Y := Y) f₀).obj K).property.1
  have hH := ((nativeShriek D l (X := X) (Y := Y) f₀).obj H).property.1
  simp only [nativeShriek, WeilComplex.derivedLowerShriek] at hK hH
  have h0 := compactification_functorial D l (X := X) (Y := Y) f₀ bX bY hbX hbY
  dsimp only [CyclicDerivedHomBoundaryFunctorial] at h0
  have h := h0 K.obj H.obj K.property.1 H.property.1 hK hH
  dsimp only [cyclicDerivedHomTransport] at h
  run_tac Lean.Elab.Tactic.withMainContext do
    let some decl := (← Lean.getLCtx).findFromUserName? `h | throwError "missing h"
    let e ← Lean.Meta.mkAppM ``And.right #[decl.toExpr]
    let e ← Lean.Meta.mkAppM ``And.left #[← Lean.Meta.mkAppM ``And.right #[e]]
    let v ← Lean.Elab.Tactic.elabTerm (← `($(Lean.mkIdent `v).hom)) none
    (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkApp e v)
    Lean.Elab.Tactic.replaceMainGoal []

/-- The normalized boundary component of cyclic transport.
Source: cyclicDerivedHom_exact_functorial and cyclicDerivedCanonicalRight_functorial,
for the native open/proper compactification.
(blueprint: lem-sf-native-exceptional-hom-transport-boundary).
Proof: choose the unique normalized natural middle boundary and compose the exact
open and canonical right-derived proper boundary squares. Proper normalization
identifies its forgetting comparison, and the open extension preserves boundedness.
Restrict to the full subcategory of Weil complexes and project the boundary square. -/
theorem counitHomTransport_boundary_compatible
    (bX : CyclicDerivedHomBoundary (WeilSheaf.frobeniusPullback D.k₀ l X.base.left))
    (bY : CyclicDerivedHomBoundary (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left))
    (hbX : CyclicDerivedHomBoundaryNatural _ bX ∧ CyclicDerivedHomBoundaryNormalized _ bX)
    (hbY : CyclicDerivedHomBoundaryNatural _ bY ∧ CyclicDerivedHomBoundaryNormalized _ bY)
    (K H : W D l X) :
    ∀ v : CyclicDerivedHom (WeilSheaf.frobeniusPullback D.k₀ l X.base.left)
        K.obj H.obj (-1),
      ((nativeShriek D l f₀).map (ObjectProperty.homMk
        (bX K.obj H.obj K.property.1 H.property.1 (QuotientAddGroup.mk v)))).hom =
      bY ((nativeShriek D l f₀).obj K).obj ((nativeShriek D l f₀).obj H).obj
        ((nativeShriek D l f₀).obj K).property.1 ((nativeShriek D l f₀).obj H).property.1
        (QuotientAddGroup.mk (counitHomTransport D l f₀ K H (-1) v)) := by
  simp only [counitHomTransport, counitForgetComparison, nativeShriek,
    WeilComplex.derivedLowerShriek,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    WeilComplex.forget, Functor.comp_obj]
  have hK := ((nativeShriek D l (X := X) (Y := Y) f₀).obj K).property.1
  have hH := ((nativeShriek D l (X := X) (Y := Y) f₀).obj H).property.1
  simp only [nativeShriek, WeilComplex.derivedLowerShriek] at hK hH
  have h0 := compactification_functorial D l (X := X) (Y := Y) f₀ bX bY hbX hbY
  dsimp only [CyclicDerivedHomBoundaryFunctorial] at h0
  have h := h0 K.obj H.obj K.property.1 H.property.1 hK hH
  dsimp only [cyclicDerivedHomTransport] at h
  run_tac Lean.Elab.Tactic.withMainContext do
    let some decl := (← Lean.getLCtx).findFromUserName? `h | throwError "missing h"
    let e ← Lean.Meta.mkAppM ``And.right #[decl.toExpr]
    let e ← Lean.Meta.mkAppM ``And.right #[e]
    let e ← Lean.Meta.mkAppM ``And.right #[e]
    (← Lean.Elab.Tactic.getMainGoal).assign e
    Lean.Elab.Tactic.replaceMainGoal []

/-- The fixed ordinary map of native compact support preserves the cyclic action,
forgetting, and the normalized connecting map on quotient representatives.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md.
(blueprint: lem-sf-native-exceptional-hom-transport).
Proof: combine the action, forgetting and boundary components above. -/
theorem counitHomTransport_compatible
    (bX : CyclicDerivedHomBoundary (WeilSheaf.frobeniusPullback D.k₀ l X.base.left))
    (bY : CyclicDerivedHomBoundary (WeilSheaf.frobeniusPullback D.k₀ l Y.base.left))
    (hbX : CyclicDerivedHomBoundaryNatural _ bX ∧ CyclicDerivedHomBoundaryNormalized _ bX)
    (hbY : CyclicDerivedHomBoundaryNatural _ bY ∧ CyclicDerivedHomBoundaryNormalized _ bY)
    (K H : W D l X) :
    (∀ r v, counitHomTransport D l f₀ K H r
        (cyclicDerivedHomAction _ K.obj H.obj r v) =
      cyclicDerivedHomAction _ ((nativeShriek D l f₀).obj K).obj
        ((nativeShriek D l f₀).obj H).obj r (counitHomTransport D l f₀ K H r v)) ∧
    (∀ v : K ⟶ H, counitHomTransport D l f₀ K H 0
        (cyclicDerivedForget _ K.obj H.obj v.hom) =
      cyclicDerivedForget _ ((nativeShriek D l f₀).obj K).obj
        ((nativeShriek D l f₀).obj H).obj ((nativeShriek D l f₀).map v).hom) ∧
    (∀ v : CyclicDerivedHom (WeilSheaf.frobeniusPullback D.k₀ l X.base.left)
        K.obj H.obj (-1),
      ((nativeShriek D l f₀).map (ObjectProperty.homMk
        (bX K.obj H.obj K.property.1 H.property.1 (QuotientAddGroup.mk v)))).hom =
      bY ((nativeShriek D l f₀).obj K).obj ((nativeShriek D l f₀).obj H).obj
        ((nativeShriek D l f₀).obj K).property.1 ((nativeShriek D l f₀).obj H).property.1
        (QuotientAddGroup.mk (counitHomTransport D l f₀ K H (-1) v))) := by
  exact ⟨counitHomTransport_action_compatible D l (X := X) (Y := Y) f₀ bX bY hbX hbY K H,
    counitHomTransport_forget_compatible D l (X := X) (Y := Y) f₀ bX bY hbX hbY K H,
    counitHomTransport_boundary_compatible D l (X := X) (Y := Y) f₀ bX bY hbX hbY K H⟩

end WeilConjectures.NativeExceptionalForgetful
