/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J7
-/
module

public import Sheaf.WeilSheaf.NativeExceptionalForgetfulData
public import Sheaf.WeilSheaf.NativeOpenProperForgetting
public import Sheaf.CategoryTheory.CyclicDerivedHomData

/-! # The ordinary graded Hom map of native compact support

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence, expanded by the finite-composite cyclic Hom sequence.
(blueprint: lem-sf-native-exceptional-hom-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor.IsoAlgebra
open WeilConjectures.AdicQbarRealization

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

/-- The fixed ordinary map of native compact support preserves the cyclic action,
forgetting, and the normalized connecting map on quotient representatives.

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md, exceptional
adjunction sentence; lem-sf-native-exceptional-counit-hom-squares, Steps 2--3.
(blueprint: lem-sf-native-exceptional-hom-transport).

Proof: use the exact open and total right-derived proper generators of
cyclicDerivedHom_finite_composite_functorial for the native compactification. The
open comparison is the localization of the literal sheaf-level equality. The proper
comparison is characterized by its derived unit on native K-injectives; uniqueness
identifies it with compactificationComparison, including the coherent shift maps.
Paste the two generators. The canonical restricted native functor is nativeShriek,
and the ordinary composite is counitOrdinaryShriek. The finite-composite theorem
requires boundedness only at source and final target, provided by the Weil complex
properties. Its action, forgetting and boundary clauses give these three equations.
Normalization and naturality identify the supplied boundary families with the
canonical ones. Empty source or target uses the same constructions on zero groups;
identity compactifications use the canonical unitors, with no new choice of signs. -/
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
        (QuotientAddGroup.mk (counitHomTransport D l f₀ K H (-1) v))) := by sorry

end WeilConjectures.NativeExceptionalForgetful
