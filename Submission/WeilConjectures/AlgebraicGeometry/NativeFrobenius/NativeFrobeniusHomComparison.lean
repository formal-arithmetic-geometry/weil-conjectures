/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusModelData
public import Submission.WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeHomBifunctorComparison

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Pointwise Hom transport to the native small model

Source: Stacks 03D6 and 03EO (blueprint: def-sf-native-frobenius-hom-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale.NativeFrobenius
variable (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]

attribute [local irreducible] comparisonRing nativeHom adicSectionModuleEquivalence
  inverseNativeHomComparison SheafOfModules.homObjMap

/-- Unlift slice maps and reverse the normalized native section-Hom comparison.
Source: Stacks 03D6 and 03EO (blueprint: def-sf-native-frobenius-hom-comparison). -/
def homComparison (H : AdicModuleHomComparisonCore l Y)
    (M N : TwistedActionRingedSite.Modules (ring Y l)) :
    (equivalence Y l).functor.obj (SheafOfModules.homObj (R := ring Y l) M N) ≅
      (nativeHom Y l).obj (op ((equivalence Y l).functor.obj M),
        (equivalence Y l).functor.obj N) :=
  (adicSectionModuleEquivalence l Y).inverse.mapIso
      (SheafOfModules.SmallSite.homIso (Scheme.ProEt.topology Y) (comparisonRing l Y) M N) ≪≫
    (inverseNativeHomComparison Y l H).app
      (op ((SheafOfModules.SmallSite.restriction
        (Scheme.ProEt.topology Y) (comparisonRing l Y)).obj M),
        (SheafOfModules.SmallSite.restriction
          (Scheme.ProEt.topology Y) (comparisonRing l Y)).obj N)

end AlgebraicGeometry.ProEtale.NativeFrobenius
