/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.RelativeCurvePunctual
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement

/-! # The actual strict-pair compact-support functors

Source: latest blueprint, lem-zl-composition-weight-bound.proof.md, paragraph 1,
the induced Frobenius structures (blueprint: def-zl-native-shriek-functors).
These functors are exactly the three stages of RelativeCurve.higherShriek.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.DeligneLaumon.NativeShriek

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- Strict Weil pairs in the actual ordinary derived category.
Source: the input pair in paragraph 1 (blueprint: def-zl-native-shriek-functors). -/
abbrev Pair := CategoryTheory.Endofunctor.IsoAlgebra
  (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
    (D.geometricFrobenius X₀).hom).mapDerivedCategory

/-- Put a native Weil module in degree zero, with the canonical comparison.
Source: paragraph 1, F in degree zero (blueprint: def-zl-native-shriek-functors). -/
def single : NativeL2.WeilModule D l X₀ ⥤ Pair D l X₀ :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom).mapDerivedCategorySingleFunctor 0)

/-- Canonical cohomology of a strict pair as an actual native Weil module.
Source: paragraph 1, induced Weil cohomology (blueprint: def-zl-native-shriek-functors). -/
def cohomology (n : ℕ) : Pair D l X₀ ⥤ NativeL2.WeilModule D l X₀ :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom).mapDerivedCategoryHomologyFunctorIso (n : ℤ))

variable {X₀} {Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Compact support with the specified proper/open Frobenius exchange.
Source: paragraph 1, Rf! on strict pairs (blueprint: def-zl-native-shriek-functors). -/
def image (f₀ : X₀ ⟶ Y₀) (c₀ : Compactification f₀.left) :
    Pair D l X₀ ⥤ Pair D l Y₀ :=
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso (RelativeCurve.exchange D l f₀ c₀)

end WeilConjectures.DeligneLaumon.NativeShriek
