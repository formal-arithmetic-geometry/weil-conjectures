/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # Condensed finite-fibre evaluation and Frobenius orbits

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/sec-deligne-laumon-a1/
sec-the-weight-bound-on-the-affine-line/sk-thm-dl-a1-upper/lem-zl-finite-pushforward.proof.md,
Exactness and stalks and the Frobenius-orbit sentences
(blueprint: lem-zl-condensed-finite-fibre-evaluation).

The derived comparison is characterized on H⁰ by the actual restriction of sections.
The geometric cycle and the local return use the semilinear point convention, even
when the module is zero. No reducedness, purity or semisimplicity is imposed.

## Main definitions

`Evaluation` records the canonical finite sum and derived comparison.
`Frobenius` records the geometric cycles and their specified local returns.
`Naturality` records functoriality for module maps and semilinear diagrams.

## Main statements

`condensed_finite_fibre_evaluation` asserts these comparisons and compatibilities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj DirectSum

namespace WeilConjectures.CondensedFiniteEvaluation

attribute [local irreducible] NativeCondensedModule.transport NativeCondensedModule.operator

variable (D : FiniteFieldDatum.{u}) (T₀ : Over (Spec (.of D.k₀))) [IsFinite T₀.hom]
  (l : ℕ) [Fact l.Prime]

/-- Derived sections applied to degree-zero native modules.
Source: latest blueprint, RΓ(T,F) for a degree-zero coefficient module
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def derivedOnModules :=
  DerivedCategory.singleFunctor (NativeCondensedModule.Modules l (D.geometricFiber T₀).left) 0 ⋙
    sectionsComplex D T₀ l

/-- Canonical comparison for point pullbacks around a commuting scheme square.
Source: latest blueprint, naturality for semilinear finite-scheme diagrams
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def diagramComparison (l : ℕ) [Fact l.Prime] {S' S T' T : Scheme.{u}}
    (a : T' ⟶ T) (b : S' ⟶ S) (z' : S' ⟶ T') (z : S ⟶ T)
    (h : z' ≫ a = b ≫ z) (M : NativeCondensedModule.Modules l T) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z').obj
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M) ≅
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) b).obj
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M) :=
  (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) z' a).symm.app M ≪≫
    (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) h).app M ≪≫
    (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) b z).app M

set_option maxHeartbeats 600000 in
-- The coherent pullback comparison has large concrete module-object types.
end WeilConjectures.CondensedFiniteEvaluation
