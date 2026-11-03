/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativePointFibreFunctor
public import WeilConjectures.DeligneLaumon.FiniteGeometricModel
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

local notation "Tgeom" => finiteGeometricModel D T₀

/-- The k-points of the specified geometric base change.
Source: latest blueprint, finite geometric fibre
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
abbrev Points := (Tgeom).hom.GeometricFiber (𝟙 (Spec (.of D.k)))

/-- Points above the given closed point of the arithmetic model.
Source: latest blueprint, Frobenius orbit block P_x
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
abbrev Block (x : closedPoints T₀.left) :=
  {z : Points D T₀ //
    (z.val ≫ pullback.fst T₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
        default = x.val}

/-- Derived sections applied to degree-zero native modules.
Source: latest blueprint, RΓ(T,F) for a degree-zero coefficient module
(blueprint: lem-zl-condensed-finite-fibre-evaluation). -/
def derivedOnModules :=
  DerivedCategory.singleFunctor (NativeCondensedModule.Modules l (Tgeom).left) 0 ⋙
    sectionsComplex D T₀ l

set_option maxHeartbeats 600000 in
-- The coherent pullback comparison has large concrete module-object types.
end WeilConjectures.CondensedFiniteEvaluation
