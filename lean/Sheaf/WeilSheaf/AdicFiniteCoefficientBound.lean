/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.Adic.Module
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing
import Sheaf.Paper.ConstantWeilStructure

/-!
# Passing a finite-coefficient bound to the constant adic sheaf

Source: the finite-level and rationalization steps of
`sec-poincare-duality/sk-lem-finite/prop-cohomological-finiteness.md`.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- A common upper bound for finite-coefficient direct images gives the same upper bound
for the derived direct image of the constant adic sheaf to a geometric point.

Source: literature/blueprint/master/blueprint/sec-poincare-duality/sk-lem-finite/
prop-cohomological-finiteness.md, finite-level passage and rationalization; Milne,
Lectures on Etale Cohomology, Theorem 15.1 and the proof of Theorem 19.2.
(blueprint: lem-pod-adic-unit-direct-image-finite-bound)

Proof: Use s to identify Y with the geometric point Spec k.
First take the constant integral l-adic sheaf and its reductions modulo l^n.
The hypothesis places the pro-etale direct image of each finite-level constant
sheaf (and indeed every sheaf of etale origin) in degrees at most b. The reduction exact
sequence and vanishing in degree b+1
make the transition maps in top degree epimorphic. Repleteness, or the Milnor exact
sequence on weakly contractible objects, then places the derived inverse limit in
the same upper range. The comparison of this inverse limit with integral adic direct
image is compatible with scalar extension. Inverting l is flat, and extending from
Q_l to any finite coefficient extension is flat, so these operations preserve the
upper bound. Finally the constant Qbar_l sheaf and its direct image are the filtered
coefficient extension of these constant finite-extension sheaves. Exactness of that
extension preserves the bound, giving the asserted vanishing. The argument concerns
the constant sheaf only and does not choose a lattice in an arbitrary local system. -/
theorem isLE_rightDerivedFunctor_adicLowerStar_unit_of_finite_bound
    {l : ℕ} [Fact l.Prime] {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) (f : X ⟶ Y)
    [IsIso s] [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f]
    (hchar : ringChar k ≠ l) (b : ℕ)
    (hfinite : ∀ (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ],
      ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
        ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F))).IsLE (b : ℤ)) :
    ((f)_*ᵃ[l].rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj (AdicSheaf.unit l X))).IsLE (b : ℤ) := by
  sorry

end AlgebraicGeometry.ProEtale
