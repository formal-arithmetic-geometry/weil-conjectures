/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.SmoothPurity.GeometricFrobeniusTransport.GeometricFrobeniusCohomologyTransport
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Finite-model cohomology comparison

Source: latest blueprint, det-thm-tf-uniform-formula-weil.proof.md, clause (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures.WeilUniformTrace

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

/-- The compact cohomology comparison for any finite strict model.
Source: latest blueprint, clause (3) and the scalar-descent sentence of
prop-every-iterate-trace.proof.md
(blueprint: lem-wutf-finite-model-compact-comparison).

Proof: apply strictWeil_cohomology_scalar_frobenius to the finite pair. The canonical
left-derived/exact scalar comparison identifies its induced pair with
weilStrictExtendToQbar. The unit-normalized scalar pullback mate identifies the two
Weil structures, giving an isomorphism of strict pairs. Compose with e. Naturality
of compact-support exchange, point sections and the Weil map makes the resulting
compact cohomology isomorphism intertwine the one-step operators. Functoriality and
induction on m give all powers. The same scalar comparison theorem supplies finite
dimensionality over the finite coefficient section field. No model of an arbitrary
existence theorem is used to define an object. -/
theorem finite_model_compact_comparison
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ .qbar)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (K' : strictWeilComplexCategory D ell hEll X₀ (.finite E))
    (e : (weilStrictExtendToQbar D ell hEll X₀ E).obj K'.obj ≅ K.obj) :
    (∀ i : ℤ, Module.Finite (scalars ell (.finite E))
      (compactCohomology D ell hEll X₀ (.finite E) c₀ K' i)) ∧
    (∀ i : ℤ, ∃ e :
      (ModuleCat.extendScalars (scalarInclusion.{u} ell E)).obj
          (compactCohomology D ell hEll X₀ (.finite E) c₀ K' i) ≅
        compactCohomology D ell hEll X₀ .qbar c₀ K i,
      ∀ m : ℕ,
        (ModuleCat.extendScalars (scalarInclusion.{u} ell E)).map
            ((DerivedCategory.homologyFunctor _ i).map
              (globalFrobenius D ell hEll X₀ (.finite E) c₀ K' ^ m)) ≫ e.hom =
          e.hom ≫ (DerivedCategory.homologyFunctor _ i).map
            (globalFrobenius D ell hEll X₀ .qbar c₀ K ^ m)) := by
  sorry

end WeilConjectures.WeilUniformTrace
