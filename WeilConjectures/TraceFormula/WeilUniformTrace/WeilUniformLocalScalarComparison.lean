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

/-- The local cohomology comparison for any finite strict model.
Source: latest blueprint, clause (3) and the scalar-descent sentence of
prop-every-iterate-trace.proof.md
(blueprint: lem-wutf-finite-model-local-comparison).

Proof: apply the local clause of strictWeil_cohomology_scalar_frobenius at the
canonical geometric lift, with identity reparametrization. Exact pullback and exact
point sections identify its native stalk with stalkComplex through their canonical
derived comparisons. The unit-normalized scalar pullback mate identifies the
left-derived scalar pair with weilStrictExtendToQbar. Compose with e. Naturality of
the point insertion and the pullback compositor identifies the local returns;
induction through the two associations of the iterated Weil map identifies their
m-fold maps. Apply cohomology and the canonical flat tensor/cohomology comparison.
Its isomorphism and the finite dimensionality assertions are exactly those of the
scalar comparison dependency, transported across these canonical isomorphisms. -/
theorem finite_model_local_comparison
    (K : strictWeilComplexCategory D ell hEll X₀ .qbar)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (K' : strictWeilComplexCategory D ell hEll X₀ (.finite E))
    (e : (weilStrictExtendToQbar D ell hEll X₀ E).obj K'.obj ≅ K.obj) :
    (∀ (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) (j : ℤ),
      Module.Finite (scalars ell (.finite E))
        (stalkCohomology D ell hEll X₀ (.finite E) K' m hm y j)) ∧
    (∀ (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) (j : ℤ), ∃ e :
      (ModuleCat.extendScalars (scalarInclusion.{u} ell E)).obj
          (stalkCohomology D ell hEll X₀ (.finite E) K' m hm y j) ≅
        stalkCohomology D ell hEll X₀ .qbar K m hm y j,
      (ModuleCat.extendScalars (scalarInclusion.{u} ell E)).map
          ((DerivedCategory.homologyFunctor _ j).map
            (localFrobenius D ell hEll X₀ (.finite E) K' m hm y)) ≫ e.hom =
        e.hom ≫ (DerivedCategory.homologyFunctor _ j).map
          (localFrobenius D ell hEll X₀ .qbar K m hm y)) := by
  sorry

end WeilConjectures.WeilUniformTrace
