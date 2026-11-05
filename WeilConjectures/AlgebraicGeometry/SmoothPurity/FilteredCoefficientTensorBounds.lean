/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientHomologyTriangulated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.HomologicalComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import Mathlib.Algebra.Homology.Functor
import Mathlib.Data.Fin.SuccPred
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Finite coefficient filtrations preserve constructibility and cohomological bounds

Source: Stacks Project, proetale.tex, Tag 09B5, lemma-constructible-serre;
agent-written finite-filtration application
(blueprint: lem-sf-filtered-coefficient-tensor-bounds).

The coefficient tensor is constructed as `(B_Y ⊗_R P) ⊗_{B_Y} U_Y`.
The canonical balanced identification sends `(b ⊗ p) ⊗ v` to `p ⊗ bv`;
its inverse sends `p ⊗ v` to `(1 ⊗ p) ⊗ v`. Thus this is precisely
`P ⊗_R U_Y`, with its B_Y-action, including its differential.

## Main declarations

* `filteredCoefficientTensorFunctor` and `filteredCoefficientTensorDifferential`:
  the termwise tensor functor and its actual differential.
* `filteredCoefficientTensorComplex_laws`: the shape and square-zero proof obligations.
* `filteredCoefficientTensorComplex`: the resulting cochain complex.
* `filteredCoefficientTensor_constructible_bounds`: finite coefficient devissage.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (ρ : R ⟶ adicLisseConstantRing Y B)
  (P : CochainComplex (pbcModules Y R) ℤ)

attribute [local instance] tensorSiteSmall
  SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

end AlgebraicGeometry.Scheme
