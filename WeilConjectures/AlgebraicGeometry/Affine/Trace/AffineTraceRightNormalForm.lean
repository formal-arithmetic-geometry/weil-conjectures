/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.TensorRightUnitor

/-!
# AffineTraceRightNormalForm
Source: blueprint sk-prop-an, Steps 5(b) and 6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance] Sheaf.monoidalCategory

section General
variable (B : Type*) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  (N : ℕ) (E : ∀ X : Scheme.{u}, ℕ → Sheaf X.smallEtaleTopology B)
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (upperStar B f).PreservesFlat]

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsUnit (N : Γ(Y, ⊤)) → ∀ d : ℕ,
  (upperStar B f).obj (E Y d) ≅ E X d)

variable (e0 : ∀ X : Scheme.{u}, E X 0 ≅ (constantSheaf X.smallEtaleTopology B).obj (𝟙_ B))
  (flat : ∀ X : Scheme.{u}, IsUnit (N : Γ(X, ⊤)) → ∀ d, ObjectProperty.flat (E X d))
  (prod : ∀ X : Scheme.{u}, IsUnit (N : Γ(X, ⊤)) → ∀ d, E X d ⊗ E X 1 ≅ E X (d + 1))

end General

end AlgebraicGeometry.Etale
