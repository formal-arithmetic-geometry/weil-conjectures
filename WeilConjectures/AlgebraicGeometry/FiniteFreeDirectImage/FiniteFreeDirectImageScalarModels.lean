/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
/-! # Existence of normalized scalar models

Source: Stacks Project, Tags 03EK, 06YY and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage
variable {X : Scheme.{u}}
  {p : ∀ {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}},
    (a : R ⟶ S) → Presentation X a}
  (n : SheafOfModules.SuccessiveDerivedQuotient.Normalization.{u + 1, u, u + 1, u + 2}
    (C := X.ProEt) (J := ProEt.topology X)
    (hD := fun T ↦ proEtaleRingModules_hasDerivedCategory X T) p)

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
