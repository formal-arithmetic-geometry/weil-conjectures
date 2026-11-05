/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import Mathlib.Algebra.Module.Hom
import Mathlib.CategoryTheory.Yoneda
import all WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt

/-! # Scalar cokernels of universal finite-coefficient chain maps

Source: Stacks Tags 03EK, 06YS and 06YY; blueprint DVR effectivity,
coefficient quotient step. (blueprint: lem-coef-normalized-dvr-scalar-cokernel-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
@[instance_reducible] private noncomputable def descendedAction
    {A B : Type*} [Ring A] [Ring B] (p : A →+* B) (hp : Function.Surjective p)
    (M : Type*) [AddCommGroup M] [Module A M]
    (hk : ∀ a, p a = 0 → ∀ x : M, a • x = 0) : Module B M :=
  Module.compHom M (p.liftOfSurjective hp ⟨Module.toAddMonoidEnd A M, by
    intro a ha
    ext x
    exact hk a ha x⟩)

-- A cokernel in the larger category, lying in the image of the right adjoint,
-- identifies the adjunction unit with that cokernel.

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

end WeilConjectures
