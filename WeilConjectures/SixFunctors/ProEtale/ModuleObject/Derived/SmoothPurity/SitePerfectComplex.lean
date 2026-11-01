/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Perfect complexes on the coefficient site

Source: current Weil conjectures blueprint, `sec-smooth-purity`,
`sk-lem-sp-tower/def-weil-site-perfect-complex.md`, order 2959
(blueprint: def-weil-site-perfect-complex).

The same definition applies to every commutative condensed coefficient ring, including
finite discrete coefficients, integral and rational coefficients, and the finite-subextension
condensed algebraic closure. Restriction is the exact module pullback applied termwise.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A finite projective coefficient module is a direct summand of a finite sum
of the regular coefficient module. The rank may depend on the module.
Source: current blueprint, order 2959 (blueprint: def-weil-site-perfect-complex). -/
def IsFiniteProjectiveOnCoefficientSite (Y : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) : Prop :=
  ∃ m : ℕ, Nonempty (Retract M (Mod.finiteFree (condensedRingObj Λ Y) m))

/-- Perfectness is pro-etale local representation by a bounded complex of finite
projective coefficient modules. Bounds and ranks may vary across the cover.
This is one predicate for all commutative condensed coefficient rings, with no
constructibility, derived completeness, localization or common-stage condition.
Source: current blueprint, order 2959 (blueprint: def-weil-site-perfect-complex). -/
def IsPerfectOnCoefficientSite (Y : Scheme.{u})
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) : Prop :=
  ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i : C.I₀,
    ∃ (P : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology (C.X i)) Ab.{u + 1})
          (condensedRingObj Λ (C.X i))) ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ n : ℤ, IsFiniteProjectiveOnCoefficientSite Λ (C.X i) (P.X n)) ∧
      Nonempty ((upperStar Λ (C.f i)).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)

end AlgebraicGeometry.ProEtale.CondensedRing
