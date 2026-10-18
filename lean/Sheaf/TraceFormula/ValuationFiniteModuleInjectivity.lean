/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Injectivity from the closed fibre over a valuation ring

Source: Stacks Project, `more-morphisms.tex`, Tag 0GSG (lemma-mod-injective-valuation-ring)
(statement; blueprint: `lem-trf-valuation-finite-module-injectivity`).

## Main statement

The statement is the closed-fibre injectivity criterion of Tag 0GSG.  Its proof
first replaces an essentially finite type local algebra by a localization of a
polynomial algebra, approximates the source module by finitely presented
modules, applies the finite-presentation criterion of Tags 0GSE(2) and 046Y,
and finally identifies the approximating module with the source using the
injectivity obtained in the preceding step.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w z

namespace Algebra

/--
Injectivity modulo the maximal ideal over a valuation ring implies injectivity
and flatness of the cokernel.

Source: Stacks Project, `more-morphisms.tex`, Tag 0GSG (lemma-mod-injective-valuation-ring),
statement (blueprint: lem-trf-valuation-finite-module-injectivity).

Proof steps: (1) reduce an essentially finite type local algebra to a localized
polynomial algebra; (2) approximate the source by finitely presented modules
with unchanged closed fibre; (3) use Tag 0GSE(2) to make the finite flat target
finitely presented; (4) apply Tag 046Y to obtain injectivity and flatness of
the cokernel; (5) use the surjective colimit map and injectivity to identify the
approximation with the original source.
-/
theorem valuation_finite_module_injectivity
    (A : Type u) (B : Type v) (N : Type w) (M : Type z)
    [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B]
    [Algebra.EssFiniteType A B] [IsLocalHom (algebraMap A B)]
    [AddCommGroup N] [AddCommGroup M]
    [Module B N] [Module B M] [Module A N] [Module A M]
    [IsScalarTower A B N] [IsScalarTower A B M]
    [Module.Finite B N] [Module.Finite B M]
    (u : N →ₗ[B] M)
    [Module.Flat A M]
    (h_fibre :
      Function.Injective
        (Submodule.mapQ
          ((IsLocalRing.maximalIdeal A) •
            (⊤ : Submodule A N))
          ((IsLocalRing.maximalIdeal A) •
            (⊤ : Submodule A M))
          (u.restrictScalars A)
          (by
            rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'',
              Submodule.map_top]
            exact Submodule.smul_mono
              (I := IsLocalRing.maximalIdeal A) (J := IsLocalRing.maximalIdeal A)
              (N := LinearMap.range (u.restrictScalars A))
              (P := (⊤ : Submodule A M))
              le_rfl le_top))) :
    Function.Injective u ∧
      Module.Flat A
        (M ⧸ Submodule.restrictScalars A (LinearMap.range (u.restrictScalars A))) := by
  sorry

end Algebra

end
