/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module


public import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections

/-!
# Proper base change for constructible complexes

Source: literature/blueprint/slopmaster2-20261029-2300/blueprint/sec-six-functors-basics/
sk-thm-sfb-proper-base-change/_section.md (blueprint: sk-thm-sfb-proper-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y}

/-- The constant `Q̄_ℓ` coefficient complex on `X`, represented by the monoidal unit.
Source: blueprint sk-thm-sfb-proper-base-change, geometric-point consequence. -/
noncomputable abbrev qbarConstantComplex (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    {X : Scheme.{u}} (_a : X ⟶ Spec (.of k)) :
    DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) :=
  MonoidalCategory.tensorUnit _

/-- The degree-`i` ordinary cohomology module of the constant `Q̄_ℓ` complex on `X`.
Source: blueprint sk-thm-sfb-proper-base-change, geometric-point consequence. -/
noncomputable abbrev qbarCohomology (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) (i : ℤ) :
    ModuleCat.{u + 1} (PadicAlgCl ℓ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PadicAlgCl ℓ)) i).obj
    ((WeilConjectures.condensedQbarOrdinarySections ℓ k a).obj
      (qbarConstantComplex ℓ a))

/-- Proper direct image preserves constructibility, satisfies proper base change and the
projection formula for every admissible coefficient. The final clause records finiteness and
boundedness of the cohomology over an algebraically closed point.

Source: the proper-base-change unit, Tags 0F0G, 09B1, 09A6, 0GL0 and 0F10
(blueprint: sk-thm-sfb-proper-base-change).

Proof: split into finite, integral and rational coefficients as in the blueprint. The finite
case is `det-thm-sfb-proper-base-change-finite`, using finite-coefficient proper base change
and constructible finiteness. The integral case is
`det-thm-sfb-proper-base-change-integral`, and it
uses derived completeness, reduction modulo a uniformizer and derived Nakayama. The rational
case is `det-thm-sfb-proper-base-change-rational`, following by inverting the uniformizer and
passing through finite subextensions. In each case
the canonical exchange map is an isomorphism and the canonical projection map is an isomorphism.
The geometric-point assertion follows by applying the result to the constant coefficient complex
over an algebraically closed point and using the perfectness of the resulting complex; the
cohomology modules are the `qbarCohomology` objects and are finite-dimensional and bounded.
(blueprint: sk-thm-sfb-proper-base-change). -/
theorem properBaseChange (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (hf : IsProper f.left) :
    (∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj Λ X.left)),
      (constantModelBoundedConstructible Λ X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
        (constantModelBoundedConstructible Λ Y.left
          ((R((f.left)_*⟦Λ⟧)).obj K)) ∧
        DerivedCategory.finiteTorAmplitude _ ((R((f.left)_*⟦Λ⟧)).obj K)) ∧
    (∀ {X' Y' : Over (Spec (.of k))}
      [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
      [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
      {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X},
      (sq : IsPullback g' f' f g) →
      ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
          (condensedRingObj Λ X.left)),
        (constantModelBoundedConstructible Λ X.left K ∧
          DerivedCategory.finiteTorAmplitude _ K) →
          IsIso ((baseChangeMap Λ (sq.map (Over.forget (Spec (.of k)))).toCommSq).app K)) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
          (condensedRingObj Λ X.left)),
      ∀ M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
          (condensedRingObj Λ Y.left)),
      (constantModelBoundedConstructible Λ X.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      (constantModelBoundedConstructible Λ Y.left M ∧
        DerivedCategory.finiteTorAmplitude _ M) →
      IsIso (moduleObjectProjectionMap Λ f.left K M)) ∧
    (∀ [IsAlgClosed k], IsProper X.hom →
      ∃ a b : ℤ, (∀ i : ℤ, (i < a ∨ b < i) →
        IsZero (qbarCohomology ℓ X.hom i)) ∧
        ∀ i : ℤ, FiniteDimensional (PadicAlgCl ℓ)
          (qbarCohomology ℓ X.hom i)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
