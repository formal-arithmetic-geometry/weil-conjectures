/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralExpressionSystemComparison
/-! # Recursive strict-to-derived expression comparison

Source: Stacks 07A4 and 0941. The comparison is constructed recursively from
cochain tensor models and exact-localization factors, before completion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] SheafOfModules.monoidalCategory
universe t u s i j
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open Opposite AlgebraicGeometry
namespace WeilConjectures.IntegralCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {S : Type s} {W : S → Scheme.{t}}
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal

/-- Localization of the actual strict structural arrows is compatible with the
specified recursively constructed expression comparisons.
Source: Stacks 07A4 (cochain tensor constraints), 0D6D (localization composition),
and 0941 (strict coefficient systems)
(blueprint: stage3-pur-integral-structural-system-comparison).

Proof: use induction on StructuralMap. On associators, the model's triple-generator
formula and tensor-generator extensionality identify its chain map with the native
cochain associator. Naturality of the derived associator transports the three factor
comparisons. The unit-model scalar formula identifies the native right unitor; combine
with symmetry to obtain the left unitor. The symmetry-model generator formula is the
native braiding with sign (-1)^(pq), and its naturality transports the factors. For the
compositor, apply the exact-localization factorization equations to the prescribed
ordinary adjunction-normalized composition isomorphism; its composition factor is
exactly integralComparisonSystemComposition. Identity is functoriality. Inversion
follows by cancelling the localized forward iso; composition follows by reassociation.
The tensor context follows from naturality of CoefficientTensorModels.comparison and
the two inductive equations. The pullback context follows from naturality of the exact
localization comparison and the inductive equation. All equations concern whole
sequence-site derived maps. Zero objects, empty inputs, identity pullbacks and the
signed summands are covered by these same naturality and generator equations. -/
theorem structuralSystemComparison (M : CompletedOperations.Models l E W)
    {I : Type i} {location : I → S} (N : ∀ k : I, Complex l E (W (location k)))
    (hg : ∀ k : I, Good l E (W := W) (location k) (N k))
    {a : S} {P Q : CompletedOperations.Expression W location a}
    (α : CompletedOperations.StructuralMap P Q) :
    DerivedCategory.Q.map (structuralValue l E N α).hom ≫
        (systemComparison l E M N hg Q).hom =
      (systemComparison l E M N hg P).hom ≫
        (CompletedOperations.structuralValue l E M α
          (fun k ↦ DerivedCategory.Q.obj (N k))).hom := by
  sorry

end WeilConjectures.IntegralCoherence
