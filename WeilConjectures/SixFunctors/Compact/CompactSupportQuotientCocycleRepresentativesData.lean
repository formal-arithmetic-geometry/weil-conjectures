/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientCocycleData
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientChainFormulas

/-! # Chain-level quotient and balancing maps

Source: blueprint coefficient quotient proof, Steps 2 and 3; Stacks Tags 03EK and 06YY.
(blueprint: lem-coef-compact-support-quotient-model-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted

attribute [local irreducible] WeilConjectures.scalarReductionExistence
  WeilConjectures.scalarReductionExtension

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Termwise quotient and invertible balancing maps on an arbitrary complex.

Source: blueprint quotient proof, Steps 2 and 3; Stacks Tags 03EK and 06YY.
(blueprint: lem-coef-compact-support-quotient-model-maps).

Proof: construct the map s tensor x to q(s) tensor x by the ordinary tensor
adjunction on each term. Its ordinary adjunct sends t tensor (s tensor x) to
(t q(s)) tensor x. These formulas commute with restrictions and differentials,
so sheafification gives chain maps. The reverse balancing map sends t tensor x
to t tensor (1 tensor x). Balancing proves the composites are identities on pure
tensors, and hence after sheafification; this proves the second chain map invertible.
Take Mm and Mn to be the actual ordinary scalar-extension objects and take em,en
to be their identity isomorphisms. The component maps then give the asserted HEq
witnesses and formulas. This construction needs no K-flatness or termwise flatness:
it works also for the zero complex, equal levels and repeated indices. -/
theorem compactSupportQuotient_chain_maps (W : Scheme.{u})
    (m n : ℕ) (h : n ≤ m)
    (P : CochainComplex (scalarReductionSource.{u, u} l E W) ℤ) :
    ∃ (a : (compactSupportQuotientComplex l E W m).obj P ⟶
        ((proEtaleCoefficientRestrictScalars W
          (compactSupportLevelQuotient l E m n h)).mapHomologicalComplex (.up ℤ)).obj
            ((compactSupportQuotientComplex l E W n).obj P))
      (b : ((pbcExtend.{u} (compactSupportLevelSheafQuotient l E W m n h)).mapHomologicalComplex
          (.up ℤ)).obj ((compactSupportQuotientComplex l E W m).obj P) ⟶
        (compactSupportQuotientComplex l E W n).obj P),
      (∀ i : ℤ, ∃
        (Mm : scalarReductionTarget.{u, u} l E W m)
        (Mn : scalarReductionTarget.{u, u} l E W n)
        (em : (scalarReductionExtension.{u, u} l E W m).obj (P.X i) ≅ Mm)
        (en : (scalarReductionExtension.{u, u} l E W n).obj (P.X i) ≅ Mn)
        (a₀ : Mm ⟶ (proEtaleCoefficientRestrictScalars W
          (compactSupportLevelQuotient l E m n h)).obj Mn)
        (b₀ : (pbcExtend (compactSupportLevelSheafQuotient l E W m n h)).obj Mm ⟶ Mn),
        HEq em.hom (𝟙 ((scalarReductionExtension.{u, u} l E W m).obj (P.X i))) ∧
        HEq en.hom (𝟙 ((scalarReductionExtension.{u, u} l E W n).obj (P.X i))) ∧
        HEq (a.f i) a₀ ∧ HEq (b.f i) b₀ ∧
          CompactSupportQuotientModuleSpec l E W m n h (P.X i) Mm Mn em en a₀ b₀) ∧
      IsIso b := by
  obtain ⟨a, b, ha, hb, hiso⟩ := compactSupportQuotient_chain_formulas l E W m n h P
  refine ⟨a, b, ?_, hiso⟩
  intro i
  refine ⟨_, _, Iso.refl _, Iso.refl _, a.f i, b.f i,
    HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, ?_⟩
  constructor
  · intro U s x
    exact ha i U s x
  · exact hb i

end WeilConjectures
