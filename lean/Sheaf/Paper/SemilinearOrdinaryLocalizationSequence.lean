/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearOpenClosedData

/-! # Localization on ordinary strict systems
Source: Stacks 09AH (blueprint: lem-sp-semilinear-ordinary-localization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.SemilinearSections.OpenClosed

/-- The actual counit and unit give a short exact sequence of ordinary systems.
This assertion involves objects of the abelian system category, with no complexes
and no coefficient-change compatibility.
Source: Stacks 09AH; parent proof steps 1, 4 and 5
(blueprint: lem-sp-semilinear-ordinary-localization).

Proof: evaluate at each coefficient index. The open datum's restrictionLevel,
level and counit_level identify the evaluated open arrow with the counit of
ordinary sheafified extension by zero. The closed datum's pushEvaluation,
pullEvaluation and unitEvaluation identify the evaluated closed arrow with the
ordinary closed unit. Its levelPresentation identifies the chosen inverse image
with the small-model presentation. Uniqueness of left adjoints transports the
unit to the one in the ringed localization theorem. Apply that theorem at B_n,
using the given quasi-compact complementary open, to obtain monicity, epicity,
vanishing composite and exactness at that level. Evaluation is exact and jointly
conservative: a system morphism is invertible if every component is, because its
componentwise inverses commute with transitions. Apply this to kernels, cokernels
and homology. It detects the vanishing composite and zero homology, monicity and
epicity, proving the ordinary short exact sequence. These arguments include empty
open/closed pieces and zero rings. -/
theorem semilinearOrdinaryLocalization
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (U : T.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (B : ℕ → Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (K : ClosedData i B τ)
    (O : SequenceOpenOrdinary.{u + 1, u, 0} (Scheme.ProEt.topology T) U B τ)
    (M : Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology T) B τ) :
    Mono (O.adjunction.counit.app M) ∧ Epi ((adjunction i B τ).unit.app M) ∧
      (ComposableArrows.mk₂ (O.adjunction.counit.app M)
        ((adjunction i B τ).unit.app M)).Exact := by sorry

end WeilConjectures.SemilinearSections.OpenClosed
