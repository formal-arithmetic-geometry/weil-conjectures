/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Sheaf.SixFunctors.OpenClosedWeilMateData

/-! # Strict completion normalization of the integral mates -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Strict completion normalization of the integral mates.
Source: main-20261015, open/closed localization, coefficient and Weil paragraphs.
(blueprint: lem-sf-open-closed-weil-mate-completion-stage).

Proof: Apply the immersion completed-pullback comparison to the open and closed
maps and the three Frobenius automorphisms. Its finite-generator normalization
constructs the ordinary coefficient transport rho₀. Deriving its computation
counit constructs rho and fixes the displayed complex equation. Complete
representatives exist by the completion equivalence. The strict completion unit,
unit-normalized tower/reflector comparison and inverse gamma give the five
inclusion comparisons. Finite-Hom Mittag-Leffler uniqueness shows the pin holds
for every normalized Comparison and every representative. The normalized open
Roos and closed derived adjunctions identify the fixed adjoint mates. The
composition coherence of the pinned pullback comparisons gives the b/d cubes;
mate unit/counit identities and mate pasting give the remaining equations. -/
theorem sf_openClosed_weil_completion_stage
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (_ιE : E →ₐ[Padic l] Ω)
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left] [IsClosedImmersion i₀.left]
    (_hij : Set.range i₀.left.base = (Set.range j₀.left.base)ᶜ) :
    sfCompletionOpenClosedWeilMateAssertions D l hl E j₀ i₀ := by sorry

end WeilConjectures
