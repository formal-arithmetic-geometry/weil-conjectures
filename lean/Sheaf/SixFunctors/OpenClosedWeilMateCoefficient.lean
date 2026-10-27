/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Sheaf.SixFunctors.OpenClosedWeilMateData

/-! # Coefficient compatibility of the ordinary mate words -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Coefficient compatibility of the ordinary mate words.
Source: main-20261015, open/closed localization, coefficient and Weil paragraphs.
(blueprint: lem-sf-open-closed-weil-mate-coefficient-stage).

Proof: Apply basicOperationsCoefficientReduction to the open and closed immersions
and the three geometric Frobenius automorphisms. Its tensor comparisons respect
composition, hence the two pullback cubes commute. Open scalar comparison is the
inverse left-adjoint mate; closed scalar comparison is the right-adjoint mate.
Their defining adjunct formulas give the four unit/counit equations. Pasting
mates around the pullback cubes gives the alpha and c transport equations.
Integral quotient reduction uses perfect quotients; finite quotient reduction
is restricted to the stated finite-Tor domain. Finite field extension uses
finite free tensor. These are exactly the three clauses, including repeated
quotient levels. -/
theorem sf_openClosed_weil_coefficient_stage
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
    sfCoefficientOpenClosedWeilMateAssertions D l E j₀ i₀ := by sorry

end WeilConjectures
