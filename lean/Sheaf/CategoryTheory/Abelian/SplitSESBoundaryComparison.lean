/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Comparing the cone and split-row boundaries

Source: Stacks Project, Derived Categories, Tag 0152.
(blueprint: lem-sc-p1-split-ses-boundary-comparison).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- The canonical cone boundary is the image of the split-row boundary.
Source: Stacks Project, Derived Categories, Tag 0152, the formula for the canonical
boundary through the cone quasi-isomorphism.
(blueprint: lem-sc-p1-split-ses-boundary-comparison).

Proof: Let q : Cone(S.f) -> S.X₃ be the cone comparison. Its components are the
projection onto S.X₂ followed by S.g. In the chosen splitting write S.X₂ⁿ as
S.X₁ⁿ ⊞ S.X₃ⁿ. The differential has diagonal entries d₁,d₃ and upper-right entry
sⁿ d₂ rⁿ⁺¹. Multiplying q by this entry gives the split boundary. Subtracting the
third cone map, which is minus the first projection, gives a null-homotopic map;
the homotopy in degree k is Hᵏ = proj₂ ≫ rᵏ, landing in S.X₁[1]ᵏ⁻¹.
Indeed d_Cone ≫ H + H ≫ d_{X₁[1]} = proj₁ + proj₂ ≫ g ≫ s ≫ d₂ ≫ r,
which is q followed by the split boundary minus the third cone map. Here the
shifted differential is -d₁. Expand r f + g s = id, f r = id and f d₂ = d₁ f.
Apply Q, which identifies homotopic maps, and cancel Q(q), a quasi-isomorphism.
The commutation of Q with shift gives exactly the displayed formula. This works
for every degreewise splitting, including the zero row, and does not require a
splitting by chain maps. -/
theorem triangleOfSESδ_eq_degreewiseSplit
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (σ : ∀ k : ℤ,
      (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) k)).Splitting) :
    triangleOfSESδ hS =
      ShiftedHom.map (CochainComplex.homOfDegreewiseSplit S σ) Q := by sorry

end DerivedCategory
