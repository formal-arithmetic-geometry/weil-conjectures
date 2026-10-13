/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# The split-row boundary on cocycles

Source: Stacks Project, Derived Categories, Tags 0152 and 06XR.
(blueprint: lem-sc-p1-split-ses-cocycle-boundary).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

namespace CochainComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A lift followed by its differential computes composition with the split boundary.
Source: Stacks Project, Derived Categories, Tags 0152 and 06XR, the canonical
boundary and its computation by homotopy classes of maps into resolutions.
(blueprint: lem-sc-p1-split-ses-cocycle-boundary).

Proof: The split boundary has component sⁿ d₂ rⁿ⁺¹. Put t = b rⁿ. The splitting
identity gives b = t fⁿ + c sⁿ. Multiply by d₂ and use f d₂ = d₁ f. Since
b d₂ = a fⁿ⁺¹ and fⁿ⁺¹ rⁿ⁺¹ = id, obtain c sⁿ d₂ rⁿ⁺¹ = a - t d₁.
Thus the cocycle obtained by composing c with the degree-one split boundary differs
from a by the coboundary of t. The unsigned shift of fromSingleMk identifies
composition of these shifted maps with this component formula. The maps from the
single complex are consequently homotopic; Q identifies them. No injectivity,
boundedness, or augmentation is used, and n may be any integer. In the zero row the
same identities give zero on both sides. -/
theorem degreewiseSplit_cocycle_boundary
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (S : ShortComplex (CochainComplex C ℤ))
    (σ : ∀ k : ℤ,
      (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) k)).Splitting)
    (M : C) (n : ℤ) (c : M ⟶ S.X₃.X n)
    (hc : c ≫ S.X₃.d n (n + 1) = 0)
    (b : M ⟶ S.X₂.X n) (hb : b ≫ S.g.f n = c)
    (a : M ⟶ S.X₁.X (n + 1))
    (ha : a ≫ S.X₁.d (n + 1) (n + 1 + 1) = 0)
    (hba : b ≫ S.X₂.d n (n + 1) = a ≫ S.f.f (n + 1)) :
    (ShiftedHom.map (Cocycle.equivHomShift.symm
      (Cocycle.fromSingleMk c (zero_add n) (n + 1) rfl hc)) DerivedCategory.Q).comp
        (ShiftedHom.map (homOfDegreewiseSplit S σ) DerivedCategory.Q)
        (show (1 : ℤ) + n = n + 1 by omega) =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk a (zero_add (n + 1)) (n + 1 + 1) rfl ha))
          DerivedCategory.Q := by sorry

end CochainComplex
