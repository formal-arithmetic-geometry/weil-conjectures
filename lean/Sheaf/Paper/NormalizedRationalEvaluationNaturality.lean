/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.Paper.DerivedAutomorphismHomEvaluation

/-! # Naturality of normalized rational evaluation

Source: Stacks 08J9; normalized closed data, rationalization step 14
(blueprint: lem-coef-normalized-rational-evaluation-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- The Hom-first rational counit is natural in the two internal-Hom entries.
Source: Stacks 08J9; pod-derived-automorphism-hom-evaluation, proof step 14.
Proof: normalize the two tensor objects, Hom objects and counits by their
recorded integral object equalities. Inverse transpose on a pure tensor is the
pure tensor of integral inverse transpose, by podRationalClosed_existsUnique.
In particular evaluation is integral evaluation tensor one. For a pair of
pure-tensor arrows a tensor f and b tensor g, the two sides are a*b times the
integral evaluation naturality equation. That equation follows by precomposition
with the actual completion unit from the ambient counit's naturality; the
normalized completed transpose is injective. The operation normalization gives
bilinearity in f and g, so tensor-product induction extends the equation to
arbitrary rational arrows, including sums. Reinsert the object equalities.
This uses neither faithfulness of individual reductions nor absence of torsion.
(blueprint: lem-coef-normalized-rational-evaluation-naturality). -/
theorem normalizedRationalEvaluation_naturality
    (P P' : (constructibleRationalHomPairs l E W).FullSubcategory) (g : P ⟶ P') :
    (rationalDerivedTensor l E W).map
        (Prod.mkHom ((rationalDerivedInternalHom l E W).map g) (𝟙 P'.obj.1.unop)) ≫
      (podRationalClosed l E W).evaluation P' =
    (rationalDerivedTensor l E W).map
        (Prod.mkHom (𝟙 ((rationalDerivedInternalHom l E W).obj P)) g.hom.1.unop) ≫
      (podRationalClosed l E W).evaluation P ≫ g.hom.2 := by
  sorry

end WeilConjectures
