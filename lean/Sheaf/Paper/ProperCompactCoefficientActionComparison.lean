/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module
public import Sheaf.Paper.OrdinaryCompactCohomology
public import Sheaf.Paper.CompactSupportCoefficientAction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Intermediate comparisons for proper compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Coefficient)

/-- The proper comparison at this coefficient level.
Source: literature/blueprint/latest/blueprint/sec-zeta-weil/sk-input-weights/
prop-weil-proper-compact-coincidence.proof.md, first paragraph
(blueprint: lem-weil-proper-compact-coefficient-action-comparison).

Proof: For every finite coefficient field compare c with the identity compactification
on the full integral quotient system. These comparisons preserve the tensor-unit mates
which define the integral coefficient beta maps: both scalar squares are the same
identity-open and proper restriction square before total limit. Localize the comparisons;
pure-tensor naturality gives rational naturality and the localized scalar square.
For a morphism represented over a common field, expand both stage-system maps as beta,
the finite-stage map and inverse beta. The scalar square and finite-stage naturality
cancel the adjacent beta factors. This equality persists over every larger common field,
so it descends to the quotient of common-stage representatives. The inverse comparisons
satisfy the same calculation, giving inverse natural transformations. The normalization
fields in S and S₀ fix all the maps used here, hence the argument applies to every such
action. Empty inputs, zero maps and identity stages are preserved by these constructions.
-/
theorem properCompactCoefficientActionComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of D.k))]
    [IsProper (Y ↘ Spec (CommRingCat.of D.k))]
    (c : Compactification (Y ↘ Spec (CommRingCat.of D.k)))
    :
    letI : (Spec (CommRingCat.of D.k)).Over (Spec (CommRingCat.of D.k)) := ⟨𝟙 _⟩
    ∀ S : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω c,
      ∀ S₀ : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω
          (Compactification.ofIsProper (Y ↘ Spec (.of D.k))),
        Nonempty (S.system.functor ≅ S₀.system.functor) := by
  sorry

end WeilConjectures
