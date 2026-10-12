/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FiniteEtaleTraceSplitting

/-!
# Local sheet correspondence for two finite clopen splittings

Source: Stacks Project, Section 03SH, paragraph after Definition 03SE;
SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-etale-trace-split-reindexing)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Two finite splittings of the same pullback admit a local correspondence of sheets.
Source: Stacks Project, Section 03SH, paragraph after Definition 03SE;
SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-etale-trace-split-reindexing)

Proof. Pull both coproducts back along `g₁` and `g₂`. Pullback pasting identifies their
ambient schemes with `Z ×[X] Y`. Pullbacks preserve the clopen coproduct decompositions
and the isomorphisms of each piece with the base. Intersect every piece of the first
splitting with every piece of the second. Project these intersections to `Z` using the
isomorphism of either sheet with `Z`; the two images agree, and are clopen. For each
point of `Z` each first sheet meets exactly one second sheet, and conversely, so these
memberships define a bijection of the finite index sets. Intersect the finitely many
clopen images corresponding to this bijection; this is an open neighbourhood of the
point on which all memberships are constant. These opens cover `Z`. Take `R` to be
the presieve of their inclusions, hence a covering by the jointly surjective criterion.
On each open corresponding sections factor through the same intersection piece and
are both inverses to its projection, so coincide. Compose with the induced maps to
`W ×[X] Y`; their equality follows from the commuting square and pullback uniqueness.

If no bijection of the index sets exists, there is no point of `Z`, by the pointwise
bijection construction. Take the empty covering presieve in that case; its local
correspondence condition is vacuous. This also handles empty index sets. This is a
geometric statement only: it involves no sheaf, finite sum, or global section. -/
theorem finiteEtaleTrace_split_reindexing {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : Etale f) :
    let B := MorphismProperty.Over.pullback @Etale ⊤ f ⋙ MorphismProperty.Over.map ⊤ hf
    ∀ (W T₁ T₂ Z : X.Etale) (h₁ : T₁ ⟶ W) (h₂ : T₂ ⟶ W)
      (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂), g₁ ≫ h₁ = g₂ ≫ h₂ →
      ∀ (D₁ : FiniteEtaleTraceSplitting f T₁) (D₂ : FiniteEtaleTraceSplitting f T₂),
      ∃ R : Presieve Z, Sieve.generate R ∈ X.smallEtaleTopology Z ∧
        ∀ (Q : X.Etale) (k : Q ⟶ Z), R k → ∃ e : D₁.J ≃ D₂.J,
          ∀ j, k ≫ g₁ ≫ D₁.sectionMap hf j ≫ B.map h₁ =
            k ≫ g₂ ≫ D₂.sectionMap hf (e j) ≫ B.map h₂ := by sorry

end AlgebraicGeometry.Etale
