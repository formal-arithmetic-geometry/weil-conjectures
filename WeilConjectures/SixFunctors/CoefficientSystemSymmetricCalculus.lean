/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagramData

/-! A simultaneous symmetric coefficient-system calculus. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
variable {l E D hl f c}

/-- The coefficient-system calculus admits the canonical signed tensor constraints.
Source: Stacks 0FPT, 08J9, 06YS and 0941; realization proof steps 1 and 12
(blueprint: lem-sf-coefficient-system-symmetric-calculus).
Proof: construct the derived calculus on the ringed sequence site using simultaneous
K-flat and K-injective resolutions. Use the same total tensor for its closed
structure and its representative tensor model. The signed swap, reassociation,
and multiplication by the degree-zero ring give symmetry, associativity and
unit constraints on those representatives. Their coherence equations hold on
pure tensor summands and descend through the K-flat localization. The
resolution-normalized fiber and global comparisons of the calculus use these
same maps. Thus both the calculus coherence and the ringed tensor coherence
hold for this common witness, rather than choosing unrelated tensor structures. -/
theorem coefficientSystemSymmetricCalculus (W : Scheme.{u}) :
    ∃ S : CoefficientDerivedSystemCalculus l E W,
      Nonempty (CoefficientDerivedSystemCoherence l E W S) ∧
      ∃ β : @SymmetricCategory (coefficientSequenceDerived l E W) _ S.systemClosed.monoidal,
        Nonempty (RingedDerivedTensorCoherence.{u+1, u, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) S.systemClosed S.systemTensorModel β) := by
  obtain ⟨S, ⟨hS⟩⟩ := coefficientDerivedSystemEvaluationCalculus l E W
  exact ⟨S, ⟨hS⟩, hS.systemTensorCoherence⟩

end WeilConjectures.FiniteAdjunctionDiagram
