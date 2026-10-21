module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! Declarations of ours that lived in the upstream file
`WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex`
(moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20:
upstream files are verbatim in live). -/

/-!
# Truncations of cochain complexes: behaviour on degrees

Supplement to `Mathlib.Algebra.Homology.Embedding.CochainComplex`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Category Limits ComplexShape ZeroObject

namespace CochainComplex

variable {C : Type*} [Category* C]

open HomologicalComplex

variable [HasZeroMorphisms C] (K : CochainComplex C ℤ)
  [HasZeroObject C] [∀ i, K.HasHomology i]

instance CochainComplex_mono (n : ℤ) : Mono (K.ιTruncLE n) := by
  dsimp only [ιTruncLE]
  infer_instance

end CochainComplex
