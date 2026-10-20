module

public import WeilConjectures.FromJoel.Algebra.Homology.CochainComplexMinus

/-!
Declarations of ours that lived in the upstream file
`WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc`
(moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20:
upstream files are verbatim in live).
-/

/-!
# Filtration of a cochain complex

Migrated from `Mathlib/Algebra/Homology/Embedding/CochainComplexTrunc.lean`
on the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Category Limits Functor

namespace CochainComplex

variable {C : Type*} [Category C] [Abelian C]
  (K L : CochainComplex C ℤ)

instance CochainComplexTrunc_mono (n : ℤ) : Mono (K.ιTruncLE n) := by
  dsimp only [ιTruncLE]
  infer_instance

end CochainComplex
