/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FieldShriekCompositionNormalization

/-! # Normalized completed refinement comparisons

Source: Stacks 0F7B and 0F7J; Bhatt--Scholze Definition 6.7.6.
(blueprint: lem-zl-qcqs-completed-refinement).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

include hl in
/-- A proper refinement has its open-adjunction-normalized completed comparison.
Source: Stacks 0F7B, 0F7J, and Bhatt--Scholze Definition 6.7.6 and Lemma 6.7.7
(blueprint: lem-zl-qcqs-completed-refinement).

Proof: for the square c.i followed by r.hom equals d.i, the canonical restriction
map is proper base change followed by the clopen-support identification over X.
The open adjunction transposes its inverse composed with the open unit to the
map epsilon from d.i_! K to Rr_* c.i_! K. On the normalized strict reduction
system its evaluations are the finite proper/open comparisons, hence invertible.
The completed cone has zero reductions and is complete, so epsilon is invertible.
Push epsilon inverse along d.g and insert the inverse canonical proper compositor
for r.hom followed by d.g. This is rho, and the transpose equation and compositor
formula are exactly SfCompletedRefinementSpec. Finite-type schemes over the field
are qcqs; this construction requires no separatedness of their structure maps.
For empty X both extension objects are zero and the same normalization applies. -/
theorem sfQcqsCompletedRefinement_exists
    {c d : Compactification f} (r : c.Refinement d)
    (K : sfIntegralConstructibleCategory l E X) :
    ∃ ρ : (image (completed l E) c).obj K.obj ≅
        (image (completed l E) d).obj K.obj,
      SfCompletedRefinementSpec l E r K.obj ρ := by sorry

end WeilConjectures
