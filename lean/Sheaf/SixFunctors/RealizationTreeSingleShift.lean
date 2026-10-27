/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.SixFunctors.RealizationTreeShiftData
public import Sheaf.SixFunctors.RealizationAdjunctionInsertionShift

/-! # The realization square for one selected leaf

Source: the conditional expression-tree argument of
lem-pur-realization-tree-shift-transport, following the coefficient-comparison
sentence of the current blueprint fix-prop-coherence.proof.md.
(blueprint: lem-pur-realization-tree-single-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

open Classical in
/-- A single selected leaf preserves the admissible domain and its realization square.
Source: lem-pur-realization-tree-shift-transport, proof steps 1--4, motivated by
current blueprint fix-prop-coherence.proof.md, coefficient comparisons
(blueprint: lem-pur-realization-tree-single-shift).

Proof: First shift the selected integral input. Integral constructibility and
completeness are stable under shifts. Shift its normalized strict reduction tower,
including transition-adjoint maps and retained etale-origin transition squares.
Cohomology and Tor bounds translate by minus the shift. Along the selected path,
use the designated operation shift isomorphisms; other subtrees are unchanged.
Include the hidden open-extension intermediate of compact support. The finite
collection of old and translated bounds has a common finite envelope.
Before using BasicTree recursion, expand every compact-support constructor as
its open/proper composite along compactOpen and compactProper. The hidden open
admissibility witness gives precisely the expanded domain. The canonical
supportExpansion generator and its contexts, together with R.coherence, identify
the actual comparison of the original tree with the expanded one. Its system
and integral evaluation maps are identities; the slot shifts agree by the
specified composite shift formulas and functoriality. The expanded tree is
BasicTree. Now induct on its selected path using the assumed recursion.
At a leaf the comparison is the inverse unit, so use the assumed unit square.
At a unary vertex apply the child square, naturality of the operation shift,
and the corresponding insertion square. Expand compact support as its recorded
open/proper composite. At a tensor vertex use the child square and tensor
naturality in the selected slot, then the insertion square for that same slot.
The other child remains fixed. Use the signed right-slot comparison throughout
when the selected occurrence is on the right; no symmetry is inserted. The
endpoint equalities of variableContext give precisely the displayed sourceShift
and integralShift. This also applies to zero and negative shifts. -/
theorem realizationTreeSingleShift (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    (_hInsertion : RealizationAdjunctionInsertionShift l E D o R)
    (_hRecursion : ∀ {I : Type u} [Finite I]
      {X : I → Over (Spec (.of D.k))} {W : Over (Spec (.of D.k))}
      (e : Expression _ I X W) (ge : e.geometric) (K : (e.domain l E o).FullSubcategory),
      Recursion.BasicTree e → Recursion.Equations l E R R.comparison e ge K)
    : (∀ {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))}
      {W : Over (Spec (.of D.k))} (e : IndependentExpression _ I X W)
      (ge : e.val.geometric) (K : (e.val.domain l E o).FullSubcategory) (i : I) (r : ℤ),
      ∃ h : e.val.domain l E o (Function.update K.obj i ((K.obj i)⟦r⟧)),
        (R.comparison e.val ge).hom.app ⟨Function.update K.obj i ((K.obj i)⟦r⟧), h⟩ ≫
            (e.integralShift l E K.obj i r).hom =
          (e.sourceShift l E o K.obj i r).hom ≫
            ((R.comparison e.val ge).hom.app K)⟦r⟧') := by sorry

end WeilConjectures.IntegralSystemRealization
