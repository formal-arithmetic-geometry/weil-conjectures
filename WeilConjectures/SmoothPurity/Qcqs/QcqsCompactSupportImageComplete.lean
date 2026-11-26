/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.DeligneLaumon.QcqsCompactSupportOpenComplete
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportProperComplete

/-! # Completeness of qcqs compact-support images

This is the completeness component of the finite-comparison theorem.

## Implementation details

The proof is split from the finite-mate component so that the proper/open completion argument
can be developed independently. The completed open extension is identified with the normalized
quotient tower; exactness and quasi-compactness transport its completion unit, and the
right-adjoint proper direct-image/total-limit comparison shows that the completion unit of the
proper/open image is invertible.

## References

* [Bhatt--Scholze, *The pro-étale topology for schemes*, Lemmas 6.1.13 and 6.7.7]
* [Stacks Project, Tags 0E8I and 0F7J]
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [Xbase : X.Over (Spec (.of K₀))] [Ybase : Y.Over (Spec (.of K₀))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of K₀))]
  [Xqc : QuasiCompact (X ↘ Spec (.of K₀))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of K₀))]
  [fbase : f.IsOver (Spec (.of K₀))] [fs : IsSeparated f]
  [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f)

include K₀ hl Xbase Ybase Xft Xqc Yft Yqc fbase fs fft fqc

/-- The completed proper/open image of an integral constructible input is derived complete. -/
theorem sfQcqsCompactSupport_image_complete
    (K : sfIntegralConstructibleCategory l E X) :
    IsSfDerivedComplete l E Y ((image (completed l E) c).obj K.obj) := by
  have hopen := sfQcqsCompactSupport_open_complete l E K₀ hl c K
  exact sfQcqsCompactSupport_proper_complete l E K₀ hl c
    ((openExtension (completed l E) c.i).mapDerivedCategory.obj K.obj) hopen

end WeilConjectures
