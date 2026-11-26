/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportImageComplete
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportFiniteMates

/-! # Finite comparisons for qcqs completed compact support

The comparison below is the actual scalar-adjunction mate on constructible integral
inputs. Its source is the ordinary completed proper/open composite.

## Implementation details

The schemes are Noetherian and qcqs, being of finite type over a field, and the input is
complete by integral constructibility. On a K-flat representative open extension is exact and
the quotient tensor comparison is the extension-summand tensor map. Quasi-compact open extension
preserves completeness, and proper direct image commutes with the total derived inverse limit
by its right adjunction; the perfect two-term quotient resolution identifies its scalar mate
with proper image of the quotient tensor map. The unit/counit factorization of the composite is
precisely `comparison (reduction ...) c`, so this specific mate is invertible. No separatedness
of either structure morphism is used.

## References

* [Bhatt--Scholze, *The pro-étale topology for schemes*, Definition 6.7.6 and Lemmas 6.1.13,
  6.7.7]
* [Stacks Project, Tags 0E8I and 0F7J]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
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

/-- Actual completed proper/open compact support preserves derived completeness on
integral constructible inputs; its scalar-adjunction mate to each positive finite
quotient is invertible.
This statement concerns the ambient proper/open functor, without the recorded integral
functor or any choice of realization map. -/
theorem sfQcqsCompactSupport_finiteComparison
    (K : sfIntegralConstructibleCategory l E X) :
    IsSfDerivedComplete l E Y ((image (completed l E) c).obj K.obj) ∧
      ∀ n : ℕ, IsIso
        ((comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app K.obj) := by
  exact ⟨sfQcqsCompactSupport_image_complete l E K₀ hl c K,
    sfQcqsCompactSupport_finiteMates l E K₀ hl c K⟩

end WeilConjectures
