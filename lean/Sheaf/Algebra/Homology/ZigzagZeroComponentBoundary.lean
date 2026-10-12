module

public import Sheaf.Algebra.Homology.ZigzagModule
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import Sheaf.Algebra.Homology.ZigzagModuleFunctorial

/-! # Exact-row induction for a zero-component zig-zag

Source: Stacks Project, Algebra, Tag 00M1 (`lemma-no-spectral-sequence`),
injectivity argument. (blueprint: new-zigzag-zero-component-boundary).
-/

@[expose] public section

open CategoryTheory
namespace HomologicalComplex₂
universe u v
variable {R : Type u} [CommRing R]
/-- If a zig-zag has vanishing `(0,n)` component, successive exact-row lifts
 express it as a boundary.

Source: Stacks Project, Algebra, Tag 00M1 (`lemma-no-spectral-sequence`),
injectivity argument, lines 18496--18504.
(blueprint: new-zigzag-zero-component-boundary).

Maintain a residual cycle whose components of horizontal index below `k` are
zero, together with a tuple whose boundary is the difference from the original
cycle. Start at `k=1` with the original cycle and the zero tuple, using `hzero`.
For `1 ≤ k ≤ n`, its zig-zag equation at `(k-1,n-k)` says
`d aₖ,ₙ₋ₖ = δ aₖ₋₁,ₙ₋ₖ₊₁ = 0`. Row exactness at this positive index supplies
`f` in `Aₖ₊₁,ₙ₋ₖ` with `d f = aₖ,ₙ₋ₖ`. Subtract the boundary of the tuple
supported at `(k+1,n-k)` with value `f`. This kills the `k`-th component and
changes only the `(k+1,n-k-1)` component if `k<n`. Earlier components remain
zero. The first clause of `zigzagModule_functorial` and submodule subtraction
keep the residual a cycle. Add this tuple to the accumulated boundary preimage.
After `k=n`, all components are zero, so the original tuple is the boundary
of the accumulated tuple by linearity and direct-sum extensionality. For `n=0`,
the only index is `(0,0)`, so `hzero` already implies `a=0`, the boundary of zero.
No column exactness or assumptions on the ring's characteristic are used. -/
theorem zigzag_zero_component_boundary
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (hrow : ∀ (p q : ℕ), 0 < p →
      (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
        (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
          HomologicalComplex.zero_f])).Exact)
    (n : ℕ) (a : zigzagTotal A n) (ha : a ∈ zigzagCycles A n)
    (hzero : DirectSum.component R (ZigzagIndex n)
      (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2)
      ⟨(0, n), by simp⟩ a = 0) :
    a ∈ zigzagBoundaries A n := by
  sorry


end HomologicalComplex₂
