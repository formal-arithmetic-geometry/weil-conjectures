module

public import Sheaf.Algebra.Homology.ZigzagModule
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import Sheaf.Algebra.Homology.ZigzagModuleFunctorial
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Removing the zeroth component of a row boundary

Source: Stacks Project, Algebra, Tag 00M1 (`lemma-no-spectral-sequence`),
injectivity argument. (blueprint: new-zigzag-boundary-reduction).
-/

@[expose] public section

open CategoryTheory
namespace HomologicalComplex₂
universe u v
variable {R : Type u} [CommRing R]
/-- The row-cokernel boundary hypothesis permits subtracting one trivial zig-zag
 to kill the `(0,n)` component.

Source: Stacks Project, Algebra, Tag 00M1 (`lemma-no-spectral-sequence`),
injectivity argument, lines 18488--18496.
(blueprint: new-zigzag-boundary-reduction).

Let `π = A.pOpcycles 0`. Lift the witness `y` of `hboundary` through the
surjective cokernel projection `π` in degree `n+1`, obtaining `c` in `A₀,ₙ₊₁`.
The chain-map identity for `π` gives `πₙ(a₀,ₙ - δ c) = 0`. The kernel of this
cokernel projection is the image of `d : A₁,ₙ → A₀,ₙ`, so choose `e` with
`d e = a₀,ₙ - δ c`. Define `b` to be the sum of the direct-sum inclusions of
`c` at `(0,n+1)` and `e` at `(1,n)`. Its boundary has zeroth component
`δ c + d e = a₀,ₙ`. Boundaries are cycles by the first clause of
`zigzagModule_functorial`; hence `a - zigzagBoundary A n b` is a cycle by
submodule closure under subtraction, and its zeroth component is zero by
linearity of the component projection. The construction also works for `n=0`;
row exactness is not used in this initial reduction. -/
theorem zigzag_boundary_reduction
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (hrow : ∀ (p q : ℕ), 0 < p →
      (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
        (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
          HomologicalComplex.zero_f])).Exact)
    (n : ℕ) (a : zigzagTotal A n) (ha : a ∈ zigzagCycles A n)
    (hboundary : ∃ y : (A.opcycles 0).X (n + 1),
      (A.opcycles 0).d (n + 1) n y = (A.pOpcycles 0).f n
        (DirectSum.component R (ZigzagIndex n)
          (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2) ⟨(0, n), by simp⟩ a)) :
    ∃ b : zigzagTotal A (n + 1),
      a - zigzagBoundary A n b ∈ zigzagCycles A n ∧
      DirectSum.component R (ZigzagIndex n)
        (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2)
        ⟨(0, n), by simp⟩ (a - zigzagBoundary A n b) = 0 := by
  sorry


end HomologicalComplex₂
