module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Sheaf.RingTheory.GlobalDimension
import Sheaf.Algebra.ProjectiveDimensionWellDefined
import Sheaf.RingTheory.CohenMacaulayFreeResolution
import Sheaf.RingTheory.Depth
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.RegularLocalMaximalCohenMacaulayFree

/-!
# Finite module resolutions over regular local rings

Source: Stacks Project, Algebra, Proposition Tag 00O7, proof of the first assertion
(blueprint: lem-weil-pbc-regular-local-finite-module-resolution).
-/

@[expose] public section

universe u v

namespace IsRegularLocalRing

/-- Every finite module over a regular local ring of dimension `d` has a projective
resolution of length at most `d`.
Source: Stacks Project, Algebra, Proposition Tag 00O7.
(blueprint: lem-weil-pbc-regular-local-finite-module-resolution).

Proof:
Choose `d` generators of the maximal ideal, using regularity and the equality
of the dimension with `d`. They form an `R`-regular sequence by Tag 00NQ
(`lem-weil-pbc-regular-local-generators-regular-sequence`). Since the maximal
ideal is proper, this sequence gives depth of `R` at least `d` by
`def-weil-pbc-depth`.

For a nonzero finite module `M`, Tag 00NG
(`lem-weil-pbc-cm-local-free-resolution-to-mcm`) gives its depth `e`, with
`e ≤ d`, and an exact sequence `0 → K → F_{d-e-1} → ⋯ → F₀ → M → 0`.
Each `Fᵢ` is finite free and `K` is finite and either zero or of depth `d`.
In the latter case Tag 00NT (`lem-weil-pbc-regular-local-mcm-free`) makes
`K` free; in the former case it is free of rank zero. Thus this is a free
resolution of length `d - e`. When `e = d`, exactness identifies `K` with
`M`, so `M` itself is free.

Free modules are projective. Extend this exact sequence by zero objects
on the left to obtain a `ProjectiveResolution` of `M`, with zero terms
above degree `d - e`. Since `d - e ≤ d`, the same resolution has zero terms
above `d`, as in `lem-weil-pbc-projective-dimension-well-defined` (1).
For the zero module take the all-zero projective resolution directly.
These constructions work in the module universe `max u v` and prove the
asserted bound for every finite module. -/
theorem finiteModule_hasProjectiveResolutionLE
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    ∀ M : ModuleCat.{max u v} R, Module.Finite R M →
      ModuleCat.HasProjectiveResolutionLE M d := by
  sorry

end IsRegularLocalRing
