/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.RingTheory.GlobalDimension
import Mathlib.Order.RelClasses
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Projective dimension of a well-ordered union of submodules

Source: Stacks Project, Algebra, Lemma 0D1U
(blueprint: lem-weil-pbc-well-ordered-union-projective-dimension).
-/

universe u v w

namespace ModuleCat

/-- A well-ordered increasing union of submodules whose successive quotients have
projective resolutions of length at most `n` has a projective resolution of length at most `n`.
The predecessor union is represented by its submodule supremum and pulled back along the
inclusion of `F e` into `M`. For a least index this is the zero submodule.
Source: Stacks Project, Algebra, Lemma 0D1U
(blueprint: lem-weil-pbc-well-ordered-union-projective-dimension).

Proof (the node's eleven steps):
1. Induct on `n`, with the claim quantified over all modules and all well-ordered filtrations.
A finite set of elements in a chain lies in a single stage, by taking a largest index.
2. For `n = 0`, every successive quotient is projective, so the quotient projections split
(`lem-weil-pbc-projective-direct-summand`, `lem-weil-pbc-ses-projective-quotient-splits`).
Choose sections and form the map from the direct sum of the quotients to `M`.
3. This map is injective: a nonzero finite support has a largest index, and projection to
that index's quotient detects its nonzero component.
4. It is surjective by transfinite induction: subtract the section of the image of an
element in its stage's quotient; the difference belongs to the predecessor union.
5. Direct sums of projectives are projective (`lem-weil-pbc-projective-direct-sum-family`),
so the resulting isomorphism gives a length-zero resolution of `M`.
6. For positive `n`, take the free module on the elements of `M`, filtered by the free
modules on the elements of the stages. Its kernel is filtered by the corresponding kernels.
Finite support shows that both filtrations exhaust their modules.
7. The inclusions and the free-module surjection give a short exact sequence of successive
quotients of the kernel, free module and `M`. Injectivity follows from intersection with
the predecessor free module; exactness follows by subtracting the basis vector of the
image; surjectivity follows from surjectivity on each stage.
8. The free successive quotient has basis the elements of the stage outside its predecessor
union, hence is projective and admits a resolution of length at most `n - 1` by padding.
9. Dimension shifting (`lem-weil-pbc-projective-dimension-ses-kernel`) gives length at most
`n - 1` for the kernel's successive quotients.
10. Apply the induction hypothesis to the kernel filtration.
11. Splice its resolution with the free-module surjection onto `M`; exactness at the free
term is the kernel equality, and exactness at the preceding term uses injectivity of the
kernel inclusion. This gives the required length at most `n` resolution. -/
theorem hasProjectiveResolutionLE_of_wellOrderedUnion
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R) (n : ℕ)
    {E : Type w} [LinearOrder E] [IsWellOrder E (· < ·)]
    (F : E → Submodule R M) (hF : Monotone F)
    (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
    (hquot : ∀ e : E, HasProjectiveResolutionLE
      (ModuleCat.of R ((F e) ⧸
        ((⨆ e' : {i : E // i < e}, F e'.val).comap (F e).subtype))) n) :
    HasProjectiveResolutionLE M n := by
  sorry

end ModuleCat
