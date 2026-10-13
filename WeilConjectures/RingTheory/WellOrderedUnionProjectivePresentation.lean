/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.Order.RelClasses
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! Projective presentations for the successor well-ordered filtration argument. -/

@[expose] public section

universe u v w

namespace ModuleCat

open CategoryTheory

/-- The filtration argument supplies a short exact projective presentation whose
kernel has the inductive bound. Source: Stacks Project, Algebra, Lemma 0D1U.
(blueprint: lem-weil-pbc-well-ordered-union-succ-data).

Proof: the source takes free presentations of the stages. For the exact universe
generality here use projective presentations already supplied by `hquot` instead.
Put `U e = sup_{i < e} F i` and `Q e = F e / U e`. For each nonzero `Q e` take
the degree-zero term `P e` and the augmentation `a e : P e → Q e` of its supplied
length-`n+1` resolution; for a zero quotient take `P e = 0`. These are projective
objects in `ModuleCat.{v} R`. Lift `a e` through the quotient epimorphism
`F e → Q e` to a map `b e : P e → F e`. Let `P` be the external direct sum of
the `P e`, and `pi : P → M` the sum of the maps `b e` followed by stage inclusions.
Well-founded induction shows that `pi` maps the partial sum through index `e`
onto `F e`: subtract a lift of the quotient class; the remainder lies in a
preceding stage. Thus `pi` is surjective.

All these objects can be formed in universe `v`. Indeed, for each nonzero `Q e`
choose an element of `F e` outside `U e`. The chosen elements for different
indices differ, by monotonicity. The active index set therefore injects into
`M` and is small in `v`. Shrink that index set and its direct sum; the resulting
sum is categorical-projective by componentwise lifting against epimorphisms.
This avoids constructing a free R-module in universe `max u v` when `u > v`.

Let `K = ker pi` and let `G e` be its intersection with the partial sum through
`e`, pulled back into `K`. Finite supports have largest indices, so `G` is
monotone and covers `K`. The union of the preceding partial sums is the sum
strictly before `e`, and its image under `pi` is `U e`. Quotienting the kernel
sequence consequently gives an exact sequence
`0 → G e / G_{<e} → P e → Q e → 0`.
For the middle exactness, lift into the preceding partial sum the image of a
vector whose image in `Q e` is zero and subtract that lift. The difference is
in `K`. Injectivity is the equality of the intersection with the preceding
partial sum and the predecessor kernel union. Surjectivity is that of `a e`.

Dimension shifting for this projective presentation gives a length-`n` resolution
of `G e / G_{<e}`. Concretely, compare the presentation with the initial arrow
of the supplied resolution of `Q e`; Schanuel identifies their kernels after
adding the projective degree-zero terms. The supplied kernel has the truncated
length-`n` resolution, so adding projectives and taking the complementary direct
summand gives the required bound (the argument of Lemma 065S (1)). This argument
stays in `ModuleCat.{v} R` and needs no enough-projectives instance.
Apply `hIH` to `K` and `G`, obtaining its length-`n` resolution.
Take the short complex with objects `K`, `P`, and exactly `M`, and arrows
the kernel inclusion and `pi`. The inclusion is injective, `pi` is surjective,
and its kernel is the image of the inclusion, so this complex is short exact.
Its middle term is projective and its first term has the required bound.
At `n = 0` this gives a projective kernel. Repeated stages have zero quotients;
an empty index type is excluded by the covering assumption applied to zero. -/
theorem exists_shortExact_projective_middle_of_wellOrderedUnion_succ
    {R : Type u} [CommRing R] (n : ℕ)
    (hIH : ∀ (M : ModuleCat.{v} R) {E : Type w} [LinearOrder E]
      [IsWellOrder E (· < ·)] (F : E → Submodule R M) (hF : Monotone F)
      (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
      (hquot : ∀ e : E, HasProjectiveResolutionLE
        (ModuleCat.of R ((F e) ⧸
          ((⨆ e' : {i : E // i < e}, F e'.val).comap (F e).subtype))) n),
      HasProjectiveResolutionLE M n)
    (M : ModuleCat.{v} R) {E : Type w} [LinearOrder E]
    [IsWellOrder E (· < ·)] (F : E → Submodule R M) (hF : Monotone F)
    (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
    (hquot : ∀ e : E, HasProjectiveResolutionLE
      (ModuleCat.of R ((F e) ⧸
        ((⨆ e' : {i : E // i < e}, F e'.val).comap (F e).subtype))) (n + 1)) :
    ∃ S : ShortComplex (ModuleCat.{v} R), S.X₃ = M ∧ S.ShortExact ∧
      Projective S.X₂ ∧ HasProjectiveResolutionLE S.X₁ n := by
  sorry

end ModuleCat
