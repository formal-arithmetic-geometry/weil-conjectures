module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts

public import Sheaf.RingTheory.MPseudoCoherent
public import Sheaf.RingTheory.RingPseudoCoherent
import Sheaf.RingTheory.PseudoCoherentDistinguishedTriangle

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-!
# Direct summands of pseudo-coherent complexes

Source: literature/stacks-project/more-algebra.tex, Tags 064X and 064T
(blueprint: lem-pc-ring-pseudo-coherent-summand).
-/

/-- A direct summand of an `m`-pseudo-coherent complex is `m`-pseudo-coherent.
Proof (node): `K ⊞ L` is bounded above, so `L` is; the split triangles
`(K ⊞ L, K ⊞ L, L ⊞ L[1])` and `(L[k], L[k] ⊞ L[k-1], L[k-1])` with the triangle lemma
(lem-pc-ring-pseudo-coherent-distinguished-triangle) give that `L[n] ⊞ L[n+1]` is
`m`-pseudo-coherent for all `n ≥ 0`, that `L[n]` is for `n` large (zero witness), and by
descending induction that `L` is; symmetrically `K`.
Source: Stacks Project, More on Algebra, Tag 064X.
(blueprint: lem-pc-ring-pseudo-coherent-summand) -/
theorem mPseudoCoherent_summand {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] (m : ℤ)
    (K L : DerivedCategory (ModuleCat.{v} R))
    (h : IsMPseudoCoherent m (K ⊞ L)) :
    IsMPseudoCoherent m K ∧ IsMPseudoCoherent m L := by
  sorry

/-- If `K ⊞ L` is quasi-isomorphic to a bounded-above complex of finite free modules
(pseudo-coherent), then so are `K` and `L`.
Proof (node): stupid truncations of a bounded-above finite free model show `K ⊞ L` is
`m`-pseudo-coherent for every `m`, hence so are `K` and `L` by the first clause, and an
object that is `m`-pseudo-coherent for every `m` has a bounded-above finite free model,
built downward degree by degree (Stacks, Tag 064T).
Source: Stacks Project, More on Algebra, Tags 064X and 064T.
(blueprint: lem-pc-ring-pseudo-coherent-summand) -/
theorem pseudoCoherent_summand {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (K L : DerivedCategory (ModuleCat.{v} R))
    (h : IsPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent K ∧ IsPseudoCoherent L := by
  sorry

end DerivedCategory
