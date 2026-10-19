## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleReducedCartierDescent` states
`AlgebraicGeometry.etale_reduced_cartier_descent`. It uses the existing Mathlib
locally-Noetherian predicate, étale morphism class, scheme fibre products and
`Scheme.IdealSheafData.IsInvertible`, together with the project declaration
`Scheme.IdealSheafData.reduced_induced_closed_subscheme`.

The node hypotheses and clauses are rendered as follows.

* The locally Noetherian scheme (X) is `(X : Scheme.{u})
  [IsLocallyNoetherian X]`.
* The closed subset (Z\subseteq X) is
  `(Z : TopologicalSpace.Closeds X)`. Its reduced induced closed subscheme is
  `Scheme.IdealSheafData.vanishingIdeal Z` and its defining immersion is
  `(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι`.
* For every scheme (W) and étale (v:W\to X), the first conjunct quantifies
  `(W : Scheme.{u}) (v : W ⟶ X) [Etale v]`. The pullback closed subscheme is
  `pullback v (vanishingIdeal Z).subschemeι`; the reduced induced subscheme on
  (v^{-1}(Z)) is
  `(vanishingIdeal (Z.preimage v.continuous)).subscheme`. The existential
  isomorphism `e` is over (W), expressed by
  `e.hom ≫ ...subschemeι = pullback.fst v ...subschemeι`.
* The covering clause quantifies an arbitrary index type in the scheme universe,
  `ι : Type u`, schemes `W : ι → Scheme.{u}`, and maps
  `v : ∀ i, W i ⟶ X` with `[∀ i, Etale (v i)]`. Joint surjectivity is exactly
  `(⋃ i, Set.range (v i).base = Set.univ)`.
* The Cartier equivalence is rendered by
  `(vanishingIdeal Z).IsInvertible ↔
  ∀ i, (vanishingIdeal (Z.preimage (v i).continuous)).IsInvertible`.
  `IsInvertible` is the recorded effective-Cartier ideal notion, so this keeps
  the empty divisor (whose ideal is the unit ideal) in scope.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
* `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`,
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
* `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`,
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and `pullback.fst`.

The reduced-induced-subscheme declaration was read in full, including its
existence, reducedness, image, and uniqueness clauses. The Mathlib records were
checked against their declarations and docstrings: `IsLocallyNoetherian` is the
affine-local Noetherian scheme predicate, `Etale` is the affine-local étale
morphism class, `IsInvertible` is the effective Cartier ideal predicate, and
`pullback`/`pullback.fst` are the scheme fibre product and projection.

Edge cases checked against the statement are (Z=\varnothing), (Z=X), an
open immersion among the étale maps, a principal divisor on an affine scheme,
and an empty index family (which correctly cannot satisfy the displayed union
cover unless (X) is empty). The index universe is `Type u`, matching the
scheme universe, and no nonempty, characteristic, or dimension hypothesis was
added.

Searches made before writing the declaration:

* `msearch.py Q09 lem-trf-etale-reduced-cartier-descent leanfinder
  "Etale descent of reduced induced closed subschemes and effective Cartier
  divisors"`: successful hits for Mathlib étale predicates and étale locality,
  but no theorem stating this descent result.
* `msearch.py Q09 lem-trf-etale-reduced-cartier-descent loogle
  "AlgebraicGeometry.IsEffectiveCartierCenter, Scheme.IdealSheafData.IsInvertible,
  IsLocallyNoetherian"`: no hit (the queried effective-Cartier-center name is
  not imported by the search environment).
* `msearch.py Q09 lem-trf-etale-reduced-cartier-descent grep
  "reduced.*cartier|effective.*etale|cartier.*descent" Mathlib/AlgebraicGeometry`:
  no hit.
* `rg -n` over `WeilConjectures/` and `lean/Sheaf/` for
  `reduced.*cartier|effective.*etale|cartier.*descent|etale_reduced_cartier`:
  no declaration with this statement; only unrelated Cartier references.

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q09
lem-trf-etale-reduced-cartier-descent` compiled the module cleanly; the only
postponed proof is the required `sorry`.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix (2026-10-18)

The covering clause quantified `{ι : Type u}`, a universe restriction the node (an arbitrary
index set $I$) does not make. It now quantifies `{ι : Type*}`; joint surjectivity and the
Cartier equivalence are unchanged, and the statement only becomes more general, so no citer is
affected. The docstrings now attribute Tag 01J3 to Schemes (schemes.tex) rather than Descent.
The fixed module compiles cleanly with nt_compile.py (only the `sorry` warning).
