## Worker report

The module `lean/Sheaf/TraceFormula/FppfEtaleFiniteFreeRefinement.lean` states
`AlgebraicGeometry.Scheme.exists_etale_finiteLocallyFree_refinement` for an arbitrary scheme
`S : Scheme.{u}` and a small index type `I : Type v`. The input family is represented by
`S_i : I → Scheme.{u}`, maps `f i : S_i i ⟶ S`, and the exact Mathlib fppf covering predicate
`Presieve.ofArrows S_i f ∈ Scheme.fppfPrecoverage S`. This predicate includes flatness, local
finite presentation, and joint surjectivity and permits empty families when the target is empty.

The conclusion quantifies a small output index `A : Type v`, schemes `S' a` and `V a`, étale
maps `e a : S' a ⟶ S`, maps `p a : V a ⟶ S' a`, an original index `i a : I`, and a map
`r a : V a ⟶ S_i (i a)`. The clauses render the statement as follows:

* `∀ a, Etale (e a)` is the étale condition on every output member.
* `∀ a, Surjective (p a)` is surjectivity of each finite locally free refinement.
* `∀ a, (p a).IsFiniteLocallyFree` is Mathlib/WeilConjectures' finite, flat, locally
  finitely presented morphism predicate.
* `∀ s : S, ∃ a x, e a x = s` is joint surjectivity of the étale family.
* `∀ a, r a ≫ f (i a) = p a ≫ e a` is exactly
  `f_{i(a)} ∘ r_a = e_a ∘ p_a` in the node (Lean composition is written `≫`).

The module imports `Mathlib.AlgebraicGeometry.Sites.Fpqc` for `fppfPrecoverage`,
`Mathlib.AlgebraicGeometry.Morphisms.Etale` for `Etale` and
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree` for
`Scheme.Hom.IsFiniteLocallyFree`. Scheme morphisms and points are Mathlib's
`AlgebraicGeometry.Scheme` and their underlying coercions.

Dependency declarations used: `def-pc-scheme` uses `AlgebraicGeometry.Scheme` from
`Mathlib.AlgebraicGeometry.Scheme`; `def-weil-size-convention` is a metatheoretic convention
and contributes the explicit universe parameters `u` and `v`; `def-weil-etale-morphism` uses
`AlgebraicGeometry.Etale` from `Mathlib.AlgebraicGeometry.Morphisms.Etale`;
`def-pc-finite-locally-free` uses
`AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` from
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`; `def-weil-surjective-morphism` uses
`AlgebraicGeometry.Surjective` from `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`; and
`def-pc-fppf-site` uses `Scheme.fppfPrecoverage` from
`Mathlib.AlgebraicGeometry.Sites.Fpqc`.

Edge cases checked: `I` and `A` are arbitrary small types, including empty types; the
fppf-membership hypothesis then forces an empty target in the empty-family case. `S` and every
member may be empty. No nonemptiness, quasi-compactness, separatedness, characteristic, or
finite-index hypothesis is added. The independent index universe `v` preserves the chosen size
bound rather than restricting indices to the scheme universe `u`.

Searches made:

* `msearch.py ... leanfinder "An fppf covering ... finite locally free ..."`: eight hits for
  generic jointly-surjective precoverage and étale-site declarations; no refinement theorem.
* `msearch.py ... loogle "Scheme.Cover, fppfPrecoverage, Etale, IsFiniteLocallyFree, Surjective"`:
  zero hits (service reported unknown `Scheme.Cover`).
* `msearch.py ... grep "fppf.*finite.*free|finiteLocallyFree.*Etale" AlgebraicGeometry`:
  zero hits.
* `rg` over `WeilConjectures/` and project `lean/Sheaf/` found no declaration with this target
  id or theorem statement. The existing `FppfLocalFiniteFreeRefinement` file states the distinct
  two-level Tag 05WN refinement and only cites this target in its proof documentation.

The source statement is Tag 0DET (`lemma-dominate-fppf-etale-locally`); no correction or
`STATEMENT-DISPUTED` flag is needed.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
