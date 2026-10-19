## Worker report

The module `Sheaf.AlgebraicGeometry.AffineEtaleSplitNeighbourhood` states
`AlgebraicGeometry.exists_affine_etale_split_neighbourhood` with proof `sorry`.
It uses Mathlib's `Scheme`, `Spec`, `Etale`, `IsAffine`, scheme pullbacks, finite
coproducts, and `IsLocalRing.closedPoint`. The theorem binds `S` and `U` in the
same scheme universe with `[IsAffine S] [IsAffine U]`, an étale `f : U ⟶ S`, an
algebraically closed field `Ω`, a geometric morphism `bar_s`, an image point `s`,
and the equality `bar_s (closedPoint Ω) = s`.

The Lean rendering of each clause is as follows. The existential `V`, `g`,
`IsAffine V`, `Etale g`, and `bar_v` gives an affine pointed étale
neighbourhood, with `bar_v ≫ g = bar_s`. The natural number `n` is the
nonnegative integer. The scheme `W`, map `w : W ⟶ V`, and `[Etale w]` give the
étale remainder. The isomorphism
`e : pullback f g ≅ (∐ fun _ : Fin n => V) ⨿ W` and
`e.hom ≫ coprod.desc (Sigma.desc (fun _ : Fin n => 𝟙 V)) w = pullback.snd f g`
state that the decomposition is over `V`; the pullback is Mathlib's
`CategoryTheory.Limits.pullback`.

The singleton fibre clause is
`∀ x : V, g x = s ↔ x = bar_v (IsLocalRing.closedPoint Ω)`. The empty-remainder
clause is `∀ x : W, (w ≫ g) x ≠ s`. For each `i : Fin n`, the map `a i` is
specified exactly as the copy inclusion followed by the coproduct inclusion,
`e.inv`, the pullback projection to `U`, and `bar_v`:
`a i = bar_v ≫ Sigma.ι (fun _ : Fin n => V) i ≫ coprod.inl ≫ e.inv ≫
pullback.fst f g`. The condition `ha : ∀ i, a i ≫ f = bar_s` says these are
`S`-lifts. Finally
`E : Fin n ≃ {q : Spec (.of Ω) ⟶ U // q ≫ f = bar_s}` and
`∀ i, E i = ⟨a i, ha i⟩` give the required bijection, including `n = 0`.

Statement dependencies and declarations used:

* `def-pc-scheme`: `AlgebraicGeometry.Scheme` (Mathlib).
* `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` (Mathlib).
* `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` (Mathlib).
* `def-weil-geometric-point`: `IsAlgClosed` and
  `AlgebraicGeometry.Scheme.SpecToEquivOfField` (Mathlib); the module uses the
  former directly and `Spec` for the morphism.
* `def-weil-pbc-pointed-etale-neighbourhoods`: the recorded Mathlib match is
  `CategoryTheory.Functor.Elements` applied to
  `(AlgebraicGeometry.Scheme.pointSmallEtale bar_s).fiber`; the theorem renders
  an object of this category directly by `V`, `g`, `bar_v`, and
  `bar_v ≫ g = bar_s`, so no private category copy is introduced.
* `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and
  `pullback.fst`/`pullback.snd` (Mathlib). Finite scheme coproducts are the
  Mathlib `Sigma.ι`, `Sigma.desc`, and `coprod` constructions from
  `Mathlib.AlgebraicGeometry.Limits`.

Edge cases checked against the statement and construction: `n = 0` is allowed
by `Fin 0`, with the empty coproduct and an empty lift equivalence; `U` may be
empty, yielding this case; `W` may be empty; the marked fibre is represented by
`IsLocalRing.closedPoint Ω`, whose spectrum has one underlying point; and no
closedness or characteristic assumption has been added.

Searches made: `msearch.py ... leanfinder "affine etale morphism splits near
geometric point into copies and remainder"` returned only generic `Etale`,
standard-etale, and finite algebra splitting results, with no scheme
neighbourhood splitting. `msearch.py ... loogle "Scheme, Etale, pullback,
coproduct"` returned no result (the query's `Scheme` identifier was unknown to
Loogle). `msearch.py ... grep "split.*etale|etale.*split"
Mathlib/AlgebraicGeometry` returned no hits. Repository `rg` found no existing
`exists_affine_etale_split_neighbourhood` declaration and no source declaration
of this theorem. The existing Mathlib/source declarations listed above were
opened and their signatures/docstrings checked. No STATEMENT-DISPUTED issue or
node correction was found.

## Second reading by NV

I reread the node and the module side by side. The affine hypotheses are the two
`IsAffine` instance binders; the étale hypothesis is `[Etale f]`; the geometric
point is `bar_s` over the explicitly named image `s` through `hs`. The first
existential gives precisely an affine étale pointed neighbourhood. The next
existentials give a natural number, a remainder étale over `V`, and a
pullback decomposition whose displayed equality is the structure map to `V`.
The next two universal clauses respectively say the `s`-fibre of `V` is exactly
the marked point and that no point of `W` maps to `s`. The final existential
specifies every copy map, proves it lies over `S`, and gives a bijection with all
`S`-morphisms from `Spec Ω` to `U`. Thus every hypothesis and every clause of the
node is present, with no added finiteness, separatedness, characteristic, or
closed-point assumptions. The `Fin n` encoding includes the empty case.
