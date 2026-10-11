## Worker report

Module: `Sheaf.AlgebraicGeometry.FpqcDescendingTypesMorphisms`.
The theorem `AlgebraicGeometry.fpqcDescentEffective_of_affine` states the
one-member fpqc specialization of Stacks Tag 02W3. Its proof is `sorry`.

- A property of scheme morphisms is `P : MorphismProperty Scheme.{u}`.
- Clause (1), stability under every base change, is `hbase`. For
  `g : Y ⟶ V` and `h : V' ⟶ V`, `pullback.snd g h` is the base-changed
  projection, and `P g → P (pullback.snd g h)` states its property.
- Clause (2), finite disjoint unions including `m = 0`, is `hcoprod`.
  The components are indexed by `Fin m`; `Limits.Sigma.map g` is the
  induced morphism between their scheme coproducts.
- Clause (3), affine flat surjective effectiveness, is `haffine`.
  `[IsAffine X] [IsAffine S]` makes both schemes affine; `Flat f` and
  `Surjective f` are the two conditions on `f`; `D : Over.DescentDatum f V`,
  `P V.hom`, and `D.IsEffective` are the datum, its property, and effectivity.
- The conclusion's singleton fpqc cover is `hfpqc : Presieve.singleton f ∈
  Scheme.fpqcPrecoverage S`. The arbitrary datum is `D`, its property is
  `hV : P V.hom`, and the conclusion is `D.IsEffective`. The latter's
  definition supplies the scheme over `S`, the pullback identification and
  compatibility with the descent transport, equivalent to the stated
  isomorphism equation.

Dependencies used: `AlgebraicGeometry.Scheme` and `Scheme.Hom` (Mathlib,
`def-pc-scheme`); `Limits.pullback` and `pullback.snd` (Mathlib,
`def-pc-fibre-product`); `Limits.Sigma.map` and the scheme coproduct
instance (Mathlib, `lem-weil-pbc-scheme-coproduct-family`); `Flat` (Mathlib,
`def-weil-flat-morphism`); `Surjective` (Mathlib,
`def-weil-surjective-morphism`); `CategoryTheory.Over.DescentDatum` and
`CategoryTheory.Over.DescentDatum.IsEffective` from
`WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`; and
`Scheme.fpqcPrecoverage` (Mathlib, `def-weil-pbc-fpqc-covering`).

Edge cases checked: `m = 0` is admitted by `Fin m`; the empty base and
empty scheme are not excluded; identity covers and singleton covers remain
admitted. `Scheme.{u}` uses an arbitrary universe, and no characteristic
condition is imposed. The full family hypothesis is retained although the
one-member proof only needs its finite refinement instance.

Searches: `msearch.py leanfinder` with the full affine-reduction description
found only descent of morphism properties, not effectivity of descent data;
`msearch.py loogle` for `DescentDatum.IsEffective, fpqcPrecoverage, Flat`
returned no match; `msearch.py grep` for `DescendingTypes|descend.*types|
effective.*[Dd]escent|IsEffective` in `AlgebraicGeometry` returned none.
`rg` over the source `WeilConjectures` found `Over.DescentDatum.IsEffective`
and specialized descent results, but no Tag 02W3 reduction. The exact node
identifier was absent there by `grep -rn`; `rg` over the project's
`lean/Sheaf` found no matching theorem. Stacks Tag 02W3 was read from the
Stacks Project website because `literature/stacks-project/descent.tex` is
not present in this read-only checkout.

Server compile: clean, exit 0.

## Second reading by E1

The node's objects, hypotheses, and conclusion were matched against the file as follows.

- The property of scheme morphisms is `P : MorphismProperty Scheme.{u}`; this is the
  first explicit parameter of `fpqcDescentEffective_of_affine`.
- Hypothesis (1), stability under arbitrary base change, is
  `hbase : ∀ {Y V V'} (g : Y ⟶ V) (h : V' ⟶ V), P g →
  P (pullback.snd g h)`.  The schemes and morphisms have the same universe and
  `pullback.snd` is the recorded fibre-product projection.
- Hypothesis (2), finite coproduct stability for every `m ≥ 0`, is rendered by
  `hcoprod : ∀ (m : ℕ) (Y V : Fin m → Scheme.{u})
  (g : ∀ i, Y i ⟶ V i), (∀ i, P (g i)) → P (Limits.Sigma.map g)`.
  `Fin m` includes the empty family when `m = 0`.
- Hypothesis (3), effectiveness for flat surjective affine maps, is `haffine`.
  Its `[IsAffine X] [IsAffine S]`, `Flat f`, `Surjective f`, descent datum
  `D : Over.DescentDatum f V`, and premise `P V.hom` match the node exactly.
- The singleton fpqc cover is
  `hfpqc : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S`, with arbitrary
  `f : X ⟶ S`; the datum and its property are `D` and `hV : P V.hom`.
- The conclusion is `D.IsEffective`, exactly the effectiveness notion named by
  `def-pd-descent-datum`.  Its transport-form definition is equivalent to the
  source's descended scheme, pullback identification, and compatibility equation,
  so no conclusion clause is lost.

No mismatch was found and no source or Lean text required changing.  Universes are
arbitrary (`Scheme.{u}`); no characteristic, nonempty, Noetherian, or finiteness
condition is added.  The zero scheme and empty base remain allowed, as do `m = 0`,
identity covers, and singleton covers.

Independent searches were run with `msearch.py ... leanfinder` for effective fpqc
descent of morphism properties, and with `rg` over Mathlib, `WeilConjectures`, and
the project's `lean/Sheaf`.  The hits concern descent of properties or abstract
stack infrastructure; none states this 02W3 reduction.  The existing
`CategoryTheory.Over.DescentDatum.IsEffective` declaration was opened and is the
dependency used by the file.  The module compiles cleanly with `scompile.py`.
