## Worker report

The module `Sheaf.DeligneLaumon.HProjectivePermanence` states the finite-projective-space
permanence lemma.  It binds schemes `Z`, `T`, and `B`, morphisms `f : Z ⟶ T` and
`g : T ⟶ B`, and the separatedness class `[IsSeparated g]`.  The natural number `n`
represents the source's integer `n ≥ 0`; the given map `i` has target
`ℙ(ULift.{u} (Fin (n + 1)); B)`, with `hi : IsClosedImmersion i` and the over-`B`
equality `i ≫ (ℙ(...) ↘ B) = f ≫ g`.  The conclusion is an existential map `j` into
`ℙ(ULift.{u} (Fin (n + 1)); T)` with `IsClosedImmersion j` and the over-`T` equality
`j ≫ (ℙ(...) ↘ T) = f`.  Thus the same finite coordinate set, and hence the same `n`,
is retained.  The only proof is the named theorem's expected `sorry`.

The statement dependencies are used as follows:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, giving `Scheme.{u}` and scheme
  morphisms `⟶`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, giving the
  `AlgebraicGeometry.IsSeparated` class used on `g`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, giving
  the relative projective-space notation `ℙ`, its structural morphism, and the canonical
  `IsHProjective` convention.  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` is imported
  for the projective-space construction used in the statement.

The source proof plan is represented in the docstring: separatedness makes the graph of
`f` closed, base change preserves the supplied closed immersion, composition preserves
closed immersions, and projective-space base change identifies the target with the same
`Fin (n + 1)` projective space over `T`.  No flatness, noetherianity, quasi-compactness,
or separatedness of `f` or `Z` is added.

Edge cases checked before writing: `n = 0` gives `Fin 1` and the same argument for
projective zero-space; `f = 𝟙 _` and `g = 𝟙 _` reduce to the given embedding; an empty
source has the empty closed immersion; empty and non-reduced schemes are allowed by the
scheme-theoretic closed-immersion hypotheses.  The use of `ULift.{u} (Fin (n + 1))`
keeps the coordinate type in the scheme universe and does not identify independent
universes.

Searches made: `msearch.py ... leanfinder "A scheme morphism X to Y is projective if its
composite with a separated morphism is projective"` returned only properness,
separatedness, and finiteness cancellation; `msearch.py ... loogle
"AlgebraicGeometry.IsProjective, AlgebraicGeometry.IsSeparated"` returned no hits and
reported the unknown identifier; `msearch.py ... grep
"IsProjective|IsHProjective|projective.*of_comp|projective.*permanence"
AlgebraicGeometry` found no theorem.  `rg` in `WeilConjectures/` and `lean/Sheaf/` found
`IsHProjective.comp` and projective base-change results, but no cancellation theorem with
this same-`n` conclusion.  The recorded DAG searches and the Stacks source review likewise
found no duplicate declaration.  No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by NW

I reread the module and the node clause by clause.  The three scheme/morphism binders,
separatedness hypothesis, natural-number/same-coordinate parameter, closed-immersion
hypothesis, and equality over `B` all occur explicitly.  The conclusion has exactly one
new map, the same `Fin (n + 1)` target over `T`, its closed-immersion property, and the
required equality over `T`; no extra property is asserted.  The module imports each
statement dependency and no private replacement definition.  The signature recorded in
the node is the theorem signature before `:=`, with whitespace normalized as in preflight.

## Saved-packet repair and current self-check

On 2026-10-18 UTC the required initial dry run reported only that `lean.statement`
included the trailing `:=`, whereas preflight extracts the signature before it.
The record now stops before that delimiter; the Lean statement is unchanged.
The report also now names the actual imported projective-space module.

I reread the current node, the saved Lean file, the full signatures and docstrings
of `Scheme`, `Scheme.Hom`, `IsSeparated`, `IsClosedImmersion`, and the canonical
`IsHProjective` obtained with `scompile.py --source` (its local source path is absent).
I checked `ProjectiveSpace` and its structural projection and `isPullback_map`,
and reread Stacks morphisms.tex, `lemma-projective-permanence` and
`lemma-H-projective-base-change`. Each given embedding in dimension `n` is
quantified explicitly, so the conclusion retains that dimension, including `n = 0`.
The over-base equalities have the stated orientation and compositions. All
universes and variables are explicit. No mathematical change or additional
notion is needed. This is a self-check of the retained packet; no new agent was
started, as the dispatcher brief forbids it.

The delivery metadata date is 2026-10-18, as returned by `date -u +%F`.
