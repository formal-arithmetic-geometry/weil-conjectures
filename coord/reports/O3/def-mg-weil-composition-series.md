## Worker report

This is an `existing: true` delivery.  The canonical declarations are already in
`WeilConjectures.RepresentationTheory.CompositionSeries`:

- `Representation.CompositionSeries` (source lines 157--168), whose `series` field is
  `_root_.CompositionSeries (Subrepresentation ρ)` and whose `head_eq` and `last_eq`
  fields identify the endpoints with `⊥` and `⊤`;
- `Representation.CompositionSeries.factor` (source lines 178--181), the successive
  quotient `(s.series i.succ).subquotient (s.series i.castSucc)`.

The node's finite-dimensional Weil representation is the specialization of the source's
representation `ρ : Representation k W V` with `[Field k]`, `[Group W]`, and
`[AddCommGroup V] [Module k V]`; finite dimensionality is supplied by the monodromy
representation context and is not needed to define the filtration.  The source's cover
relation is strict inclusion, and `isIrreducible_factor` (lines 185--187) states that each
factor is irreducible; its irreducibility structure includes nontriviality, so this is
exactly “nonzero and has no nonzero proper Weil-stable subspace.”  The factor abbreviation
retains repetitions because its index is every `i : Fin s.length`.

The statement has no additional hypothesis beyond the node's representation data and no
conclusion is weakened.  The monodromy-data dependency is the recorded
`AlgebraicGeometry.Monodromy.RepresentedDegreeDatum` in
`WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy`; its `rep` field is the
Weil representation used here, while the composition-series structure itself is generic
and therefore does not duplicate monodromy data.

Edge cases checked: the zero representation admits the length-zero series (head and last
are both `⊥ = ⊤`); a nonzero simple representation has the two-term series `0 < V`; an
empty index of factors occurs exactly for the zero case; and arbitrary finite-dimensional
representations, including reducible ones and repeated isomorphic factors, are covered.
No characteristic, algebraic-closure, or nontriviality assumption is introduced.

Searches performed on 2026-10-17:

- `msearch.py ... leanfinder` with “finite filtration of a finite-dimensional Weil
  representation by Weil-stable subspaces with simple successive quotients”: eight hits,
  including general `CompositionSeries`/Jordan--Hölder infrastructure but no competing
  declaration.
- `msearch.py ... loogle` with `Representation.CompositionSeries,
  Representation.Subrepresentation, CompositionSeries`: zero hits; the service reported
  `Representation.CompositionSeries` as unknown in its index.
- `msearch.py ... grep` with `CompositionSeries|composition series|simple successive quotient`
  in `WeilConjectures`: seven textual hits, none defining another composition-series notion;
  the exact source module was found in the current published side library.
- Direct `rg` over `dag/lean_names_upstream.json`, the source checkout, and
  `lean/WeilConjectures` found the blueprint binding and the exact declarations.  The
  current server source was confirmed with
  `scompile.py --source WeilConjectures.RepresentationTheory.CompositionSeries`.

No new module, dependency module, new node, statement correction, or
`STATEMENT-DISPUTED` flag is needed.

## Second reading by N3

I reread the target node, its `def-wf-monodromy-data` dependency, and the complete source
module.  The endpoint equations render `0 = V₀` and `V_t = V`; the root composition-series
relation renders every strict adjacent inclusion; `factor` renders each quotient in the
same order; and `isIrreducible_factor` supplies the simple/nonzero clause.  The generic
source representation specializes to the finite-dimensional monodromy representation, so
all objects and clauses of the node are retained.  The source declaration and recorded
signature are unchanged and no duplicate declaration is introduced.
