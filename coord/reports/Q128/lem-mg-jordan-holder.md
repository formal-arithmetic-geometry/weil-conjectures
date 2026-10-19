## Worker report

Recorded the existing declaration `Representation.CompositionSeries.jordanHolder`
in `WeilConjectures.RepresentationTheory.CompositionSeries` (published upstream
source, read with `scompile.py --source`). No module or duplicate theorem is added.
The source docstring explicitly names this blueprint node. The older local source
checkout lacks this module, but the published source supplies it, as it does for
both dependencies' already reviewed bindings.

Hypotheses and clauses:

- A finite-dimensional Weil representation is a specialization of the theorem's
  `ρ : Representation k W V`, with `W` its Weil group. The upstream binders are
  independent types `k`, `W`, `V`, `[Field k]`, `[Group W]`, `[AddCommGroup V]`,
  `[Module k V]`, and implicit `ρ`. The theorem needs no finite-dimensionality
  assumption once the two finite composition series are supplied. Thus it applies
  directly to the node's representation, with no additional assumption.
- Any two composition series are `(s₁ s₂ : ρ.CompositionSeries)`.
- Simple factors are `s₁.factor i` and `s₂.factor (e i)`. The structure records a
  finite saturated chain of invariant subspaces from bottom to top. Its factor is
  the quotient of each next term by the previous term. The source's
  `isIrreducible_factor` and `isIrreducible_iff` identify these with nonzero
  representations having no nonzero proper invariant subspace.
- Permutation and multiplicities are `∃ e : Fin s₁.length ≃ Fin s₂.length`:
  the bijection matches each occurrence separately, including repeated factors.
- Isomorphism is `∀ i, Nonempty ((s₁.factor i).Equiv (s₂.factor (e i)))`.
  `Representation.Equiv` is a linear equivalence intertwining the group actions,
  so this is an isomorphism of Weil representations, not just vector spaces.

The statement dependency is `Representation.CompositionSeries` and its `.factor`
in `WeilConjectures.RepresentationTheory.CompositionSeries`, exactly the recorded
binding of `def-mg-weil-composition-series`. The proof dependency
`lem-mg-composition-series-exists` is `Representation.exists_compositionSeries`
in the same module. I read the full signatures and docstrings of these declarations.
I also read the current blueprint statement and its two proof paragraphs: selecting
and matching a simple first factor, then quotienting by it and inducting. The
published theorem proves the result through Mathlib's lattice Jordan–Hölder theorem
and the canonical subquotient equivalences; no new proof is supplied in this delivery.

Edge cases checked: zero representation (both factor lists empty), a simple
representation (one factor), repeated identical simple factors (indices retain
multiplicity), nonsplit extensions, and permuted factor orders. There is no
nonzero restriction in the uniqueness theorem and no restriction on characteristic
or algebraic closure. Independent universes in the existing interface cover the
node's objects. No statement correction or disputed statement is needed.

Searches made:

- `msearch.py leanfinder`, “Jordan Holder composition series representation”:
  eight hits, including `CompositionSeries.jordan_holder` and `.Equivalent` in
  Mathlib; no representation-specialized hit.
- `msearch.py leansearch`, “Any two composition series of a representation have
  isomorphic simple factors up to permutation”: eight hits, including the same
  Mathlib theorem and equivalence relation; no specialized hit.
- `msearch.py loogle`, `CompositionSeries.jordan_holder,
  Representation.CompositionSeries.jordanHolder`: zero hits; the latter name is
  unknown to the search index.
- `msearch.py grep`, `jordanHolder|jordan_holder`, `RepresentationTheory`: no hits;
  the same query in `Order` gives the general Jordan–Hölder file.
- Direct `rg` of Mathlib's `Order/JordanHolder.lean` finds the general theorem
  at line 458 and `Equivalent` at line 268. Direct `rg` of the older upstream
  `WeilConjectures` and the project's `lean/Sheaf` finds no duplicate declaration.
- `dag/lean_names_upstream.json` explicitly binds this blueprint id to
  `Representation.CompositionSeries.jordanHolder`. The dependency node records
  name the same published module. `scompile.py --source` confirms its actual full
  source and exact signature. I also read the imported
  `WeilConjectures.Mathlib.RepresentationTheory.Irreducible` source through that
  wrapper to check the simple-factor semantics.

Validation: `scompile.py` compiled the scratch existing-declaration probe cleanly
against both the sandbox overlay and published library. It checked the full explicit
universe-polymorphic theorem type and its application to a finite-dimensional
representation. `#print axioms Representation.CompositionSeries.jordanHolder`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
No delivered Lean files require compilation; `deliver2.py` also probes the existing
declaration before preflight.

## Second reading by Q128

This is the author's self-check, not an independent review; the maintainer performs
independent review of the delivery. Rereading the node beside the published source
confirmed both series use the dependency's exact composition-series structure,
the equivalence of `Fin` types retains every repeated factor, and the pointwise
`Representation.Equiv` preserves the Weil action. The theorem is more general in
not requiring finite dimensionality for uniqueness, and directly applies to the
node's finite-dimensional case. No mismatch or source alteration was needed.
