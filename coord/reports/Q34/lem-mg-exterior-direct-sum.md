## Worker report

The item is already stated by the source declaration
`Representation.exteriorPowerDirectSumEquiv` in
`WeilConjectures.RepresentationTheory.ExteriorPowerDirectSum`; therefore no
new Lean module is added.  The declaration is recorded in the node with
`existing: true` and branch `slopmaster2`.

The source declaration has explicit universes and parameters `{k : Type u}`
with `[Field k]`, `{W : Type w}` with `[Group W]`, a natural number `s`, and
`V : Fin s → Type v`.  Its hypotheses
`[∀ i, AddCommGroup (V i)]`, `[∀ i, Module k (V i)]`, and
`[∀ i, FiniteDimensional k (V i)]` render the node's finite-dimensional Weil
representations.  The argument `ρs : ∀ i, Representation k W (V i)` renders
`V₁, …, V_s` with their common Weil action, and `N : ℕ` renders “for every
N”.  The conclusion
`((directSum ρs).exteriorPower N).Equiv
(directSum fun n : {n : Fin s → ℕ // ∑ i, n i = N} ↦
piTprodExteriorPower ρs n.1)` is the canonical equivariant decomposition;
the subtype is exactly the tuples with sum `N`, and
`piTprodExteriorPower` is the tensor product of the individual exterior
powers.  The source docstring explicitly states that terms with
`n i > dim (V i)` are zero.  The item has no statement dependencies.  Its
proof dependency is `def-wf-weil-category`; that dependency supplies the
meaning of Weil representation data for the blueprint proof, while the
existing source declaration already supplies this item's statement.

Edge cases checked against the source definition are `s = 0` (the unique
empty tuple and the zero direct sum), `N = 0`, `N > 0` with `s = 0` (both
sides are subsingleton/empty as appropriate), zero-dimensional summands,
and indices with `n i > finrank (V i)` (the corresponding exterior power is
zero).  The `Fin s` index and the explicit universe `v` do not exclude these
cases.

Searches made:

- `msearch.py ... leanfinder "canonical equivariant decomposition exterior power direct sum representations"` returned only generic exterior-power declarations in Mathlib and no full direct-sum representation decomposition.
- `msearch.py ... loogle "Representation.exteriorPowerDirectSumEquiv, Representation.exteriorPowerProdEquiv"` returned no hits locally.
- `msearch.py ... grep "exteriorPowerDirectSumEquiv|exteriorPowerProdEquiv" RepresentationTheory` returned no hits in the read-only checkout.
- `msearch.py ... grep "exteriorPowerDirectSumEquiv" /home/ubuntu/weil-src-slopmaster2/WeilConjectures` returned no local-checkout hit; the checkout is stale for this source file.
- `python3 /home/ubuntu/weil-launcher-nt/scompile.py --source WeilConjectures.RepresentationTheory.ExteriorPowerDirectSum` printed the current server source, including the exact declaration and its blueprint docstring.
- A server compile of a temporary file importing that module and running `#print Representation.exteriorPowerDirectSumEquiv` and `#check @Representation.exteriorPowerDirectSumEquiv` succeeded and confirmed the recorded signature.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q34

I reread the node statement and the server source declaration independently.
Every node clause is present: a finite family of finite-dimensional
representations over one field, an arbitrary exterior degree `N`, the
sum-indexed tuples with nonnegative natural entries, the tensor product of
individual exterior powers, and the canonical equivariant equivalence.
The source declaration's `Fin s` family is the precise Lean encoding of
`V₁,\ldots,V_s`; its tuple subtype enforces the sum equation and hence the
implicit `n_i ≥ 0`.  The explicit finite-dimensional typeclass is exactly
the node hypothesis, and no extra mathematical hypothesis is introduced.
The source's recursive `s = 0` and `s + 1` branches cover the empty-family
and all positive-family cases, while the `N = 0` branch covers the degree-zero
edge case.  No mismatch was found, so no change was needed after this
second reading.
