## What changed

In `Sheaf.WeilSheaf.NativeOpenProperForgetting`, proved `hearts` and
`proper_normalization` without changing their statements.
All existing public declarations, definitions, and public imports are preserved.
The original `open_proper` proof is still `by sorry`; this is a partial delivery
of a module with several holes, rather than a decomposition.

`hearts` applies `IsoAlgebra.fixedPair_forget_properties` to the actual native
Frobenius autoequivalence. The exact homology comparison transports native qcqs
stratification in both directions, and the existing faithful-exact boundedness
lemmas give the boundedness equivalence. This uses the native heart's existing
Grothendieck instance and does not construct another coefficient category.

`proper_normalization` uses a fully proved private generic helper. Its four local
unit equations are obtained from the existing right-derived uniqueness and
composition APIs. Cancellation of the homotopy-composition identifications gives
the equation for the specific four-factor `properComparison`, on every complex.
Explicit preservation of K-injectives gives invertibility of both units.
The existing characteristic binder is preserved, with a scoped unused-section-
variable linter setting because the normalization proof itself is formal and
needs no characteristic assumption.

The existing `proper_frobenius` proof is preserved. It landed in the shared
repository during the session, after the first source read; it is not counted as
progress of this delivery. A generic scratch calculation of the normalization
was checked separately before integration. Only the item module and its existing
DAG node are delivered.

The final module was compiled through `lcompile.py` within the 60-second limit.
The delivery tool also checks the module with its axiom/declaration probe.

## Proved and sorry left

Current delivery-base holes: 3. Holes closed: 2. Holes added: 0. Split-off statements: 0.

Closed:

- `AlgebraicGeometry.NativeWeilOpenProper.hearts`.
- `AlgebraicGeometry.NativeWeilOpenProper.proper_normalization`.

One original hole remains, unchanged:

- `AlgebraicGeometry.NativeWeilOpenProper.open_proper`, node
  `lem-sf-native-weil-open-proper-forgetting`.

The remaining theorem must establish shift compatibility and the Frobenius
square for the independently constructed derived actions, then combine them
with naturality of the canonical compactification comparison. The degreewise
identity in `proper_frobenius` alone is not asserted to prove that derived square.
There is no `sorry` in a helper or definition, and no new module or node.
The six previously proved theorem bodies are preserved.

## No longer needed

Removed six proof-only imports from the item:

- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.AlgebraicGeometry.CompactificationMiddleOverBase`.
- `Mathlib.Topology.Constructible`.

The actual native framework already supplies the Grothendieck, Frobenius
reindexing, exact open-extension, and left-exact proper-pushforward APIs.
The formal normalization holds for arbitrary source/target native hearts, so
finite-type properties of the compactification's middle scheme are unnecessary
for this proof. The converse constructibility implication uses the existing
stratified-lisse predicate directly, without a Noetherian-space argument.

Accordingly removed these dependencies from the item's proof plan:

- `def-weil-pbc-proetale-site`.
- `def-weil-size-convention`.
- `lem-pur-ringed-site-grothendieck-abelian`.
- `lem-sf-weil-frobenius-action-resolutions`.
- `lem-weil-proetale-weakly-etale-localization`.
- `lem-pur-site-restriction-module-adjunction-exact`.
- `lem-weil-pbc-ringed-topoi-module-adjunction`.
- `lem-sfb-compactification-middle-over-base`.
- `def-weil-constructible-subset`.

These are no longer direct proof obligations of this node; this does not claim
their source modules are globally unused. No module is withdrawn and no upstream
declaration is removed. Dependencies still needed by the remaining
`open_proper` argument stay in the DAG. The unit has no realized statement or
steps bypassed by these changes.

## Where the brief, the DAG or earlier work was wrong

The earlier plan did not exploit the existing native Grothendieck and exactness
instances, or the unit equations of the four-factor canonical comparison. These
provide the completed clauses directly. The Noetherian constructibility detour
is unnecessary because the native stratified-lisse predicate already includes
the constructibility of strata. The DAG now distinguishes these implemented
proofs from the remaining derived-action and shift argument.

The current server queue was checked again: this is a three-hole proof item,
not a zero-hole repair. The first read showed four holes; the intervening
`proper_frobenius` landing accounts for the difference. Its recorded global-build error names three dependency imports;
the delivered module compiles against the published build after the proof changes.
No target statement, public signature, definition, or coefficient action changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.WeilSheaf.NativeOpenProperForgetting": "c95c7bfd2923ddcb1c2f2c4af38ca7023d443f9a"}, "results": {"Sheaf.WeilSheaf.NativeExceptionalHomTransport": {"hash": "b1bfb8088d3ec79a7fe43d0f8a201a0ae6d86776", "status": "OK"}}, "seconds": 107, "time": "2026-10-28T05:11:09+0800", "transitive": 0, "version": 1}
```

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
