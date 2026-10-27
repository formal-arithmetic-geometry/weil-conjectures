## What changed

Only `Sheaf.Paper.ClopenCommonCompactSupport` and its existing DAG node change.
All existing public signatures, definitions and public imports are preserved.
Proof imports and proved private helpers implement normalized descent of natural
isomorphisms from bounded-below etale origins, with identities and cocycle.

The finite-sum proof factors the specified map through the image of the actual
biproduct decomposition. Restriction preserves bounded constructibility by the
existing finite-clopen bounds and intrinsic pullback-model comparison. The final
two sum-transport proofs use the original component-independence theorem.

## Proved and sorry left

Closed 8 of the original 10 holes (namespace
`WeilConjectures.PurityFiniteSetting`):

- `clopenSupportCanonicalComparison_existsUnique`
- `clopenSupportCanonicalComparison_coherence`
- `clopenSupport_geometry`
- `clopenSupport_sum`
- `clopenSupportSumMap_naturality`
- `clopenSupport_restriction_constructible`
- `clopenSupportSumMap_compactification`
- `clopenSupportIndependentSumComparison_eq`

Two original holes remain, both with node
`lem-pur-clopen-common-compact-support` and their original docstrings:

- `clopenSupport_insertion`: the two normalized insertion adjunctions,
  off-diagonal vanishing, constructible preservation and decomposition.
- `clopenSupport_independent`: compatibility of normalized open-extension
  composition with the canonical compactification comparison on etale origins,
  followed by descent.

Added holes: 0. Split-off statements: 0. Every new private helper is proved.
The final two sum-transport theorems depend on the retained independence hole;
this delivery does not claim that they are axiom-free independently of it.

## No longer needed

No modules are withdrawn, no original public imports are removed, and no original
planned dependency of the retained insertion hole is pruned. In particular
`Sheaf.Paper.FiniteClopenDerivedDecomposition` and its node
`lem-pur-finite-clopen-derived-decomposition` remain needed for that proof plan.
The proved restriction theorem uses finite-clopen constructibility bounds and
`openSquareDerivedPullbackModel` directly.

The delivery does not import `Sheaf.Paper.OpenExtensionFiniteTor` or
`Sheaf.SixFunctors.GraphFrobeniusOpenExchange`, explored during the earlier attempt.
It introduces no finite-Tor or Frobenius theory for this clopen statement.
No claim of globally pruned modules is made.

## Where the brief, the DAG or earlier work was wrong

No statement correction was required. The saved report from the previous attempt
incorrectly claimed the insertion proof was complete; its actual Lean body was
still `sorry`. This report and the node now record that hole accurately and retain
its original planned dependencies.

The component-independence conclusion needs compatibility of composition with
compactification comparisons, in addition to their naturality and cocycle.
The original named theorem remains open rather than moving that requirement to
a renamed theorem or assuming a new coherence datum.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
