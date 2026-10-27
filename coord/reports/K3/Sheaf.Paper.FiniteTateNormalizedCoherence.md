## What changed

Restored the assigned quarantined module and replaced the body of
`AlgebraicGeometry.Scheme.finite_tate_normalized_coherence`, preserving its statement.
The proof constructs the etale pullback from `finiteEtaleTwistPullbackData`, proves
its normalization by tensor induction, and constructs the pro-etale isomorphism
by transport. Its square follows by cancellation. The exponent transition is
constructed from the existing etale transition data; its normalization and its
comparison square are proved using root inclusion injectivity, the root tower
cone equations, and the existing local lifted root tensor extensionality theorem.

A new module, `Sheaf.Paper.FiniteTateTransportedPullbackNormalization`, isolates
only the generator formula for the explicitly constructed pro-etale pullback.
The original node now records this route. Existing definitions, public imports,
and all target signatures are unchanged.

The complete main proof compiled in 27.3 seconds; profiling settings were removed
before delivery. The new module also compiled successfully (6.0 seconds with warm
imports). The delivery tool performs the final unprofiled compile and preflight.

## Proved and sorry left

Original holes closed: one,
`AlgebraicGeometry.Scheme.finite_tate_normalized_coherence`
(`lem-amb-finite-tate-normalized-coherence`). There are zero holes in the item module.
Its exponent conclusion, etale pullback normalization, isomorphism construction,
and commuting pullback square have complete Lean proofs.

Holes added: one,
`AlgebraicGeometry.Scheme.finite_tate_transported_pullback_normalized`
(`lem-amb-finite-tate-transported-pullback-normalization`). This is the only new
`sorry`. This delivery is a decomposition, with one hole closed and one added,
not a net closure of the coherence obligation. The new statement concerns one
fixed morphism, level, degree, and explicitly given isomorphisms. It asserts only
the pro-etale generator formula; it asserts neither existence, the comparison
square, nor exponent coherence. Its docstring gives the local root and mate
calculation still to formalize.

## No longer needed

The direct proof imports `Sheaf.Paper.AmbTateRootProjectionReduction` and
`Sheaf.AlgebraicGeometry.FiniteRootSiteComparison` are removed. The main proof
uses the tower cone equations and existing root tensor extensionality instead
of the large ringed root projection package. Thus
`lem-amb-tate-root-projection-reduction` and
`lem-weil-pbc-ringed-topoi-module-pullback-tensor` are no longer dependencies of
this node. The generic Mathlib monoidal adjunction identities suffice for the
etale tensor induction.

`lem-amb-finite-root-site-comparison` is not directly applied by the main proof;
it remains needed by the proved local root tensor detector and by the new
pullback normalization lemma. No claim is made that this module is globally
unused. No existing module, declaration, or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item was absent at assignment and listed in `coord/rework.tsv`, with its
source preserved under `quarantine/Sheaf/Paper/FiniteTateNormalizedCoherence.lean`.
That source was restored before proof work. Its one original hole and signature
were preserved as the baseline. No statement was found false or weakened.

The planned local tensor detection for exponent coherence already has a proved
library theorem, `finiteTate_local_root_tensors_hom_ext`; it need not be rebuilt.
The comparison square for the pullback map is formal cancellation once the map
is explicitly transported. The remaining geometric issue is its prescribed
root formula, now separated from both constructions and exponent coherence.
The blueprint unit route is retained.

## New nodes

`lem-amb-finite-tate-transported-pullback-normalization`, in
`dag/nodes/sec-smooth-purity/lem-amb-finite-tate-transported-pullback-normalization.json`,
records the fixed-level pullback generator calculation, with source, complete
proof plan, searches, and the exact Lean statement. The empty tuple (degree zero),
identity base changes, equal annihilator levels, empty schemes, and zero
coefficient modules introduce no extra hypotheses or exceptional cases. No
change record is needed: no existing statement or definition is changed.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
