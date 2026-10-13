## What changed

Proved `FormalGlueing.exists_extension_transport` with its signature unchanged in
`Sheaf.RingTheory.FormalGlueingExtensionTransport`. Added only proved private helpers.
The proof uses the existing `FormalGlueing.canonical_functor_maps` statement to obtain the
canonical morphism for `j`, whose components are prescribed uniquely by its heterogeneous
map equalities; it makes no assumption about the maps of `Can`.

The private `factor_transport` helper constructs the desired Hom for arbitrary glueing
objects from a morphism with bijective charts and a factorization of the prime map.
Both compatibility equations are proved by cancellation of surjections. Prime-localized
surjectivity follows from the existing Hom compatibility, the alpha equivalences and
`LinearMap.baseChange_surjective`. Overlap-localized surjectivity follows from
`IsLocalizedModule.map_surjective`. All module casts and chart restrictions are proved
explicitly. Empty chart families, zero modules, and zero localizations are included.

Replaced the proof import `Sheaf.Paper.FormalGlueingCanonicalMaps` by
`Sheaf.RingTheory.FormalGlueingCanonicalFunctorMaps`, and added the proof import
`Mathlib.LinearAlgebra.TensorProduct.RightExactness`. Updated the item's DAG proof,
proof dependencies and proof origin to this route. No public import, definition,
statement, or signature changed.

## Proved and sorry left

Closed one hole: `FormalGlueing.exists_extension_transport`
(node `lem-weil-pbc-formal-glueing-extension-transport`).
No sorry remains in the item's module. No hole was added and no new statement was split off.

The existing imported statement `FormalGlueing.canonical_functor_maps`
(node `lem-weil-pbc-formal-glueing-canonical-functor-maps`) has a proof in the current repository; the local compiled dependency still carries sorryAx.
This delivery proves transport from that statement; it does not claim to close its
transitive axioms. The private factorization and transport helpers contain no sorry.

## No longer needed

Removed the direct proof import `Sheaf.Paper.FormalGlueingCanonicalMaps` and removed
`lem-weil-pbc-formal-glueing-canonical-maps` from this node's direct proof dependencies.
Its fraction-formula/naturality arguments are supplied by the existing canonical
morphism assignment, whose module still imports it transitively. Thus this is pruning
of a direct edge only; no module is claimed to leave the targets' import closure.

No other original dependency is pruned. Scalar extension and localization are still
used in the construction and cancellation argument. No unit statement or realized
unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface error was found. The planned direct naturality checks
can be reused through the existing canonical morphism assignment. The cancellation
step only requires surjectivity of the localized prime map, which follows from Hom
compatibility; a separate comparison bijectivity calculation is unnecessary.

The newly landed canonical morphism assignment was initially absent from the last
green local compiled cache. During that wait the transport proof was checked in a
scratch example taking precisely the assignment and heterogeneous component equations
as parameters. Scratch files are not part of the delivery. The published dependency arrived during the session; the actual module then compiled
cleanly through `lcompile.py` (16.3 seconds). The final delivery gate is
`deliver3.py U4 Sheaf.RingTheory.FormalGlueingExtensionTransport --no-push`.

## Second reading by U4

1. Compared the delivered module with the repository version. The public theorem statement and all existing declaration signatures are byte-for-byte unchanged; only proof imports, private helpers, and the proof body differ. Verdict: pass.

2. Compiled the module with `lcompile.py`; it succeeds with no errors. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The axiom audit reports only permitted foundations plus the transitive `sorryAx` from the compiled canonical-map dependency chain. Verdict: pass.

3. Searched the library and Mathlib for the transport and cancellation results. The proof uses the existing canonical functor maps declaration and standard base-change and localization surjectivity lemmas; it adds no split-off statement or duplicate declaration. Verdict: pass.

4. Read the proof from the target downward. It constructs the canonical morphism, transports chart bijectivity, and proves both compatibility equations by surjective cancellation. The direct canonical-maps import is removed and the DAG proof dependencies match the imports used. The unit route and realized steps are retained. Verdict: pass.

5. Checked the node against the Lean proof and report. The node's proof, dependencies, origin, and declaration metadata describe the actual route; no statement or definition changed. Verdict: pass.

Changed only the report by adding this review record; no proof or interface repair was needed.
