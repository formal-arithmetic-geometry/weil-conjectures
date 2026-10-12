## What changed

The item module now proves `AlgebraicGeometry.Scheme.Modules.H.openFreeExtComparison`
with its signature and docstring unchanged. The proof applies the existing
`H.globalFreeExtComparison` on the scheme W, obtains the two Ext transports, and
composes the equivalences. It checks the R-scalar, S-scalar, and base-change
identities by separate Lean rewrites. Added proof-only imports:
`Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisGlobalExtComparison` and
`Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisOpenExtTransport`.

The new module states the purely Ext-valued open-extension/cartesian transport.
It contains no HOver group or H.baseChangeLinear map. It isolates the open
adjunction portion of the argument, leaving the global constant-to-free-sheaf
comparison in the existing global theorem. This is a proper decomposition:
the upper theorem requires both results and an explicit composition of
additive equivalences, rather than one application of a renamed statement.
The item node's proof, proof_deps, and proof_origin follow this route.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.Modules.H.openFreeExtComparison`
(node `lem-pc-open-free-ext-comparison`). Its proof has no sorry.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.H.openFreeExtTransport`
(node `lem-pc-open-free-ext-transport`), whose entire proof is `:= by sorry`.
The new declaration has its source and complete natural-language argument
in its docstring and node. No new definition or axiom is introduced.

The existing imported theorem
`AlgebraicGeometry.Scheme.Modules.H.globalFreeExtComparison`
(node `lem-pc-global-free-ext-comparison`) remains sorry; it was not modified.
This delivery is a decomposition, with one upper hole closed and one lower
hole added, not a sorry-free proof or positive net hole reduction.

Both delivered modules compile with lcompile.py in import order. No target,
existing signature, public import, or declaration visibility changes.

Edge cases checked for the new statement: W empty makes both Ext sources
zero; M zero makes the coefficient groups zero; W top reduces the transports
to canonical scheme isomorphisms. No step requires flatness of S over R,
quasi-coherence, finiteness, or nonempty schemes. The S-action in the second
transport is the full S-action, rather than only its restriction to R.

## No longer needed

No import was removed. The public MayerVietorisFreeComplex import remains
necessary because the statement uses H.openFreeSheaf. The proof does not use
`H.openFreeShortComplex_shortExact` or any two-open-cover hypothesis; the old
proof-dependency edge to `lem-pc-free-mayer-vietoris-short-exact` is replaced
by the global comparison and the new transport. The free-sheaf definitions
in the same module are still needed, so that module cannot be pruned.
No module is claimed globally unreachable by this delivery.

## Where the brief, the DAG or earlier work was wrong

The old node named only the scalar-comparison definitions and the free
Mayer--Vietoris short-exactness node. Neither gives the derived open-extension
adjunction or its cartesian Ext compatibility. The new transport records that
missing part explicitly; the global top-open case is reused from its existing
node. The unit record sk-thm-picard-rr has no realized statement or step node
that this reduction bypasses.

Searches actually run: LeanFinder for open-free-sheaf Ext versus restricted
cohomology; Loogle for CategoryTheory.Adjunction.extAddEquiv; grep for
extAddEquiv|extensionByZero|openFreeExtComparison; LeanSearch for the
inverse-image-compatible open Ext adjunction (unavailable, HTTP 500).
The generic exact-adjunction Ext equivalence in the source library is useful
for the remaining proof, but no search returned the complete cartesian
open-subscheme transport. Existing Zariski extension-by-zero adjunction and
exactness nodes were read and named in the new proof plan; étale variants
were not substituted for Zariski abelian sheaves.

Sources checked directly: Stacks 00A7 (adjunction), 01AK (exactness),
04J0 (localization and direct-image restriction), 01F7 (derived functoriality).
A direct construction of the global top-free-sheaf isomorphism was also
explored in scratchpad; its presheaf isomorphism compiled, but instance
checking for the full cohomology compatibility repeatedly exceeded the
single-file limit. That exploration is not part of the delivered Lean.

## New nodes

`lem-pc-open-free-ext-transport`, in
`dag/nodes/sec-picard-framework/lem-pc-open-free-ext-transport.json`, with
module `Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisOpenExtTransport`.
It states two Ext-to-Ext transports and their scalar and cartesian
coefficient compatibility. Its proof plan uses the exact open-extension
adjunction, the free-sheaf representing property, the cartesian
restriction/direct-image identity and the adjunction mates of the units.
It is strictly the open-subscheme transport part of the argument, and
neither states nor assumes the cohomology-to-global-Ext comparison.
No interface changes or forced adaptations; no change record is needed.

## Second reading by C1

1. **Visible changes and statements.** I diffed the delivered comparison module against the repository version. The existing theorem signature and docstring are unchanged; only proof-only imports and the proof body changed. The added transport module and node are explicitly listed above, with no target or existing declaration altered.

2. **Proof and axioms.** Both delivered modules compile with `lcompile.py --all` in import order. The comparison theorem has no local `sorry`; the only remaining hole is the named, documented transport theorem `H.openFreeExtTransport`, exactly as listed above. No definitions contain `sorry`, and the delivery introduces no axiom, unsafe, opaque, extern, or implemented_by declaration. The comparison proof is a direct composition of the existing global comparison and the transport theorem, and each of its three compatibility goals is discharged by the corresponding rewrite.

3. **Split-off statement.** I checked the transport statement against its use: it is strictly the open-subscheme Ext transport and scalar/cartesian naturality needed by the composition, while omitting the cohomology-to-Ext comparison supplied by the existing global theorem. Its hypotheses and conclusions match the displayed Lean declaration, and the docstring and node give the source and complete intended argument. A repository search found no existing declaration with this statement.

4. **Pruning and imports.** The comparison module retains `MayerVietorisFreeComplex` as a public import because its statement uses `H.openFreeSheaf`; the global comparison and open transport imports are proof-only. The old short-exactness dependency is no longer used by the proof and is removed from the node's proof dependencies. No additional import can be removed without breaking elaboration.

5. **DAG and unit route.** The comparison node's proof steps, dependencies, and origin now follow the Lean composition. The new transport node has the required statement, source, proof plan, dependencies, Lean record, chapter, unit, and split status. The unit's route is preserved: the global top-open comparison remains an explicit step, and the new node supplies only the open transport required afterward.

**Changes made during second reading:** added this section only; no Lean source or DAG content required repair.
