## What changed

Replaced the hole in `AlgebraicGeometry.Etale.SfP1Transport.sectionComparison`
with the calculation for its diagonal and projection exchange squares. The
statement and original public import are unchanged. Ordinary constant-object
base change gives inverse transport of both units; exchange naturality pastes
those formulas. Proper forget-supports naturality and cancellation of the
coefficient comparison finish the coordinate calculation, using one remaining
normalization theorem on a single self-product.

`OrdinaryFiniteConstantBaseChange` proves the ordinary equation for every
commutative square and every commutative coefficient ring. It reuses U2's
proved `ordinaryFiniteUnitPullback_comp` from `OrdinaryFiniteUnitPullbackComp`,
node `lem-amb-ordinary-finite-unit-pullback-comp`, and applies the generic
mate-unit identity. `OrdinarySupportedUnitComparison` reuses F1's proved
`supportedDerivedUnit_eq` from `OrdinaryFiniteConstantUnitComp`, node
`lem-sp-ordinary-finite-constant-unit-comp`, to express the constant-object unit
through the ordinary derived adjunction.

The requested standalone timing initially exceeded the limit. Profiling isolated
45.1 seconds of kernel checking in the repeated composition calculation; the
unit API also exceeded the limit in the initial batch. Reusing these existing
library theorems removes both private reconstructions. The profiler options are
removed and no resource limit is changed. The revised base-change file compiles
alone in 6.5 seconds; the revised unit API compiles alone in 5.9 seconds.

The proved inverse-unit API and ordinary diagonal/projection pasting API isolate
the ordinary calculation. The remaining theorem
`diagonalSection_forgetSupports` is natural in a map from the tensor unit to any
coefficient object on the original self-product. It contains neither the
coordinate isomorphism nor either exchange square. It states the support
normalization step, not another copy of the assigned theorem.

The unclaimed transport-data module receives two implementation repairs.
`diagonalLift` and `projectionComparison` use the same canonical proper
forget-supports isomorphism through `ordinaryProperForgetComparison`, which
records its ordinary endpoint. The diagonal coefficient map is the intact
inverse constantComparison. Existing declaration signatures, public attributes
and main's public imports are preserved. The sole added public import supplies
the endpoint wrapper. File-local irreducibility and sequential declaration
checking avoid repeatedly expanding the large derived-functor construction.
No resource limit or source-library module is changed.

This returned-delivery repair starts from current main's E1 transport-data
implementation and node. It preserves `traceComposite`, `presentationTrace`,
`presentationTrace_assoc`, and E1's trace construction verbatim. Main's
`SfP1SupportedExtMapData` remains the unique owner of `supportedMap`.
The duplicate unlanded constructor draft remains excluded.

The transport-data node is copied from current main, adding only the endpoint
wrapper to `stmt_deps`. E1's `proof`, `proof_deps`, `proof_origin`, Lean declaration
list, `reviewed_proof`, and all remaining metadata are preserved. This repairs
both DAG-check failures in the earlier return; no foreign construction proof is reset
and no review metadata is authored by this worker.

The implementation change records are
`coord/changes/u3-sf-p1-diagonal-lift-endpoints.md` and
`coord/changes/u3-sf-p1-projection-endpoints.md`. They request the independent
statement review required for definitions in a target's dependency closure.
The reviewer C-d31b0 passed the previous packet, but landing rejected the
reviewer replacement filename `u3-sf-p1-diagonal-lift-endpoints.md`. The tool
maps replacement change records by `<stem>.change.md`, not by the repository
basename. Both records now state their delivery path and the exact accepted
replacement filename, so the next review can supply corrections using the
documented mapping. No delivery record was missing.

The transport-data implementation and its node were reconstructed from current
main, reapplying only the endpoint repairs and the wrapper statement dependency.
Current main has fifteen other direct importers, including the four consumers
restored since the preceding repair. All twenty-five files passed server compilation with exit code zero
(result `dc0df12e82047670164fa26e`): ten delivery modules and all fifteen
current direct importers. `OrdinaryFiniteConstantBaseChange` took 30.0 seconds;
the item took 37.4 seconds. Every validation-only source copy was checked byte
for byte against current main, then removed before delivery. The packet contains
only its ten Lean modules. No consumer adaptation or quarantine withdrawal is
delivered.

## Proved and sorry left

The original module had one hole, in
`AlgebraicGeometry.Etale.SfP1Transport.sectionComparison`. Its replacement body
contains no `sorry`.

These new public theorems are proved without holes:

- `AlgebraicGeometry.Etale.ordinaryFiniteConstant_baseChange`.
- `AlgebraicGeometry.Etale.supportedDerivedUnit_eq_adjunction`.
- `AlgebraicGeometry.Etale.SfP1Transport.constantUnit_inverseProperExchange`.
- `AlgebraicGeometry.Etale.SfP1Transport.ordinarySection_exchange`.
- `AlgebraicGeometry.Etale.SfP1Transport.diagonalLift_eq_ordinaryProperForget`.
- `AlgebraicGeometry.Etale.SfP1Transport.projectionComparison_eq_ordinaryProperForget`.

All private helpers are proved. `ordinaryProperForgetComparison` is a real
construction of the original canonical isomorphism, with no hole or arbitrary
witness. Main's existing `SfP1Transport.supportedMap` remains unchanged and has no hole.

One hole is added and remains:
`AlgebraicGeometry.Etale.SfP1Transport.diagonalSection_forgetSupports`, in
`SfDiagonalSectionForgetSupports.lean`, node
`lem-sf-diagonal-section-forget-supports`. Its docstring gives the complete
compactification and adjunction-composition argument. The outstanding step
identifies the specified compact-support compositor with the ordinary
compositor after proper forget-supports, evaluates the resulting section map
at the constant object, and applies naturality in the coefficient map.

This is a decomposition: one original hole closed, one strictly smaller
normalization obligation added, net zero holes within this packet. The ordinary
exchange calculation and the proof combining the parts are complete. This is
not an unconditional proof of the original theorem.

## No longer needed

No existing module is withdrawn and no original public import is removed.
The unpublished `OrdinaryFiniteUnitPullbackComparison` draft and its draft node
remain excluded. The returned, unlanded duplicate supportedMap module and node
are also excluded; main's existing supportedMap declaration and owner node
remain unchanged.

`OrdinaryFiniteConstantBaseChange` no longer directly imports
`OrdinaryFiniteUnitPullbackHom`, `UpperStarConstantSheafComp`, or
`LeftDerivedUpperStarSingle`: the existing proved composition theorem replaces
their local reconstruction. `OrdinarySupportedUnitComparison` no longer directly
imports `OrdinaryFiniteUnitPullbackHom`: F1's existing proved unit formula
replaces that reconstruction. These library modules remain needed transitively;
none is withdrawn.

The item's proof no longer uses the planned nodes
`lem-sfb-ringed-derived-monoidal-comparisons`
(`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`) and
`lem-sf-diagonal-kernel-integral-triangles`
(`Sheaf.AlgebraicGeometry.SfDiagonalKernelIntegrals`) as proof steps. Explicit
constant-object mate calculations replace the first; the single-self-product
proper-support normalization replaces the proposed use of the second. These
nodes are removed from this item's proof dependency list. Their modules are
not claimed globally unused: transport-data retains its original imports and
any transitive dependence on them.

No coefficient-line, Kummer-orientation, Ext-class, trace, decomposition or
projective-line integral theorem is needed for the ordinary exchange
calculation. The unit route and its realized nodes are preserved.

## Where the brief, the DAG or earlier work was wrong

The planned ringed-derived theorem provides a generic system, rather than the
component equation for these specific ordinary etale derived functors. The
diagonal-integral triangles theorem does not state the proper
forget-supports/compositor normalization. Neither statement is disputed.
The new nodes record the actual ordinary calculation, the remaining support
normalization, and the proved component APIs used by the proof.

The adopted source already proves constant-sheaf composition and its derived
single-object version, and U2's library module provides the proved composition
formula. F1's library module already proves the supported-unit formula.
Consequently ordinary unit transport needs no new assumed base-change statement. It requires no properness, finiteness, nonemptiness or nonzero-ring
hypothesis. The remaining normalization keeps the original properness and
coefficient hypotheses and applies to empty schemes and the zero ring.

The implementation repair records ordinary endpoints before component
composition while preserving the canonical maps and all public signatures.
The first packet independently relocated a declaration that A4 had already
moved on main; that duplicate was removed in the preceding repair. An earlier
return identified another concurrency error: the retained packet predated E1's
trace factorization and node review. This repair preserves all of E1's current
implementation and node metadata, reapplying only U3's two endpoint repairs.

## New nodes

- `lem-sf-ordinary-finite-constant-base-change`: the proved constant-object
  exchange equation for any commutative square.
- `lem-sf-ordinary-supported-unit-comparison`: the proved constant-object
  unit formula for the ordinary derived adjunction.
- `def-sf-ordinary-proper-forget-comparison`: the canonical proper
  forget-supports isomorphism with its ordinary endpoint recorded.
- `lem-sf-diagonal-section-forget-supports`: the remaining support normalization
  on a single self-product, natural in the coefficient map.
- `lem-sf-p1-diagonal-lift-proper-forget`: the proved defining equation for
  diagonalLift in terms of the canonical endpoint wrapper.
- `lem-sf-p1-projection-proper-forget`: the proved component equation for
  projectionComparison in terms of the same wrapper.
- `lem-sf-ordinary-proper-unit-inverse-exchange`: proved inverse transport
  of constant-object units for a Cartesian proper square.
- `lem-sf-p1-ordinary-section-exchange`: the proved pasting of the diagonal and
  projection ordinary unit calculations.

The existing transport-data node gains only the endpoint wrapper as a
construction dependency. Main's existing supportedMap owner dependency and
review metadata are preserved. Its mathematical statement and public Lean
signatures are unchanged. The item's proof fields describe the actual
ordinary calculation and single-self-product normalization.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
