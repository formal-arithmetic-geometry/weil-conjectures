## What changed

The signature of `integralProjectionSupportFactorCoordinates` is unchanged. Its proof
now transposes the proper/open composite to an actual integral morphism between
constructible objects, computes finite coordinates of that morphism, and compares it
with the recorded support map using the proved Milnor joint-faithfulness theorem.
Private proved helpers handle adjunction transposition, naturality, preservation of the
factored support identification, and equality transports. The support-preservation
calculation reuses the generic private argument in `CommonProjectionProperFactor`,
then passes to inverse components; its tensor-specific public API is unnecessary here.
No shared definition or existing public interface is changed. A change record
documents the module-local reducibility hints and additional namespace opening
flagged by the conservative command scanner.

Four new modules give explicit finite coordinate isomorphisms and separate the three
missing unary/finite compatibility facts. The coordinate definitions are actual
composites of the supplied normalization isomorphisms. They contain no postponed data.
The new proof imports are private.

## Proved and sorry left

The original hole in
`WeilConjectures.FixProjectionCompactification.integralProjectionSupportFactorCoordinates`
is reduced to the following three independent parts. This is a decomposition, not a
claim to have proved all underlying normalization results: one upper hole is closed
and three lower holes are added.

- `WeilConjectures.FixProjectionCompactification.integralProjectionDirectFactorEvaluation`
  (`lem-sf-integral-projection-direct-factor-evaluation`): evaluation of a proper mate
  on an arbitrary input; it contains no open or support comparison.
- `WeilConjectures.FixProjectionCompactification.integralProjectionOpenFactorEvaluation`
  (`lem-sf-integral-projection-open-factor-evaluation`): evaluation of the open
  coefficient map; it contains no proper image or support identification.
- `WeilConjectures.FixProjectionCompactification.finiteSupportFactorRealization`
  (`lem-sf-finite-support-factor-realization`): compatibility of the finite support
  realization with the proper/open identification at one finite coefficient ring;
  it contains neither integral reduction nor coefficient-system realization.

Each remaining hole is a named public theorem in its own module with its source and
complete mathematical proof in the docstring. The factor coordinate data module has
zero holes. All four new modules compile, and the original module's complete
combining proof compiled in 26.5 seconds under the standard limits. Temporary
profiling options and the resulting style warnings were removed for delivery;
the delivery tool's clean compile and axiom probes passed. Its first preflight
found a metadata-only error: the inferred `directIso` signature had been recorded
with its definition body. The node now records exactly `def directIso`, matching
the source signature; its mathematical statement specifies all five constructions.
The three required search categories and the proof-local command change record
were also completed before resubmission.

## No longer needed

No original public import is removed, and no module is withdrawn or claimed pruned.
The direct proof route no longer performs the original global support-value
expansion. Its explicit proof dependencies on the qcqs compact-support realization,
open reconstruction effectivity and integral residue Tor are replaced by the separate
unary evaluation facts and the existing support-adjunct finite-coordinate theorem.
In node terms, `def-weil-integral-rational-qbar-compact-support`,
`lem-sf-open-reconstruction-effectivity`, and `lem-coef-integral-residue-tor` cease to
be direct proof dependencies of this node. These results remain transitively needed by
the coordinate definitions and normalizations, so their modules cannot be pruned.
`def-fix-six-functor-datum` is retained among the original statement dependencies.

## Where the brief, the DAG or earlier work was wrong

The earlier plan gave a mathematical expansion but no Lean identification of the
separate proper/open maps with the support adjunct. In particular, finite derived
system evaluation alone does not justify equality of system morphisms. The new
argument first lifts the composite to an actual integral morphism whose endpoints are
constructible, and uses the already proved constructible joint-faithfulness theorem
there. It does not assume evaluation is faithful on all derived systems. The unit route
is preserved; none of its realized statements or steps is bypassed.

Edge cases were checked in the mathematical argument: zero inputs, identity proper
maps, identity or empty open immersions, and the positive quotient exponent `m+1`
all obey the same adjunction and naturality identities. No nonempty, nonzero or
flat-quotient hypothesis is introduced.

## New nodes

`def-sf-integral-projection-factor-evaluation-data` records five explicit coordinate
isomorphisms (`directIso`, `extensionIso`, `direct`, `extension`, `support`), all built
from existing coefficient normalization data.

`lem-sf-integral-projection-direct-factor-evaluation` isolates evaluation of the unary
proper adjunction mate. Its proof uses the existing completed-pullback evaluation
statement and the two specified counit equations.

`lem-sf-integral-projection-open-factor-evaluation` isolates evaluation of the unary
open coefficient comparison, using the prescribed open scalar mate and openProjection.

`lem-sf-finite-support-factor-realization` isolates the finite-ring composition and
proper/open normalization calculation, before any integral or system coordinates.

All four nodes retain the item's chapter and unit. The original node's proof and
proof dependencies follow the finite-coordinate argument. The change record is
`coord/changes/X9-integral-projection-support-factor-coordinates.md`; it documents
the proof-local commands conservatively flagged by preflight. No other existing
module or public interface is changed.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
