## What changed

Replaced the hole in `AlgebraicGeometry.Etale.projectiveLineExceptionalBaseChange`
with the finite trace-model argument and the existing
`CategoryTheory.isIso_mateEquiv_app_of_counit`. The original signature and public
import are unchanged. Its three new imports are proof imports. A proved private
helpers identify the canonical map with its defining mate and prove the generic
counit-to-base-change criterion. Local irreducibility
attributes keep Lean from unfolding the large derived-functor constructions;
no upstream definition or attribute is changed.

`ProjectiveLineTraceModel` constructs the trace on a presented projective line,
its actual inverse-projection counit and its twisted-pullback comparison. The
ordered projection is invertible by the existing arbitrary-base proper torsion
projection theorem. All data are explicit composites; no object is chosen from
an unproved existence statement.

`ProjectiveLinePresentations` proves the change from optional-singleton to two
homogeneous coordinates and the universal-property presentation of a pullback,
including both projection equations. The main proof obtains normalized finite
splittings and both diagonal integrals from
`exists_arbitraryBaseFiniteP1Integrals`, applies the one-base adjunction step at
each base, substitutes their specified counits into the concrete counit square,
and cancels exchange with its inverse in the mate calculation.

The remaining work is separated into two sourced statements: the diagonal
adjunction at one base, and the equality of the already constructed counits
across a square of compatible presentations. Neither has exceptional inverse
image base change as its conclusion. The unit's projective-line diagonal and
trace route is retained.

## Proved and sorry left

Original item: one hole, in
`AlgebraicGeometry.Etale.projectiveLineExceptionalBaseChange`. Its proof body is
now complete from the two intermediate statements. This is a decomposition,
not a completed proof of the mathematics: one upper hole closed, two lower
holes added, net minus one hole closed.

New proved declarations:

- `AlgebraicGeometry.Etale.isIso_finiteP1Projection`.
- `AlgebraicGeometry.Etale.exists_projectiveLinePresentation`.
- `AlgebraicGeometry.Etale.exists_projectiveLinePullbackPresentation`.

The only new holes are:

- `AlgebraicGeometry.Etale.exists_presentedFiniteP1TraceAdjunction`, node
  `lem-asd-presented-projective-line-trace-adjunction`. This proves both diagonal
  triangles for the specified trace counit, then transports the adjunction to
  the presentation. It asserts no base-change result.
- `AlgebraicGeometry.Etale.presentedFiniteP1Counit_baseChange`, node
  `lem-asd-presented-projective-line-trace-counit-base-change`. This is the
  trace/projection exchange equality for explicit maps, with no adjunction or
  exceptional inverse-image hypothesis or conclusion.

Both have complete source-based proofs in their docstrings. The four helper
modules compiled together through lcompile: presentations (3.9 s), model (47.0 s),
adjunction statement (49.3 s), and counit statement (48.6 s). The final main proof
compiled in 12.2 s, with kernel checking of its theorem taking 0.18 s. Profiling
options were removed for delivery. No definition has a hole. Edge cases checked in the statements: arbitrary non-Noetherian base,
identity change of base, empty base, zero coefficient ring, and N=1. No affine,
boundedness, constructibility or extra Tor hypothesis has been introduced.

## No longer needed

No original Lean import was removed and no module is withdrawn. No whole module
is claimed pruned.

The old planned direct dependency `def-amb-p1-trace` and its Noetherian interface
`Sheaf.AlgebraicGeometry.ProjectiveLineTrace` are not used directly. The proof
uses the already stated arbitrary-base finite splitting and constructs its
counit from `ordinaryFiniteProjectionNatTrans` and `ordinaryFiniteTensorTrace`.
The abstract `HasTateTwist`/`ProjectiveLineAdjunctionBaseChange` route is not used:
the actual finite line is sufficient. Existing source declarations and their
imports remain in the library, including any transitive dependencies; this
report makes no claim that their modules are globally unnecessary.

The former top-node proof dependencies on finite twist, derived tensor, fibre
products and inverse image are replaced by the concrete model/presentation
nodes in its direct dependency list. The corresponding mathematics remains
needed through those nodes and the finite splitting API. Unique right adjoint,
compact support and exceptional adjunction are still used in the final mate
lemma. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The original plan requires arbitrary bases, while the
existing `ProjectiveLineFullAdjunction`, `OrdinaryFiniteP1Adjunction` and ordinary
trace-counit specialization impose Noetherian hypotheses, and
`SfAffineBaseP1TraceAdjunction` imposes affine base. They therefore do not
instantiate on this item's arbitrary S. The newer finite splitting/diagonal
integral theorem does have the required generality and is reused.

A local alias for the projection caused a large definitional comparison during
kernel checking. Using the projection directly, together with the proved mate
API and local irreducibility controls, restores the per-file compile limit.
The comparison and counit statements use the direct derived inverse-image
notation at the exchange interface, avoiding expansion of its recorded wrapper.

The coordinate type differs between the item and the finite splitting API.
This is repaired by a proved coordinate isomorphism and a proved compatible
pullback presentation, rather than an implicit definitional identification.

A read-only traversal of the overlaid node records found no new-node cycle. It
also exposed existing cycles wholly among shared dependency records (including
the derived exchange replacement chain and the supported Kummer/Cartier chain).
These records were not edited; the maintainer can check them independently.

## New nodes

`def-asd-presented-projective-line-trace-model` records the concrete trace,
counit, comparison and the proved projection isomorphism. It uses the existing
ordinary finite arrows and tensor trace rather than duplicating their maps.

`lem-asd-projective-line-presentations` records the two proved presentation
lemmas. Coordinate reindexing is the existing theorem from the source library;
the second lemma is the pullback universal property.

`lem-asd-presented-projective-line-trace-adjunction` is the one-base diagonal
argument. Its tools are the already stated finite diagonal integrals and the
coordinate trace contractions. They supply the unit/triangle route in the
source, not a replacement for that route.

`lem-asd-presented-projective-line-trace-counit-base-change` records the concrete
trace/projection square for compatible presentations. Its projection-exchange
tool is the existing ringed exchange/tensor coherence; the finite splitting's
trace clause supplies the other square. The normalized line comparisons and
exchange pasting transport it to the supplied presentations.

The blueprint-wide searches for projective line, counit, reindexing and
presentations found the existing Noetherian adjunction and general framework
nodes, but no statement with these arbitrary-base normalized finite interfaces.
Mathlib searches were actually run through msearch: LeanFinder returned ordinary
scheme-module adjunctions, Loogle returned mkOfUnitCounit and its component
identities, and grep returned only linear-algebra trace base change.

All nodes are in the item's chapter and unit. The top node's proof,
proof_deps and proof_origin follow the Lean reduction. No existing definition,
public signature or target statement changes, and no consumer adaptation or
change record is required.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
