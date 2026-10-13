## What changed

Replaced the remaining base hole by a genuine decomposition into existence of a
normalized natural transformation and componentwise invertibility of that same
transformation. The base proof uses the componentwise isomorphism criterion and
`asIso`, retaining the supplied normalization equations. Its original statement,
the extension statement, and the final normalization statement are unchanged.

Added `AffinePushforwardComparisonCoordinates`, with the original explicit maps
parameterized by the ordinary comparison, and kept the two original coordinate
names as transparent aliases. The lower theorem signatures now refer to this
shared API instead of duplicating the large constructions. All coordinate data
are fully constructed. Added one unfold in the existing extension proof; the
ordinary comparison is locally irreducible for proof elaboration. Details and
users are in `coord/changes/affine-tilde-pushforward-coordinate-api.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.affineTildePushforwardCohomologyNormalization_base`.
This is a decomposition, not a complete proof of the affine calculation: one
original hole is closed and two strictly partial lower holes are added (net -1).
The existing extension and final existence proofs are preserved and compile.

Every remaining sorry introduced by the delivery:

- `AlgebraicGeometry.exists_affinePushforwardCohomologyEdge`, node
  `lem-pc-affine-pushforward-cohomology-edge-exists`: existence and normalization
  of a natural map, with no invertibility conclusion.
- `AlgebraicGeometry.affinePushforwardCohomologyEdge_isIso`, node
  `lem-pc-affine-pushforward-cohomology-edge-isIso`: invertibility of components
  assuming a normalized natural map, with no existence conclusion.

The parent and coordinate API contain no sorry. Each lower hole is a named public
theorem in its own module, with the full mathematical argument in its docstring.
Both statements allow arbitrary unbounded complexes and zero rings. A normalized
map is not assumed to be an arbitrary comparison isomorphism.

## No longer needed

No existing library imports, dependency modules, or nodes are pruned. The new
generic coordinate module omits `WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde`: it takes
the ordinary comparison as an input and does not construct the pullback comparison. The base
node now uses the two lower edge-map nodes; its old mathematical ingredients
remain needed in those lower proofs. Removed the earlier attempt's uncommitted
restatement node and the false/repackaged comparison/identity helpers from the
sandbox; these were never library nodes and are not counted as pruning.

## Where the brief, the DAG or earlier work was wrong

The retained sandbox did not match its report or node. It contained an existence
of an isomorphism and a second theorem asserting the whole base conclusion from
that existence; the node described a different theorem. The report even claimed
an independent second reading that had not validated this retained code.
The previous dry-run rejection was therefore a valid restatement rejection, not
a tool failure. This delivery discards that attempt and supplies two true proof
parts combined in Lean. No second-reading section is supplied by this worker.

The local literature checkout is absent. Read the cited Stacks pages 0AVW, 08D4
and 06Z0 online and obtained the official `perfect.tex` in the sandbox scratchpad;
the Lean-facing refinements are marked agent-written in the nodes.
LeanSearch returned HTTP 500; its searches are recorded as unavailable, not as
negative results. LeanFinder, Loogle and source searches found the generic
homology and natural-isomorphism APIs, but no duplicate normalized affine theorem.

## New nodes

`def-pc-affine-pushforward-comparison-coordinates`: the actual generic coordinate
composites, with no holes. `lem-pc-affine-pushforward-cohomology-edge-exists`:
existence/naturality and identity normalization of the edge map.
`lem-pc-affine-pushforward-cohomology-edge-isIso`: componentwise invertibility
from affine acyclicity and transport along the affine derived equivalence.
The existing base node's proof and dependencies are updated to the Lean assembly.

Unchanged direct clients `AffineBaseChangeTildeMateFactorization` and
`AffineBaseChangeTildeOrdinaryComparison` compile against the delivered API
(29 and 48 seconds). No forced adaptations are needed.

Change record: `coord/changes/affine-tilde-pushforward-coordinate-api.md`.

## Second reading by U1

1. I compared the delivered normalization module with the repository version.
Existing declaration statements are unchanged; the two coordinate definitions
are the interface changes recorded in the change record. No target statement or
definition changed silently.

2. All four delivered modules compile cleanly with `lcompile.py --all`. The base
hole is closed. The two lower theorems remain named `sorry` proofs with matching
nodes and source/proof docstrings. No delivered definition contains `sorry`, and
the declarations use no forbidden axiom or command.

3. The split statements match the concrete coordinate maps: existence supplies a
normalized natural transformation, while the isomorphism statement assumes that
same normalization and proves componentwise invertibility. They are strictly
partial parts of the parent argument, not restatements. They cover unbounded
complexes and zero rings. The cited affine results do not already provide these
normalized statements.

4. The proof uses the shortest local route: obtain the normalized map, apply the
componentwise natural-isomorphism criterion, package it with `asIso`, and retain
the equations. The coordinate API removes duplicated constructions. The parent
node depends on exactly the two lower declarations invoked; their affine
ingredients remain dependencies of the lower nodes. The identity-normalization
then extension route is retained, and the unit's pre-existing empty `realized`
fields are untouched.

5. I checked the DAG records against Lean. The parent proof and `proof_deps` name
the two invoked lower declarations. Each new node has matching module,
declaration, statement, source, proof plan, search record, and split status. The
coordinate definition node records fully constructed maps and no proof hole.

I changed only this report during second reading.
