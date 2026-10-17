## What changed

Repaired `lean/Sheaf/AlgebraicGeometry/ProjectiveGraphTwistVanishing.lean` after the
upstream sync, preserving every existing active declaration's signature and visibility.
Restored the commented, proved private helper `projective_ample_affine` for arbitrary
finite coordinate types. Its standard affine charts and pulled coordinate sections
also handle an empty coordinate type without a separate case.

Proved `projective_ample_affine_pullback` by uniqueness of left adjoints and invariance
of ampleness under isomorphism. Proved `graph_twist_isInvertible_and_affine_ample` by
constructing the closed graph over S, base changing it to each affine open V, and
explicitly composing the pullback/restriction isomorphisms of the integral twist.

Proved `exists_isZero_higherDirectImage_graph_twist` by applying the existing
`exists_isZero_higherDirectImage_twist_on_affine_open` to the coherent structure module,
taking the supremum of its thresholds over a finite affine subcover of S, gluing
vanishing with `isZero_of_iSup_eq_top`, and mapping the left unitor through the higher
direct-image functor. The structure module's sheaf-level invertibility instance is
installed with explicit universe parameters to infer finite presentation and finite type.

Updated the existing node's proof, proof dependencies, and proof origin to describe these
source interfaces. In particular, step 2 explicitly cites the existing, source-proved
general graph-lift theorem (`lemma-weil-pbc-chow-embedding-over-x`, following its current
blueprint update) and projective-space base-change theorem
(`lemma-nagata-projective-space-base-change-pullback`). Both are already in the imported
source ProjectiveSpace module; no new mathematical obligation is introduced.
No definition or statement changed; no consumer adaptations or change records are needed.
The module compiles through lcompile.py without warnings after redundant imports are removed.

## Proved and sorry left

Closed all three originally active holes, with no holes added:

- `AlgebraicGeometry.Scheme.Modules.projective_ample_affine_pullback` (private).
- `AlgebraicGeometry.Scheme.Modules.graph_twist_isInvertible_and_affine_ample` (private).
- `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_graph_twist`
  (node `lem-pc-m1-projective-graph-twist-vanishing`).

Also restored the commented private theorem `projective_ample_affine` with a complete
proof. It was not an active sorry and is not counted among the three holes closed.
There are zero sorry occurrences left in the delivered module, and zero split-offs.
The proof continues to use the existing affine-open vanishing interface and its
existing transitive obligations; this delivery does not claim to close those.

## No longer needed

Removed the retired re-export modules from this module's proof imports:

- `Sheaf.AlgebraicGeometry.ProjectiveAmpleInvertible`, replaced by `import all` of
  `WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible` to access the actual
  source private helpers.
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`, using the already
  imported source module directly.

Removed redundant direct imports of
`WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible` (ordinary duplicate),
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`,
`WeilConjectures.AlgebraicGeometry.TensorPullback`, and
`WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`.
These source modules are still available through needed proof dependencies, so their
nodes are not pruned. No mathematical proof-dependency nodes are bypassed and the
unit's route is preserved. Public imports are unchanged.

## Where the brief, the DAG or earlier work was wrong

The sync retired the Sheaf re-export modules, so importing all of the Sheaf wrapper
no longer exposes private declarations belonging to the source module. Import the
source modules with `import all` for `tensorPullback_invertible`,
`homOfGlobalSection_appTop_one`, and `nonvanishingLocus_iso`.

The existing public theorem docstring describes reindexing nonempty coordinates and
an explicit empty-source branch. The implemented coordinate-chart proof works directly
for every finite type and needs neither branch. The docstring is retained; the node's
proof describes the actual route.

Sources checked: Stacks coherent.tex, Tag 02O5
(`proposition-proper-pushforward-coherent`) and Tag 02O1 (`lemma-kill-by-twisting`),
the assigned node and all its proof-dependency signatures, and the unit realization
record. Edge cases: empty coordinates give an empty covering family and hence an
empty source; an empty base gives an empty finite affine subcover and supremum zero;
no common degree bound is newly asserted beyond the existing affine-open theorem.

## Second reading by F4

1. **Statements and signatures.** I diffed the delivered module against the repository
version. The public target and all existing active declaration signatures are unchanged;
the restored private affine helper was commented out in the upstream snapshot and is a
proof repair, not a change to an existing interface. Verdict: pass.

2. **Proof and axioms.** The module and its sandbox import set compile with `lcompile.py`.
There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or
`debug.skipKernelTC` occurrences in the module. A scratch copy of the full delivered
source followed by `#print axioms` shows exactly `propext`, `Classical.choice`, and
`Quot.sound` for the target; there is no `sorryAx`. Verdict: pass.

3. **Split-off statements.** No statements were split off and no nodes were added. The
recorded searches found no existing theorem matching the target or its helper results;
the proof uses the existing affine-open vanishing, pullback-adjunction, nonvanishing,
and ample-isomorphism interfaces. Verdict: pass.

4. **Pruning and route.** The proof follows the finite affine-cover route through the
existing affine-open vanishing theorem, and the projective chart route for ampleness.
The two source `import all` imports are required to access the source modules' private
proof helpers; redundant wrapper and direct imports were removed and listed above.
The unit's finite-cover/affine-vanishing route is retained. Verdict: pass.

5. **DAG agreement.** The existing node's `proof`, `proof_deps`, and `proof_origin`
describe the declarations and interfaces used by the delivered proof. Its statement,
chapter, unit, and `lean` record are unchanged, and no new hole or node is present.
Verdict: pass.

The second reading required no mathematical or Lean changes. I added this review
record and corrected its axiom report using a scratch copy of the delivered source.
