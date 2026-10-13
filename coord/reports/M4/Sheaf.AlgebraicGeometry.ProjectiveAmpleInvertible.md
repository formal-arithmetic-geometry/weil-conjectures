## What changed

Proved `AlgebraicGeometry.projective_closedImmersion_ample_invertible` in
`Sheaf.AlgebraicGeometry.ProjectiveAmpleInvertible`, preserving its full signature,
universe, public visibility, chosen adjunction units and coordinate sections.

The actual witness is `i ⁻¹ᵁ ProjectiveSpace.standardOpen _ _ k`. The Proj twist is
invertible by the source instance, and uniqueness of left adjoints transports the
usual pullback's invertibility to tensor pullback twice. A proved private helper
recovers a structure-module morphism from its value at one. The existing theorem
`nonvanishingLocus_eq_compl_support_zeroLocus` and the source theorem
`Proj.compl_support_zeroLocus_unitToTwist` identify the integral coordinate locus.
Two applications of `nonvanishing_tensorPullback` give the precise twice-pulled
coordinate locus in the statement. The source's `iSup_standardOpen` and
`isAffineOpen_standardOpen`, followed by Mathlib's affine preimage and finite compact
union lemmas, give the requested compact affine cover. The inverse right unitor
transports each coordinate to tensor power one, proving absolute ampleness.

Added proof imports of `SectionNonvanishingZeroLocus`, `NonvanishingTensorPullback`,
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection` and
`import all Sheaf.AlgebraicGeometry.AmpleIso`. The latter deliberately accesses its
already proved private `nonvanishingLocus_iso` helper; no dependency module is adapted.
Updated only `proof`, `proof_deps`, `proof_origin` of the item's DAG node, and its
proof docstring. All public imports are retained because they describe the interface.

Compilation succeeds without errors or warnings in about five seconds, with default
heartbeats and transparency settings. An initially expensive inference of the
coordinate morphism was resolved by explicitly specifying its grading and the ring
section type, rather than altering any definition or increasing resource limits.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.projective_closedImmersion_ample_invertible`
(node `lem-weil-pbc-projective-ample-invertible`). There are zero `sorry`s left in the
item and zero holes added or split off. Both new private helpers are fully proved:
`tensorPullback_invertible` and `homOfGlobalSection_appTop_one`.

This is a proof from existing declarations, not a decomposition into new holed
statements. Remaining transitive dependencies are the existing library's; the
module's axiom check is performed by the delivery dry run.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`;
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistGluedIdentification`;
- `Sheaf.AlgebraicGeometry.TensorPullback` (already publicly supplied by
  `TensorPullbackAdjunction`);
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (already publicly supplied
  by the interface imports);
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist` (publicly supplied by
  the proof import `ProjectiveSpace.CoordinateSection`).

The proof no longer needs nodes
`lem-weil-pbc-projective-space-standard-charts`,
`lem-weil-pbc-projective-space-twist-glued-identification` or a direct
`def-weil-residue-field` dependency. Their first two modules are removed entirely
from this item's direct imports; downstream/global reachability is the maintainer's
queue calculation. The weaker source facts actually needed (affine charts and cover)
are already proved and are applied directly. No chart coordinate-ring equivalence,
coordinate-ratio equation, glued integral twist comparison or unique chart coefficient
argument is needed here. Consequently their proof-only lower dependencies are not
imported for this item.

## Where the brief, the DAG or earlier work was wrong

The DAG's glued-versus-Proj comparison is unnecessary for the source library's actual
interface: `ProjectiveSpace.twist` is already defined as the usual pullback of the
Proj twist. The final route does not even require that comparison; it uses the
integral coordinate zero-locus calculation followed by tensor pullback twice. The
DAG's full standard-chart conjunction is likewise unnecessary; the source already
proves its covering and affine-chart special cases. Nothing mathematical or any
statement was corrected.

`f` and `hi` do not enter the geometric argument once the closed immersion into
projective space over `Spec A` is given. Both binders stay unchanged; `hi` is explicitly
referenced to keep compilation warning-free. The argument also covers the zero ring,
the empty scheme and n = 0; it needs no points to exist and no nontriviality of A.

The existing nodes `lem-sc-nonvanishing-tensor-pullback` and `lem-sc-ample-iso` serve
as generic stalk-comparison tools from the curve-estimates family. They do not replace
any unit's own statement or proof step. The item is not a realized statement or step
of `sk-thm-p1`, whose route is unchanged. No new nodes, statement changes, forced
adaptations or new data definitions were introduced.

Sources read: Stacks [01PS](https://stacks.math.columbia.edu/tag/01PS),
[01PU](https://stacks.math.columbia.edu/tag/01PU), and
[01NG](https://stacks.math.columbia.edu/tag/01NG), together with the named existing Lean
proofs. Local literature tex files are absent on this machine; no repository files
were fetched or changed.

Resumption check: the earlier attempt already contained the complete proof. Recompiled
it successfully, checked the source signatures and the unit realization record, and
removed the redundant direct proof import of `ProjectiveSpace.Twist`. The delivery
dry run is repeated on this final set; no second-reading section is written here.

## Second reading by M4

1. **Signatures and visibility.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports, proof text, and the theorem proof differ. No target or definition changed.
2. **Proof validity.** Compiled the module with `lcompile.py`; it succeeds without errors or warnings. The item contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The two private helpers are proved directly, and the theorem uses only existing declarations plus the permitted classical constructions.
3. **Statements and nodes.** No statements were split off and no new nodes were added. The existing node's theorem statement, proof steps, dependencies, and proof origin agree with the code's route. The route identifies the coordinate nonvanishing loci, tensor-pulls them twice, proves affine cover and compactness, and transports the sections to tensor exponent one.
4. **Shortest route and pruning.** Checked the source declarations and imports used by the proof. Removed the redundant standard-chart, glued-twist, tensor-pullback, invertible-module, and direct twist imports listed above; retained only imports needed for the proof and interface. The proof uses the source's standard-open affine and cover theorems directly and does not rely on the still-holed chart conjunction or glued comparison.
5. **Unit route and mathematical strength.** The unit record remains unchanged and its realized route is respected: the theorem still constructs the integral Proj twist pullback, coordinate opens, affine cover, compactness, and ampleness. Edge cases such as `n = 0`, the empty scheme, and the zero ring are covered by the same formal argument. No hypothesis was added and no conclusion weakened.

Changed only the proof implementation and proof-only imports, updated the existing node's proof metadata to match that implementation, and added no split-off holes or definitions.
