## What changed

Completed the proof of `AlgebraicGeometry.properFlat_single_open_noetherian_comparison`
without changing its signature. Added two proof-only imports for strict intermediate
obligations: geometric descent of a relatively flat single sheaf, and termwise comparison
in a given cartesian square with independent derived localizations.

The main proof constructs the descended object as `M[0]`, supplies the standard auxiliary
localizations, proves vanishing outside degree zero using Mathlib's canonical t-structure,
and proves coherence by transporting finite presentation in degree zero and constructing
finite locally free rank-zero presentations in the other degrees. It constructs the
specified ordinary tensor-pullback functor, proves additivity from its adjunction and the
localized-site equivalence, and applies the cartesian comparison for each representative.
All three modules compile locally; the target's original statement is preserved verbatim.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.properFlat_single_open_noetherian_comparison`
(node `lem-pc-proper-flat-single-open-noetherian-comparison`). No sorry remains in that module.

Added two holes, each the entire proof of a public theorem in its own module:

- `AlgebraicGeometry.properFlat_single_noetherian_descent`
  (`lem-pc-proper-flat-single-noetherian-descent`): only geometric descent and a sheaf
  identification, with no derived category or representative comparison.
- `AlgebraicGeometry.cartesian_flat_single_termwise_comparison`
  (`lem-pc-cartesian-flat-single-termwise-comparison`): comparison on supplied cartesian
  data, with no approximation existence, Noetherianity or source-coherence conclusion.

This is a decomposition: one original hole closed and two smaller holes added, net -1.
It is not an axiom-free proof of the complete approximation theorem. The combining proof,
including its cohomology and additivity arguments, is complete Lean.

## No longer needed

No existing public imports were removed: they supply the preserved statement's vocabulary.
All added proof imports are used.

The source-cohomology argument no longer needs `lem-pc-perfect-tensor-bounded-coherent`
(module `Sheaf.AlgebraicGeometry.PerfectTensorBoundedCoherent`) or a descended perfect
factor from `def-pc-perfect-complex` (module `Sheaf.AlgebraicGeometry.PerfectComplex`).
It uses the actual descended single sheaf and the canonical single-functor homology instead.

The root proof also no longer directly needs the tensor-restriction/support route:
`lem-pc-proper-support-affine-tensor-restriction`
(`Sheaf.AlgebraicGeometry.ProperSupportAffineTensorRestriction`),
`lem-weil-pbc-finite-type-module-support-closed`
(`Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed`), and
`lem-weil-pbc-closed-subset-proper-over-base-properties`
(`Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`). The new descent theorem
only descends a sheaf along a proper morphism. Existing approximation and base-change nodes
remain below the new intermediate obligations as recorded in their proof plans; no claim
is made that all these modules disappear from the global targets' import closure.

For completeness, the remaining old direct proof dependencies removed from the root
node are `def-pc-ringed-spaces-derived-direct-image`,
`lem-pc-flat-complex-derived-pullback`, `lem-pc-restrict-derived-direct-image-open`,
`lem-pc-rf-base-change-complex`, `lem-pc-noetherian-approximation-data`, and
`lem-weil-pbc-eventually-proper`. These six are retained as dependencies of the
split-off obligations, rather than used directly by the combining proof. Together
with the five listed above, this accounts for all eleven removed root dependencies.
No previously imported module was actually pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The old plan unnecessarily descended a perfect factor to prove bounded coherent source
cohomology. For a single descended finitely presented module, its object in degree zero
has the needed bounds and coherence directly. The unit's Noetherian-approximation route
is retained; no direct-image coherence or pseudo-coherence is assumed.

The existing base-change interfaces mostly use one shared localization universe, whereas
the item supplies independent universes. The cartesian comparison obligation explicitly
includes the required localization transport; it does not treat these categories as
definitionally equal. The geometric descent obligation retains the cartesian square and
sheaf identification, rather than merely choosing unrelated Noetherian data.

Checked the two new statements on zero sheaves, empty sources, empty U (no x), rank-zero
free terms and complexes unbounded below. The geometric descent uses flatness descent
Tag 05LY; the original mention of Tag 08E7 is not the flatness-descent citation.

## New nodes

`lem-pc-proper-flat-single-noetherian-descent` is the geometric part of the approximation,
with properness and an identified relatively flat finitely presented sheaf; it has no
derived assertions. Its statement is in
`lean/Sheaf/AlgebraicGeometry/ProperFlatSingleNoetherianDescent.lean`.

`lem-pc-cartesian-flat-single-termwise-comparison` computes base change on supplied data
and bounded-above finite-free representatives. It has no existence or coherence claim.
Its statement is in
`lean/Sheaf/AlgebraicGeometry/CartesianFlatSingleTermwiseComparison.lean`.

Both inherit the item's chapter/unit and have source citations and complete proof plans
in their docstrings. Searches were actually run with `msearch.py`: LeanSearch unavailable
(HTTP internal server error), LeanFinder eight unrelated hits, and Mathlib grep no exact
geometric statement. Blueprint searches for Noetherian approximation, 0A1D and 081F found
no matching statement. No definition, existing signature, visibility or other module was
changed; no change record or forced adaptation is needed.

## Second reading by V2

1. I compared the delivered target module with the repository version. The theorem
   signature and all existing declarations are unchanged byte for byte; only proof-only
   imports, a private helper, and theorem proofs were added. The two auxiliary modules
   are new split-off statements and are recorded by matching DAG nodes.
2. I compiled all three modules with `lcompile.py`; each compiled successfully. The only
   remaining `sorry`s are the two named split-off theorems, with no forbidden declaration
   forms or hollow definitions. The target proof itself has no `sorry`. A scratch-copy
   `#print axioms` check of all three public theorems returned only `propext`,
   `Classical.choice`, `Quot.sound` and the expected `sorryAx`.
3. I checked both split-off statements against their docstrings and source citations.
   They are strictly smaller than the target: one is geometric descent only and the other
   is supplied-data termwise comparison. Edge cases listed above remain covered, and no
   duplicate library declaration was found. Independent LeanFinder and Mathlib grep
   searches used "cohomology flat sheaf arbitrary base change bounded above free resolution"
   and "finite.*presentation.*descen|single.*base.*change|zero.*finite.*presentation".
   The hits do not provide either statement. I read the nearby chosen-module stage and
   canonical relatively flat base-change interfaces: their additional diagram data,
   separation assumptions or shared localization instances prevent a direct application.
   I checked [Tag 05LY](https://stacks.math.columbia.edu/tag/05LY),
   [Tag 081F](https://stacks.math.columbia.edu/tag/081F),
   [Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H) and
   [Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D) against the informal arguments.
4. I checked the proof route and imports. The target keeps the unit's approximation and
   comparison route, while replacing the unnecessary perfect-factor detour with the
   single sheaf in degree zero. Added imports are used; no existing public import was
   removed, and the DAG proof dependencies match the declarations used by the proofs.
5. The unit and chapter fields, realized route, theorem signatures, proof origins and
   split-node metadata agree with the Lean files. No statement or definition change
   record is required.

Second-reading changes: added this review and completed the removed direct-dependency
list. No Lean or node repair was necessary. The unit's `realized` arrays are currently
empty in the repository; this delivery preserves them and does not claim to repair that
pre-existing bookkeeping omission. The target docstring still describes the old
perfect-factor route; the executable proof and updated node use M[0] as explained above.
