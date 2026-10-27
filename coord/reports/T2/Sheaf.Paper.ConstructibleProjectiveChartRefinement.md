## What changed

Replaced the hole in `WeilConjectures.constructible_projective_chart_refinement`
without changing its statement. The proof obtains a residue-lisse refinement tree,
uses clause (2) of the existing single-affine hypercover theorem on each nonempty
leaf, derives weak contractibility in that affine scheme's own site, applies the
affine common-chart argument, and proves that the resulting chart composites cover
the leaf. It explicitly identifies the covering arrow to the terminal object and
uses surjectivity of its underlying scheme map.

Added `Sheaf.Paper.AffineCommonProjectiveCharts`, with a complete proof from the
existing residue-lisse projective-model theorem and the new clopen transport lemma.
Its private proved lemmas `residueFiniteTor` and `residueConstructible` supply the
exact inputs of the existing theorem. The first identifies the residue quotient
as a field and applies the existing private proved `bounded_field_tor` lemma in
`Sheaf.Paper.FieldTorAmplitude`, using a proof-only `import all`. The second
converts finite local models to fixed finite locally constant sheaves, uses the
trivial stratification, and bounds support by a finite integer interval. This
avoids identifying the slice-wise tensor predicate with the older all-resolutions
predicate. An initial direct tensor proof exposed a universe ambiguity after import
pruning; the bounded-field lemma provides the shorter route already in the library.

Added two separate source arguments as named public theorems, each with a complete
proof in words and its own node: the finite residue-lisse tree, and common clopen
refinement/ordinary transport of already supplied completed projective charts.
Updated the original node to the actual assembly proof, and added a node for the
proved affine argument. No existing definition, statement, source-library module,
or consumer interface was changed.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.constructible_projective_chart_refinement` (one of one original
holes). The new public theorem `WeilConjectures.affine_common_projective_charts`
and its two private input lemmas have complete Lean proofs.

Added precisely two holes, both in new modules and both exactly `:= by sorry`:

- `WeilConjectures.constructible_residue_tree`, node
  `lem-fix-constructible-residue-tree`.
- `WeilConjectures.clopen_projective_chart_common_refinement`, node
  `lem-fix-clopen-projective-chart-common-refinement`.

This is a decomposition: one original hole closed and two lower holes added,
net minus one hole closed. The affine theorem itself adds no hole. Neither lower
statement is the original result renamed: the first has no affine cover or
projective models, and the second starts with already supplied completed projective
models and has no constructibility, stratifications, weak contractibility, or
residue hypotheses. The proved assembly supplies the cover and its own-site
weak contractibility, uses the residue input on that cover, and proves coverage of
the leaf.

Compilation: the assigned theorem assembly compiled successfully through
`lcompile.py`. The final affine module, including both private helpers and its
public proof, compiled successfully in 6.8 seconds. The two named lower statements
also compiled separately. The first four-module compile of the revised packet returned server-busy exit
124 before compiling its first file; this is retried as instructed. `deliver3.py`
performs its independent compile and preflight checks before pushing.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.Paper.ProEtaleConstantModulePullbackHomology`;
- `Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant`;
- `Sheaf.Paper.ConstructibleFlatCohomologyTorBound`;
- `Sheaf.SixFunctors.ConstructibleOpenClosedRefinement`;
- `Sheaf.Paper.ResidueLisseProjectiveModels`;
- `Sheaf.Paper.ProEtaleCoefficientModulePullbackComposition`;
- `Sheaf.Paper.SfClopenCoefficientComparison`.

These arguments are still needed in the lower nodes, or in the proved affine
module. They are not claimed as globally pruned modules. The slice-wise Tor-bound
conclusion is unnecessary for the affine proof, but that module's proved residue
maximal-ideal identification is used privately. `Sheaf.Paper.FieldTorAmplitude` is a new proof-only
import of the affine module, for its existing bounded-field Tor lemma. No existing
node or module is withdrawn, and no source-library declaration is removed. The unit's realized route is kept.

## Where the brief, the DAG or earlier work was wrong

The plan's finite Tor step uses two different predicates: the Tor-bound theorem
states a localized tensor assertion, whereas the existing projective-model theorem
asks for vanishing over every representative and K-flat resolution. The delivery
obtains the latter from the existing bounded-field Tor lemma rather than assuming
these predicates are definitionally equal.

The existing projective-model theorem concludes with completed pullback; the item
requires ordinary pullback. This distinction is retained in the explicit clopen
transport lemma, including completeness and the ordinary derived compositor.
Similarly, the residue-tree lemma retains ordinary pullback and stability on qcqs
weakly etale objects; no ordinary/completed identification is silently assumed.

Edge cases checked in the statements and proof plans: an empty list of original
partitions still permits choosing the residue partitions; empty leaves have no
chart obligations; the zero residue complex uses a finite interval and zero models;
empty covering members and rank-zero projective terms are allowed. A finite
disjoint open cover is clopen even for non-Hausdorff affine schemes, since each
complement is the finite union of the other opens. The interval argument and the
bounded-field Tor lemma do not assume connectedness or finite Krull dimension.

## New nodes

`lem-fix-constructible-residue-tree`, in
`dag/nodes/sec-six-functors/lem-fix-constructible-residue-tree.json`, records the
finite refinement and the ordinary residue/completeness restriction argument,
including its stability on qcqs objects of each leaf. This is the first retained
hole. Its proof follows original steps 1--3 and the residue part of step 4.

`lem-fix-clopen-projective-chart-common-refinement`, in
`dag/nodes/sec-six-functors/lem-fix-clopen-projective-chart-common-refinement.json`,
records common refinement of two already existing finite projective-chart covers
and their transport to composite ordinary pullbacks. This is the second retained
hole, corresponding to the restriction and common-refinement part of original
step 6.

`lem-fix-affine-common-projective-charts`, in
`dag/nodes/sec-six-functors/lem-fix-affine-common-projective-charts.json`, records
the proved affine argument: derive finite residue constructibility and finite Tor
amplitude, apply the existing projective-model theorem to both restrictions, and
combine the models by the clopen-refinement lemma. It has no new hole.

No change record is required: all existing signatures and definitions are unchanged.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
